import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.CompContDiffLipschitz

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

def FormActionBound (m : Measure X) (ρ : X → ℝ) (v : Lp ℝ 2 m) (A : ℝ) : Prop :=
  ∀ f : Lp ℝ 2 m, Sobolev m (f : X → ℝ) →
    2 * ⟪v,f⟫_ℝ ≤ A + ∫ x, ρ x * (weakGradient m f x)^2 ∂m

variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X]

lemma regularizedLog_weighted_gamma (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u f : X → ℝ}
    (hu : Sobolev m u) (hf : Sobolev m f)
    (hun : ∀ᵐ x ∂m, 0 ≤ u x) {ε : ℝ} (hε : 0 < ε) :
    (fun x => (u x+ε)*gamma m f (regularizedLog ε ∘ u) x) =ᵐ[m] gamma m f u := by
  have hr := hu.comp_contDiff_lipschitz hfin (regularizedLog_contDiff hε)
    (regularizedLog_lipschitz hε) (regularizedLog_zero ε)
  filter_upwards [gamma_comp_contDiff hfin hpar hu.2.1 hf.2.1
    (regularizedLog_contDiff hε) hr.2.1.1
    (ae_of_all _ fun x => regularizedLog_deriv_bound hε (u x)),
    gamma_comm (m := m) f (regularizedLog ε ∘ u),gamma_comm (m := m) u f,hun]
    with x hc h1 h2 hn
  rw [h1,hc,regularizedLog_deriv hε,max_eq_right (by linarith : ε ≤ u x+ε),h2]
  have hnz : u x+ε ≠ 0 := ne_of_gt (by linarith)
  field_simp

lemma weighted_gradient_add_smul (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {f g : Lp ℝ 2 m}
    (hf : Sobolev m (f : X → ℝ)) (hg : Sobolev m (g : X → ℝ))
    {ρ : X → ℝ} (hρm : AEStronglyMeasurable ρ m) {B : ℝ}
    (hρb : ∀ᵐ x ∂m, |ρ x| ≤ B) (c : ℝ) :
    (∫ x, ρ x*(weakGradient m (f+c•g : Lp ℝ 2 m) x)^2 ∂m) =
      (∫ x, ρ x*(weakGradient m f x)^2 ∂m) +
      2*c*(∫ x, ρ x*gamma m f g x ∂m) +
      c^2*(∫ x, ρ x*(weakGradient m g x)^2 ∂m) := by
  have hfe : Integrable (fun x => ρ x*(weakGradient m f x)^2) m :=
    hf.2.2.integrable_sq.bdd_mul hρm (by simpa only [Real.norm_eq_abs] using hρb)
  have hge : Integrable (fun x => ρ x*(weakGradient m g x)^2) m :=
    hg.2.2.integrable_sq.bdd_mul hρm (by simpa only [Real.norm_eq_abs] using hρb)
  have hfge : Integrable (fun x => ρ x*gamma m f g x) m :=
    (integrable_gamma hfin hf hg).bdd_mul hρm (by simpa only [Real.norm_eq_abs] using hρb)
  have hre : (f+c•g : Lp ℝ 2 m) =ᵐ[m] (fun x => f x+c*g x) := by
    filter_upwards [Lp.coeFn_add f (c•g),Lp.coeFn_smul c g] with x ha hc
    simp only [ha,hc,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  calc
    _ = ∫ x, ρ x*(weakGradient m f x)^2+
        2*c*(ρ x*gamma m f g x)+c^2*(ρ x*(weakGradient m g x)^2) ∂m := by
      apply integral_congr_ae
      filter_upwards [weakGradient_congr_ae hre,
        weakGradient_linear_combination_sq hfin hpar hf.2.1 hg.2.1 c] with x hre hx
      rw [hre,hx]; ring
    _ = _ := by
      have h1 := integral_add (hfe.add (hfge.const_mul (2*c))) (hge.const_mul (c^2))
      have h2 := integral_add hfe (hfge.const_mul (2*c))
      simp only [Pi.add_apply] at h1 h2
      rw [h1,h2,integral_const_mul,integral_const_mul]

lemma FormActionBound.logarithmic_shift_exact
    (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {u L v : Lp ℝ 2 m} (hu : IsLaplacian m u L)
    (hun : ∀ᵐ x ∂m, 0 ≤ u x) {B : ℝ} (hub : ∀ᵐ x ∂m, |u x| ≤ B)
    {ε A : ℝ} (hε : 0 < ε) (hv : FormActionBound m (fun x => u x+ε) v A)
    (t : ℝ) :
    let r := (regularizedLog_memLp hε u).toLp (fun x => regularizedLog ε (u x))
    FormActionBound m (fun x => u x+ε) (v+t•L)
      (A-2*t*⟪v+t•L,r⟫_ℝ+t^2*⟪L,r⟫_ℝ) := by
  dsimp only
  let r := (regularizedLog_memLp hε u).toLp (fun x => regularizedLog ε (u x))
  have hre : (r : X → ℝ) =ᵐ[m] regularizedLog ε ∘ (u : X → ℝ) :=
    (regularizedLog_memLp hε u).coeFn_toLp
  have hr : Sobolev m (r : X → ℝ) := (sobolev_congr_ae hre).mpr
    (hu.1.comp_contDiff_lipschitz hfin (regularizedLog_contDiff hε)
    (regularizedLog_lipschitz hε) (regularizedLog_zero ε))
  have hρm : AEStronglyMeasurable (fun x => u x+ε) m :=
    (Lp.memLp u).aestronglyMeasurable.add_const ε
  have hρb : ∀ᵐ x ∂m, |u x+ε| ≤ B+ε := by
    filter_upwards [hub] with x hx
    exact (abs_add_le _ _).trans (by rw [abs_of_pos hε]; linarith)
  have hcross (f : Lp ℝ 2 m) (hf : Sobolev m (f : X → ℝ)) :
      (∫ x, (u x+ε)*gamma m f r x ∂m) = -⟪L,f⟫_ℝ := by
    rw [L2.inner_def]
    calc
      _ = ∫ x, gamma m f u x ∂m := by
        apply integral_congr_ae
        filter_upwards [gamma_congr_ae (Filter.EventuallyEq.rfl : (f : X → ℝ) =ᵐ[m] f) hre,
          regularizedLog_weighted_gamma hfin hpar hu.1 hf hun hε] with x h1 h2
        rw [h1]; exact h2
      _ = ∫ x, gamma m u f x ∂m := integral_congr_ae (gamma_comm _ _)
      _ = _ := by
        rw [hu.2.2 f hf]
        congr 1
        apply integral_congr_ae
        exact ae_of_all _ fun x => by simp only [RCLike.inner_apply,conj_trivial]; ring
  have hrq : (∫ x, (u x+ε)*(weakGradient m r x)^2 ∂m) = -⟪L,r⟫_ℝ := by
    rw [← hcross r hr]
    apply integral_congr_ae
    filter_upwards [gamma_self (m := m) (r : X → ℝ)] with x hx
    rw [hx]
  change FormActionBound m (fun x => u x+ε) (v+t•L)
    (A-2*t*⟪v+t•L,r⟫_ℝ+t^2*⟪L,r⟫_ℝ)
  intro f hf
  have hfr : Sobolev m (f+t•r : Lp ℝ 2 m) := by
    apply (sobolev_congr_ae ?_).mpr (hf.add hfin (hr.const_mul t))
    filter_upwards [Lp.coeFn_add f (t•r),Lp.coeFn_smul t r] with x ha hs
    simp only [ha,hs,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have H := hv (f+t•r) hfr
  rw [weighted_gradient_add_smul hfin hpar hf hr hρm hρb t,hcross f hf,hrq] at H
  simp only [inner_add_right,inner_smul_right,inner_add_left,real_inner_smul_left] at H ⊢
  nlinarith

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma FormActionBound.mono {ρ : X → ℝ} {v : Lp ℝ 2 m} {A B : ℝ}
    (h : FormActionBound m ρ v A) (hAB : A ≤ B) : FormActionBound m ρ v B :=
  fun f hf => by linarith [h f hf]

lemma FormActionBound.logarithmic_shift
    (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {u L v : Lp ℝ 2 m} (hu : IsLaplacian m u L)
    (hun : ∀ᵐ x ∂m, 0 ≤ u x) {B : ℝ} (hub : ∀ᵐ x ∂m, |u x| ≤ B)
    {ε A : ℝ} (hε : 0 < ε) (hv : FormActionBound m (fun x => u x+ε) v A)
    (t : ℝ) :
    let r := (regularizedLog_memLp hε u).toLp (fun x => regularizedLog ε (u x))
    FormActionBound m (fun x => u x+ε) (v+t•L) (A-2*t*⟪v+t•L,r⟫_ℝ) := by
  apply (hv.logarithmic_shift_exact hfin hpar hu hun hub hε t).mono
  have hi : ⟪L,(regularizedLog_memLp hε u).toLp
      (fun x => regularizedLog ε (u x))⟫_ℝ ≤ 0 := by
    rw [L2.inner_def]
    have he : (∫ x, inner ℝ (L x) ((regularizedLog_memLp hε u).toLp
        (fun x => regularizedLog ε (u x)) x) ∂m) =
        ∫ x, L x * regularizedLog ε (u x) ∂m := by
      apply integral_congr_ae
      filter_upwards [(regularizedLog_memLp hε u).coeFn_toLp] with x hx
      simp only [hx,RCLike.inner_apply,conj_trivial]; ring
    rw [he,hu.regularizedLog_identity hfin hpar hun hε]
    apply neg_nonpos.mpr
    exact integral_nonneg_of_ae (hun.mono fun x hx =>
      div_nonneg (sq_nonneg _) (by linarith))
  exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) hi)

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma weighted_gradient_smul (ρ : X → ℝ) (f : Lp ℝ 2 m) (c : ℝ) :
    (∫ x, ρ x*(weakGradient m (c•f : Lp ℝ 2 m) x)^2 ∂m) =
      c^2*(∫ x, ρ x*(weakGradient m f x)^2 ∂m) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  have hc : (c•f : Lp ℝ 2 m) =ᵐ[m] (fun x => c*f x) := by
    filter_upwards [Lp.coeFn_smul c f] with x hx
    simpa only [Pi.smul_apply,smul_eq_mul] using hx
  filter_upwards [weakGradient_congr_ae hc,weakGradient_const_mul (m := m) c (f : X → ℝ)]
    with x h1 h2
  rw [h1,h2,mul_pow,sq_abs]
  ring

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma FormActionBound.symmetric_contraction
    {P : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hP : P.toLinearMap.IsSymmetric)
    (hPS : ∀ f : Lp ℝ 2 m, Sobolev m (f : X → ℝ) → Sobolev m (P f : X → ℝ))
    {ρ ρ' : X → ℝ} {c : ℝ} (hc : 0 < c)
    (hgrad : ∀ f : Lp ℝ 2 m, Sobolev m (f : X → ℝ) →
      c*(∫ x, ρ x*(weakGradient m (P f) x)^2 ∂m) ≤
        ∫ x, ρ' x*(weakGradient m f x)^2 ∂m)
    {v : Lp ℝ 2 m} {A : ℝ} (hv : FormActionBound m ρ v A) :
    FormActionBound m ρ' (P v) (A/c) := by
  intro f hf
  have hcs : Sobolev m (c•P f : Lp ℝ 2 m) := by
    apply (sobolev_congr_ae ?_).mpr ((hPS f hf).const_mul c)
    filter_upwards [Lp.coeFn_smul c (P f)] with x hx
    simpa only [Pi.smul_apply,smul_eq_mul] using hx
  have H := hv (c•P f) hcs
  have hsym : ⟪P v,f⟫_ℝ = ⟪v,P f⟫_ℝ := hP v f
  rw [weighted_gradient_smul,inner_smul_right,← hsym] at H
  have Hg := mul_le_mul_of_nonneg_left (hgrad f hf) hc.le
  have H' : 2*⟪P v,f⟫_ℝ - (∫ x, ρ' x*(weakGradient m f x)^2 ∂m) ≤ A/c := by
    apply (le_div_iff₀ hc).mpr
    nlinarith
  linarith

end WeakHessian

end
end

end OAI
