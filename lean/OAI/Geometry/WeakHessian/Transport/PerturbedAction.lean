import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.CheegerEnergyConst
import OAI.Geometry.WeakHessian.LocalBounds.EnergyIdentification
import OAI.Geometry.WeakHessian.Entropy.LocalizedFisher
import OAI.Geometry.WeakHessian.HeatFlow.HeatDiagonal

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma FormActionBound.symmetric_contraction_error
    {P : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hP : P.toLinearMap.IsSymmetric)
    (hPS : ∀ f : Lp ℝ 2 m, Sobolev m (f : X → ℝ) → Sobolev m (P f : X → ℝ))
    {ρ ρ' : X → ℝ} {c : ℝ} (hc : 0 < c) {R : Lp ℝ 2 m → ℝ}
    (hgrad : ∀ f : Lp ℝ 2 m, Sobolev m (f : X → ℝ) →
      c*(∫ x,ρ x*(weakGradient m (P f) x)^2 ∂m) ≤
        (∫ x,ρ' x*(weakGradient m f x)^2 ∂m)+R f)
    {v : Lp ℝ 2 m} {A : ℝ} (hv : FormActionBound m ρ v A) :
    ∀ f : Lp ℝ 2 m, Sobolev m (f : X → ℝ) →
      2*⟪P v,f⟫_ℝ ≤ A/c+(∫ x,ρ' x*(weakGradient m f x)^2 ∂m)+R f := by
  intro f hf
  have hcs : Sobolev m (c•P f : Lp ℝ 2 m) := by
    apply (sobolev_congr_ae ?_).mpr ((hPS f hf).const_mul c)
    filter_upwards [Lp.coeFn_smul c (P f)] with x hx
    simpa only [Pi.smul_apply,smul_eq_mul] using hx
  have H := hv (c•P f) hcs
  have hsym : ⟪P v,f⟫_ℝ = ⟪v,P f⟫_ℝ := hP v f
  rw [weighted_gradient_smul,inner_smul_right,← hsym] at H
  have Hg := mul_le_mul_of_nonneg_left (hgrad f hf) hc.le
  have H' : 2*⟪P v,f⟫_ℝ-(∫ x,ρ' x*(weakGradient m f x)^2 ∂m)-R f ≤ A/c := by
    apply (le_div_iff₀ hc).mpr
    nlinarith
  linarith

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integral_gradient_le_regularized {ρ : X → ℝ}
    (hρ : AEStronglyMeasurable ρ m) {B : ℝ} (hb : ∀ᵐ x ∂m,|ρ x| ≤ B)
    {ε : ℝ} (hε : 0 ≤ ε) {f : Lp ℝ 2 m} (hf : Sobolev m (f : X → ℝ)) :
    (∫ x,ρ x*(weakGradient m f x)^2 ∂m) ≤
      ∫ x,(ρ x+ε)*(weakGradient m f x)^2 ∂m := by
  have hi := hf.2.2.integrable_sq.bdd_mul hρ (by simpa only [Real.norm_eq_abs] using hb)
  simp_rw [add_mul]
  rw [integral_add hi (hf.2.2.integrable_sq.const_mul ε),integral_const_mul]
  exact le_add_of_nonneg_right (mul_nonneg hε (integral_nonneg fun _ => sq_nonneg _))

omit [SigmaFinite m] in
lemma cheegerHeat_diagonal_entropy_test_error
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (h : QuadraticCheegerEnergy m)
    {θ : ℝ → ℝ} {u : ℝ → Lp ℝ 2 m} {s τ : ℝ} {v : Lp ℝ 2 m}
    (hθ : HasDerivAt θ τ s) (hu : HasDerivAt u v s) (hpos : 0 < θ s)
    {B : ℝ} (hB : 0 ≤ B) (hub : ∀ᵐ x ∂m,|u s x| ≤ B)
    (hun : ∀ᵐ x ∂m,0 ≤ u s x) {c : ℝ} (hc : 0 < c)
    {R : Lp ℝ 2 m → ℝ}
    (hgrad : ∀ f : Lp ℝ 2 m,Sobolev m (f : X → ℝ) →
      c*(∫ x,u s x*(weakGradient m (cheegerHeat h (θ s) f) x)^2 ∂m) ≤
        (∫ x,cheegerHeat h (θ s) (u s) x*(weakGradient m f x)^2 ∂m)+R f)
    (hsplit : ∀ f g : Lp ℝ 2 m,Sobolev m (f : X → ℝ) → Sobolev m (g : X → ℝ) →
      ∀ t : ℝ,R (f+t•g) ≤ 2*R f+2*t^2*R g)
    (hrelative : ∀ g : Lp ℝ 2 m,Sobolev m (g : X → ℝ) →
      2*R g ≤ ∫ x,cheegerHeat h (θ s) (u s) x*(weakGradient m g x)^2 ∂m)
    {A : ℝ} (hA : FormActionBound m (u s) v A) {ε : ℝ} (hε : 0 < ε)
    {f : Lp ℝ 2 m} (hf : Sobolev m (f : X → ℝ)) {E : ℝ} (hRf : R f ≤ E) :
    ∃ w : Lp ℝ 2 m, ∃ e : ℝ,
      HasDerivAt (fun z => cheegerHeat h (θ z) (u z)) w s ∧
      HasDerivAt (fun z => ∫ x,regularizedEntropy ε (cheegerHeat h (θ z) (u z) x) ∂m) e s ∧
      2*⟪w,f⟫_ℝ ≤ A/c+2*E-2*τ*e+
        ∫ x,(cheegerHeat h (θ s) (u s) x+ε)*(weakGradient m f x)^2 ∂m := by
  obtain ⟨L,hL,hD,hE⟩ := cheegerHeat_diagonal_entropy_hasDerivAt hfin h hθ hu hpos hε
  refine ⟨_,_,hD,hE,?_⟩
  have hPS (g : Lp ℝ 2 m) (hg : Sobolev m (g : X → ℝ)) :
      Sobolev m (cheegerHeat h (θ s) g) := (identified_sobolev_iff_energy hfin hID).mpr
    ((cheegerHeat_energy_le h hpos.le g).trans_lt ((identified_sobolev_iff_energy hfin hID).mp hg))
  have hP := hA.symmetric_contraction_error (cheegerHeat_symmetric h (θ s)) hPS hc hgrad
  have hPB := cheegerHeat_bounded h hpos.le hB (u s) hub
  have hPε : ∀ g : Lp ℝ 2 m,Sobolev m (g : X → ℝ) →
      2*⟪cheegerHeat h (θ s) v,g⟫_ℝ ≤ A/c+
        (∫ x,(cheegerHeat h (θ s) (u s) x+ε)*(weakGradient m g x)^2 ∂m)+R g := by
    intro g hg
    have H := integral_gradient_le_regularized (Lp.aestronglyMeasurable _) hPB hε.le hg
    linarith [hP g hg]
  have hLap := identified_isLaplacian_of_formGenerator hfin hID h _ _ hL
  let r := (regularizedLog_memLp hε (cheegerHeat h (θ s) (u s))).toLp
    (fun x => regularizedLog ε (cheegerHeat h (θ s) (u s) x))
  have hr : Sobolev m (r : X → ℝ) := (sobolev_congr_ae
    (regularizedLog_memLp hε (cheegerHeat h (θ s) (u s))).coeFn_toLp).mpr
    (hLap.1.comp_contDiff_lipschitz hfin (regularizedLog_contDiff hε)
      (regularizedLog_lipschitz hε) (regularizedLog_zero ε))
  exact logarithmic_shift_split_absorb hfin hpar hLap
    (cheegerHeat_nonneg h hpos.le (u s) hun) hPB hε hPε τ hf hRf
    (hsplit f r hf hr τ)
    ((hrelative r hr).trans
      (integral_gradient_le_regularized (Lp.aestronglyMeasurable _) hPB hε.le hr))

end WeakHessian

end
end

end OAI
