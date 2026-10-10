import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.LocalSobolevLipschitz
import OAI.Geometry.WeakHessian.LocalBounds.GammaAddConstLeft

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma LocalSobolev.comp_contDiff (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} (hf : LocalSobolev m f) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hfφ : LocallyL2 m (φ ∘ f)) {B : ℝ} (hB : ∀ᵐ x ∂m, |deriv φ (f x)| ≤ B) :
    LocalSobolev m (φ ∘ f) := by
  apply (localSobolev_iff_exists_upperGradient hfinite).mpr
  exact ⟨hfφ,_,(weakGradient_isMinimal hf.2).1.comp_contDiff hf.1.aemeasurable hφ hB⟩

lemma weakGradient_comp_contDiff_le (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} (hf : LocalSobolev m f) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hfφ : LocallyL2 m (φ ∘ f)) {B : ℝ} (hB : ∀ᵐ x ∂m, |deriv φ (f x)| ≤ B) :
    ∀ᵐ x ∂m, weakGradient m (φ ∘ f) x ≤ |deriv φ (f x)| *weakGradient m f x :=
  (weakGradient_isMinimal (hf.comp_contDiff hfinite hφ hfφ hB).2).2 _
    ((weakGradient_isMinimal hf.2).1.comp_contDiff hf.1.aemeasurable hφ hB)

lemma gamma_chain_residual (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hfφ : LocallyL2 m (φ ∘ f))
    {B : ℝ} (hB : ∀ᵐ x ∂m, |deriv φ (f x)| ≤ B) (c : ℝ) :
    ∀ᵐ x ∂m, |gamma m (φ ∘ f) g x-c*gamma m f g x| ≤
      |deriv φ (f x)-c| *weakGradient m f x*weakGradient m g x := by
  let ψ : ℝ → ℝ := fun s => φ s-c*s
  have hψ : ContDiff ℝ 1 ψ := hφ.sub (contDiff_const.mul contDiff_id)
  have hdψ (s : ℝ) : deriv ψ s = deriv φ s-c := by
    simpa only [Pi.sub_def,id_eq,ψ,one_mul,mul_one] using
      ((hφ.differentiable (by simp) s).hasDerivAt.sub ((hasDerivAt_id s).const_mul c)).deriv
  have hbψ : ∀ᵐ x ∂m, |deriv ψ (f x)| ≤ B+|c| := by
    filter_upwards [hB] with x hx
    rw [hdψ]
    exact (abs_sub _ _).trans (add_le_add hx le_rfl)
  have hφs := hf.comp_contDiff hfinite hφ hfφ hB
  have hψL : LocallyL2 m (ψ ∘ f) := fun o R hR => (hfφ o R hR).sub ((hf.1 o R hR).const_mul c)
  have hψs := hf.comp_contDiff hfinite hψ hψL hbψ
  filter_upwards [abs_gamma_le hfinite hpar hψs hg,
    weakGradient_comp_contDiff_le hfinite hf hψ hψL hbψ,
    gamma_sub_left hfinite hpar hφs (hf.const_mul c) hg,
    gamma_const_mul_left hfinite hpar hf hg c,
    weakGradient_nonneg (m := m) g] with x hc hd hs hm hng
  change |gamma m (fun y => φ (f y)-c*f y) g x| ≤ _ at hc
  dsimp only [Function.comp_apply] at hs
  rw [hs,hm] at hc
  rw [hdψ] at hd
  exact hc.trans (mul_le_mul_of_nonneg_right hd hng)

lemma gamma_comp_contDiff (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hfφ : LocallyL2 m (φ ∘ f))
    {B : ℝ} (hB : ∀ᵐ x ∂m, |deriv φ (f x)| ≤ B) :
    gamma m (φ ∘ f) g =ᵐ[m] (fun x => deriv φ (f x)*gamma m f g x) := by
  filter_upwards [ae_all_iff.mpr (fun q : ℚ =>
    gamma_chain_residual hfinite hpar hf hg hφ hfφ hB q)] with x hx
  obtain ⟨qs,_,_,ht⟩ := Real.exists_seq_rat_strictMono_tendsto (deriv φ (f x))
  have hl := ((tendsto_const_nhds (x := gamma m (φ ∘ f) g x)).sub
    (ht.mul_const (gamma m f g x))).abs
  have hr := (((tendsto_const_nhds (x := deriv φ (f x))).sub ht).abs.mul_const
    (weakGradient m f x)).mul_const (weakGradient m g x)
  have hr0 : Tendsto (fun n => |deriv φ (f x)-(qs n:ℝ)| *weakGradient m f x*weakGradient m g x)
      atTop (𝓝 (0:ℝ)) := by simpa only [sub_self,abs_zero,zero_mul] using hr
  have he : |gamma m (φ ∘ f) g x - deriv φ (f x)*gamma m f g x| ≤ 0 :=
    le_of_tendsto_of_tendsto hl hr0 (Eventually.of_forall fun n => hx (qs n))
  exact sub_eq_zero.mp (abs_nonpos_iff.mp he)


lemma LocalSobolev.exp_bounded (hfinite : FiniteOnBoundedSets m) {V : X → ℝ}
    (hV : LocalSobolev m V) {B : ℝ} (hB : ∀ᵐ x ∂m, V x ≤ B) :
    LocalSobolev m (fun x => Real.exp (V x)) := by
  apply hV.comp_contDiff hfinite Real.contDiff_exp
  · apply locallyL2_of_bounded hfinite (Real.continuous_exp.comp_aestronglyMeasurable hV.1.aestronglyMeasurable)
    filter_upwards [hB] with x hx
    simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr hx
  · filter_upwards [hB] with x hx
    simpa only [Real.deriv_exp,abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr hx

lemma gamma_exp_left (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {V f : X → ℝ} (hV : LocalSobolev m V) (hf : LocalSobolev m f)
    {B : ℝ} (hB : ∀ᵐ x ∂m, V x ≤ B) :
    gamma m (fun x => Real.exp (V x)) f =ᵐ[m]
      (fun x => Real.exp (V x)*gamma m V f x) := by
  have hb : ∀ᵐ x ∂m, |deriv Real.exp (V x)| ≤ Real.exp B := by
    filter_upwards [hB] with x hx
    simpa only [Real.deriv_exp,abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr hx
  simpa only [Function.comp_def,Real.deriv_exp] using
    gamma_comp_contDiff hfinite hpar hV hf Real.contDiff_exp (hV.exp_bounded hfinite hB).1 hb

lemma weakGradient_exp_bound (hfinite : FiniteOnBoundedSets m) {V : X → ℝ}
    (hV : LocalSobolev m V) {B L : ℝ} (hB : ∀ᵐ x ∂m, V x ≤ B)
    (hL : ∀ᵐ x ∂m, weakGradient m V x ≤ L) :
    ∀ᵐ x ∂m, |weakGradient m (fun y => Real.exp (V y)) x| ≤ Real.exp B*L := by
  have hd := (weakGradient_isMinimal hV.2).1.exp hV.1.aemeasurable hB
  filter_upwards [(weakGradient_isMinimal (hV.exp_bounded hfinite hB).2).2 _ hd,
    hB,hL,weakGradient_nonneg (m := m) V,
    weakGradient_nonneg (m := m) (fun y => Real.exp (V y))] with x h hx hl hn he
  rw [abs_of_nonneg he]
  exact h.trans (mul_le_mul (Real.exp_le_exp.mpr hx) hl hn (Real.exp_pos B).le)

lemma gamma_mul_exp_left (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f V g : X → ℝ} (hf : LocalSobolev m f) (hV : LocalSobolev m V) (hg : LocalSobolev m g)
    {B L : ℝ} (hB : ∀ᵐ x ∂m, V x ≤ B) (hL : ∀ᵐ x ∂m, weakGradient m V x ≤ L) :
    gamma m (fun y => f y*Real.exp (V y)) g =ᵐ[m]
      (fun x => Real.exp (V x)*(gamma m f g x+f x*gamma m V g x)) := by
  have hb : ∀ᵐ x ∂m, |Real.exp (V x)| ≤ Real.exp B := by
    filter_upwards [hB] with x hx
    simpa only [abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr hx
  filter_upwards [gamma_mul_left hfinite hpar hf (hV.exp_bounded hfinite hB) hg hb
    (weakGradient_exp_bound hfinite hV hB hL),gamma_exp_left hfinite hpar hV hg hB] with x hm he
  rw [hm,he]
  ring

lemma memLp_gamma_of_lipschitz (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {V f : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) (hf : Sobolev m f) :
    MemLp (gamma m V f) 2 m := by
  have hv := localSobolev_of_lipschitz hfinite hV
  apply (hf.2.2.const_mul (L:ℝ)).mono' (gamma_aestronglyMeasurable hfinite hv hf.2.1)
  filter_upwards [abs_gamma_le hfinite hpar hv hf.2.1,weakGradient_le_lipschitz hfinite hV,
    weakGradient_nonneg (m := m) f] with x h hL hn
  simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg L.coe_nonneg,abs_of_nonneg hn] using
    h.trans (mul_le_mul_of_nonneg_right hL hn)
end WeakHessian

end

end OAI
