import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.EnergyGammaPairing
import OAI.Geometry.WeakHessian.Calculus.VariableDissipationLimits

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

omit [SigmaFinite m] in
lemma energy_tendsto_heat_gamma_bounded_pairing
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    (h : QuadraticCheegerEnergy m) {fs : ℕ → Lp ℝ 2 m} {f : Lp ℝ 2 m}
    (hfs : ∀ n, Sobolev m (fs n : X → ℝ)) (hf : Sobolev m (f : X → ℝ))
    (hE : Tendsto (fun n => (cheegerEnergy m ((fs n-f : Lp ℝ 2 m) : X → ℝ)).toReal)
      atTop (𝓝 0)) {q : X → ℝ} (hqm : AEStronglyMeasurable q m)
    {B : ℝ} (hqb : ∀ᵐ x ∂m, |q x| ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => ∫ x, q x*gamma m (cheegerHeat h t (fs n)) (cheegerHeat h t (fs n)) x ∂m)
      atTop (𝓝 (∫ x, q x*gamma m (cheegerHeat h t f) (cheegerHeat h t f) x ∂m)) := by
  let Q := cheeger_closedQuadraticEnergy h
  have hfd := (identified_sobolev_iff_energy hfin hID).mp hf
  have hfsd (n : ℕ) := (identified_sobolev_iff_energy hfin hID).mp (hfs n)
  have hft : Sobolev m (cheegerHeat h t f) :=
    (identified_sobolev_iff_energy hfin hID).mpr ((cheegerHeat_energy_le h ht f).trans_lt hfd)
  have hfst (n : ℕ) : Sobolev m (cheegerHeat h t (fs n)) :=
    (identified_sobolev_iff_energy hfin hID).mpr ((cheegerHeat_energy_le h ht (fs n)).trans_lt (hfsd n))
  have hEt : Tendsto (fun n => (cheegerEnergy m
      ((cheegerHeat h t (fs n)-cheegerHeat h t f : Lp ℝ 2 m) : X → ℝ)).toReal) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => ENNReal.toReal_nonneg) (fun n => ?_) hE
    rw [← map_sub]
    exact ENNReal.toReal_mono (Q.sub_lt_top (hfsd n) hfd).ne (cheegerHeat_energy_le h ht (fs n-f))
  apply energy_tendsto_gamma_bounded_pairing hfin hID hfst hft _ hqm hqb
  simpa only [cheegerEnergy_congr_ae (Lp.coeFn_sub _ _),Pi.sub_def] using hEt

omit [SigmaFinite m] in
lemma energy_tendsto_variable_heat_integral
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    (h : QuadraticCheegerEnergy m) {fs : ℕ → Lp ℝ 2 m} {f ξ : Lp ℝ 2 m}
    (hfs : ∀ n, Sobolev m (fs n : X → ℝ)) (hf : Sobolev m (f : X → ℝ))
    (hE : Tendsto (fun n => (cheegerEnergy m ((fs n-f : Lp ℝ 2 m) : X → ℝ)).toReal)
      atTop (𝓝 0)) {M : ℝ} (hM : ∀ n, (cheegerEnergy m (fs n : X → ℝ)).toReal ≤ M)
    {Cξ : ℝ} (hCξ : 0 ≤ Cξ) (hξb : ∀ᵐ x ∂m, |ξ x| ≤ Cξ)
    {k : X → ℝ} (hkm : AEStronglyMeasurable k m)
    {B : ℝ} (hB : 0 ≤ B) (hkb : ∀ᵐ x ∂m, |k x| ≤ B)
    {T : ℝ} (hT : 0 ≤ T)
    (hi : ∀ n, IntervalIntegrable
      (fun s => ∫ x, (cheegerHeat h s ξ x*k x)*
        gamma m (cheegerHeat h (T-s) (fs n)) (cheegerHeat h (T-s) (fs n)) x ∂m) volume 0 T) :
    IntervalIntegrable
      (fun s => ∫ x, (cheegerHeat h s ξ x*k x)*
        gamma m (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x ∂m) volume 0 T ∧
    Tendsto (fun n => ∫ s in 0..T, ∫ x, (cheegerHeat h s ξ x*k x)*
      gamma m (cheegerHeat h (T-s) (fs n)) (cheegerHeat h (T-s) (fs n)) x ∂m)
      atTop (𝓝 (∫ s in 0..T, ∫ x, (cheegerHeat h s ξ x*k x)*
        gamma m (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x ∂m)) := by
  let Z := fun (u : Lp ℝ 2 m) s => ∫ x, (cheegerHeat h s ξ x*k x)*
    gamma m (cheegerHeat h (T-s) u) (cheegerHeat h (T-s) u) x ∂m
  have hlim (s : ℝ) (hs : s ∈ Icc 0 T) : Tendsto (fun n => Z (fs n) s) atTop (𝓝 (Z f s)) := by
    apply energy_tendsto_heat_gamma_bounded_pairing hfin hID h hfs hf hE
      ((Lp.memLp _).aestronglyMeasurable.mul hkm) (B := Cξ*B) _ (sub_nonneg.mpr hs.2)
    filter_upwards [cheegerHeat_bounded h hs.1 hCξ ξ hξb,hkb] with x hξ hk
    rw [Pi.mul_apply,abs_mul]
    exact mul_le_mul hξ hk (abs_nonneg _) hCξ
  have hmeas (n : ℕ) : AEStronglyMeasurable (Z (fs n)) (volume.restrict (uIoc 0 T)) :=
    (intervalIntegrable_iff.mp (hi n)).1
  have hbound (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 T) : ‖Z (fs n) s‖ ≤ (Cξ*B)*(2*M) := by
    rw [Real.norm_eq_abs]
    exact (abs_weighted_heat_gamma_le hfin hID h (hfs n) hCξ hξb hkm hB hkb
      hs.1 (sub_nonneg.mpr hs.2)).trans
      (mul_le_mul_of_nonneg_left (by linarith only [hM n]) (mul_nonneg hCξ hB))
  constructor
  · apply intervalIntegrable_iff.mpr
    have hzm : AEStronglyMeasurable (Z f) (volume.restrict (uIoc 0 T)) :=
      aestronglyMeasurable_of_tendsto_ae atTop hmeas ((ae_restrict_iff' measurableSet_uIoc).mpr
        (ae_of_all _ fun s hs => hlim s (by rw [uIoc_of_le hT] at hs; exact ⟨hs.1.le,hs.2⟩)))
    have hc : IntervalIntegrable (fun _ : ℝ => (Cξ*B)*(2*(cheegerEnergy m (f : X → ℝ)).toReal)) volume 0 T := intervalIntegrable_const
    apply (intervalIntegrable_iff.mp hc).mono' hzm
    apply (ae_restrict_iff' measurableSet_uIoc).mpr
    exact ae_of_all _ fun s hs => by
      rw [uIoc_of_le hT] at hs
      simpa only [Z,Real.norm_eq_abs] using abs_weighted_heat_gamma_le hfin hID h hf hCξ hξb hkm hB hkb
        hs.1.le (sub_nonneg.mpr hs.2)
  · apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (Cξ*B)*(2*M))
    · exact Eventually.of_forall hmeas
    · exact Eventually.of_forall fun n => ae_of_all _ fun s hs => hbound n s (by
        rw [uIoc_of_le hT] at hs; exact ⟨hs.1.le,hs.2⟩)
    · exact intervalIntegrable_const
    · exact ae_of_all _ fun s hs => hlim s (by rw [uIoc_of_le hT] at hs; exact ⟨hs.1.le,hs.2⟩)
end WeakHessian

end
end

end OAI
