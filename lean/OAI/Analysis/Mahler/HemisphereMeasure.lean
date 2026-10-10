import OAI.Analysis.Mahler.HemisphereJacobian
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace MahlerStokes

/-- Nonnegative Fubini in the distinguished coordinate; no integrability
assumption is needed for the singular hemisphere area density. -/
theorem setLIntegral_slice {n : ℕ} (i : Fin (n+1)) {s : Set (Fin (n+1) → ℝ)}
    (hs : MeasurableSet s) (f : (Fin (n+1) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x in s, f x) = ∫⁻ y : Fin n → ℝ,
      ∫⁻ t in {t | i.insertNth t y ∈ s}, f (i.insertNth t y) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).symm
  calc
    (∫⁻ x in s, f x) = ∫⁻ p : ℝ × (Fin n → ℝ), s.indicator f (i.insertNth p.1 p.2) := by
      rw [← lintegral_indicator hs]
      exact (hp.lintegral_comp_emb e.symm.measurableEmbedding (s.indicator f)).symm
    _ = ∫⁻ y : Fin n → ℝ, ∫⁻ t : ℝ, s.indicator f (i.insertNth t y) := by
      exact (lintegral_prod _ ((hf.indicator hs).comp e.symm.measurable).aemeasurable).trans
        (lintegral_lintegral_swap ((hf.indicator hs).comp e.symm.measurable).aemeasurable)
    _ = _ := by
      apply lintegral_congr
      intro y
      change _ = ∫⁻ t in (fun t : ℝ => i.insertNth t y) ⁻¹' s, f (i.insertNth t y)
      rw [← lintegral_indicator (hs.preimage (by fun_prop : Measurable (fun t : ℝ => i.insertNth t y)))]
      rfl

lemma measurableSet_hemisphereConeDomain {n : ℕ} (i : Fin (n+1)) :
    MeasurableSet (hemisphereConeDomain i) :=
  ((measurable_pi_apply i) measurableSet_Ioo).inter
    ((removeCoordinate i).measurable (measurableSet_coordBall n 1))

/-- The nonnegative change of variables for radial hemisphere coordinates,
with its computed Jacobian rather than an assumed surface integration law. -/
theorem lintegral_hemisphereCone {n : ℕ} (i : Fin (n+1))
    (g : (Fin (n+1) → ℝ) → ℝ≥0∞) :
    (∫⁻ z in coordBall (n+1) 1 ∩ {z | 0 < z i}, g z) =
      ∫⁻ x in hemisphereConeDomain i,
        ENNReal.ofReal ((x i)^n * (chord 1 (i.removeNth x))⁻¹) * g (hemisphereCone i x) := by
  rw [← hemisphereCone_image i]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (measurableSet_hemisphereConeDomain i)
    (fun x hx => (hasFDerivAt_hemisphereCone i hx).hasFDerivWithinAt)
    (hemisphereCone_injOn i)]
  apply setLIntegral_congr_fun (measurableSet_hemisphereConeDomain i)
  intro x hx
  change ENNReal.ofReal |(hemisphereConeDerivative i x).toLinearMap.det| * _ = _
  rw [det_hemisphereConeDerivative i hx, abs_of_pos
    (mul_pos (pow_pos hx.1.1 _) (inv_pos.2 (chord_pos hx.2)))]

lemma lintegral_pow_unitInterval (n : ℕ) :
    (∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (t^n)) =
      ENNReal.ofReal ((n+1 : ℝ)⁻¹) := by
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  rw [← ofReal_integral_eq_lintegral_ofReal ((continuous_pow n).intervalIntegrable (0 : ℝ) 1).1]
  · rw [← intervalIntegral.integral_of_le zero_le_one]
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact pow_nonneg ht.1.le n

def coneStrip {n : ℕ} (i : Fin (n+1)) (S : Set (Fin n → ℝ)) : Set (Fin (n+1) → ℝ) :=
  {x | x i ∈ Ioo (0 : ℝ) 1 ∧ i.removeNth x ∈ S}

lemma measurableSet_coneStrip {n : ℕ} (i : Fin (n+1)) {S : Set (Fin n → ℝ)}
    (hS : MeasurableSet S) : MeasurableSet (coneStrip i S) :=
  ((measurable_pi_apply i) measurableSet_Ioo).inter ((removeCoordinate i).measurable hS)

lemma coneStrip_subset {n : ℕ} (i : Fin (n+1)) {S : Set (Fin n → ℝ)}
    (hS : S ⊆ coordBall n 1) : coneStrip i S ⊆ hemisphereConeDomain i :=
  fun _ hx => ⟨hx.1, hS hx.2⟩

/-- Integrating the exact radial Jacobian leaves the hemisphere area density,
with the inverse dimension factor appearing in the cone definition of area. -/
theorem volume_hemisphereCone_strip {n : ℕ} (i : Fin (n+1))
    {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) (hSB : S ⊆ coordBall n 1) :
    volume (hemisphereCone i '' coneStrip i S) =
      ENNReal.ofReal ((n+1 : ℝ)⁻¹) * ∫⁻ y in S, ENNReal.ofReal (chord 1 y)⁻¹ := by
  have hs := measurableSet_coneStrip i hS
  have hsub := coneStrip_subset i hSB
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image volume hs
    (fun x hx => (hasFDerivAt_hemisphereCone i (hsub hx)).hasFDerivWithinAt)
    ((hemisphereCone_injOn i).mono hsub)]
  have he : (∫⁻ x in coneStrip i S, ENNReal.ofReal |(hemisphereConeDerivative i x).det|) =
      ∫⁻ x in coneStrip i S,
        ENNReal.ofReal ((x i)^n) * ENNReal.ofReal (chord 1 (i.removeNth x))⁻¹ := by
    apply setLIntegral_congr_fun hs
    intro x hx
    change ENNReal.ofReal |(hemisphereConeDerivative i x).toLinearMap.det| = _
    rw [det_hemisphereConeDerivative i (hsub hx), abs_of_pos
      (mul_pos (pow_pos hx.1.1 _) (inv_pos.2 (chord_pos (hSB hx.2)))),
      ENNReal.ofReal_mul (pow_nonneg hx.1.1.le n)]
  rw [he, setLIntegral_slice i hs _ (by unfold chord radiusSq Fin.removeNth; fun_prop)]
  rw [← lintegral_indicator hS, ← lintegral_const_mul _ (by unfold chord radiusSq; fun_prop)]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ S
  · have ht : {t : ℝ | i.insertNth t y ∈ coneStrip i S} = Ioo 0 1 := by
      ext t; simp [coneStrip, hy]
    simp only [ht, Fin.insertNth_apply_same, Fin.removeNth_insertNth,
      indicator_of_mem hy]
    rw [lintegral_mul_const _ (by fun_prop), lintegral_pow_unitInterval]
  · have ht : {t : ℝ | i.insertNth t y ∈ coneStrip i S} = ∅ := by
      ext t; simp [coneStrip, hy]
    simp [ht, hy]

end MahlerStokes

end

end OAI
