import Mathlib
import OAI.Probability.LatticeSurface.Convexity.BrunnMinkowski
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.SliceDensity
import OAI.Probability.LatticeSurface.Convexity.SliceGeometry
import OAI.Probability.LatticeSurface.Convexity.WeightedPrekopa
import OAI.Probability.LatticeSurface.Dynamics.DisplacementInequality

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace FacetVolume

lemma integrable_moment_pair {n : ℕ} {K : Set (Fin (n+1) → ℝ)} (hK : IsCompact K) :
    Integrable (fun z : ℝ × (Fin n → ℝ) => K.indicator (fun w => w 0) (Fin.cons z.1 z.2))
      (volume.prod volume) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have he (z : ℝ × (Fin n → ℝ)) : e z = Fin.cons z.1 z.2 := by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk, Fin.zero_succAbove]
  have hpres := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have hi : Integrable (K.indicator (fun w => w 0)) :=
    ((continuous_apply 0).continuousOn.integrableOn_compact hK).integrable_indicator hK.measurableSet
  have hip := hpres.integrable_comp_of_integrable hi
  change Integrable (fun x => K.indicator (fun w => w 0) (e x)) volume at hip
  simp only [he, Measure.volume_eq_prod] at hip
  exact hip

lemma sliceMoment_as_integral {n : ℕ} {K : Set (Fin (n+1) → ℝ)} (hK : IsCompact K) (t : ℝ) :
    t*sliceVolume K t = ∫ x, K.indicator (fun w => w 0) (Fin.cons t x) := by
  rw [sliceVolume_as_integral hK, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : Fin.cons t x ∈ K
  · simp only [indicator_of_mem hx, mul_one, Fin.cons_zero]
  · simp only [indicator_of_notMem hx, mul_zero]

lemma integral_sliceMoment {n : ℕ} {K : Set (Fin (n+1) → ℝ)} (hK : IsCompact K) :
    (∫ t, t*sliceVolume K t) = ∫ z in K, z 0 := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have he (z : ℝ × (Fin n → ℝ)) : e z = Fin.cons z.1 z.2 := by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk, Fin.zero_succAbove]
  have hpres := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have hint := hpres.integral_comp e.measurableEmbedding (K.indicator (fun w => w 0))
  rw [integral_indicator hK.measurableSet] at hint
  change (∫ x, K.indicator (fun w => w 0) (e x)) = _ at hint
  simp only [he, Measure.volume_eq_prod] at hint
  rw [integral_prod _ (integrable_moment_pair hK)] at hint
  simpa only [← sliceMoment_as_integral hK] using hint

lemma intervalIntegral_sliceMoment {n : ℕ} {K : Set (Fin (n+1) → ℝ)} {a b : ℝ}
    (hK : IsCompact K) (hab : a ≤ b) (hproj : ∀ z ∈ K, z 0 ∈ Icc a b) :
    (∫ t in a..b, t*sliceVolume K t) = ∫ z in K, z 0 := by
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    ← integral_sliceMoment hK]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  rw [sliceVolume_eq_zero_outside hproj ht, mul_zero]

end FacetVolume

end

end OAI
