import OAI.Geometry.RCD.Coordinates.IntervalBilinearEnergy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace OAI

/-! # Integrating the actual Sobolev time family on the real line -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates

def intervalVectorExtension {E : Type*} [Zero E] {a b : ℝ}
    (u : Ioo a b → E) (t : ℝ) : E :=
  if ht : t ∈ Ioo a b then u ⟨t,ht⟩ else 0

theorem intervalVectorExtension_eq {E : Type*} [Zero E] {a b : ℝ}
    (u : Ioo a b → E) (t : Ioo a b) : intervalVectorExtension u t = u t := by
  simp only [intervalVectorExtension,dite_eq_left t.property]

theorem intervalVectorExtension_integrable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ}
    (u : Ioo a b → E) (hu : AEStronglyMeasurable u (volume.comap Subtype.val))
    {C : ℝ} (hb : ∀ t, ‖u t‖ ≤ C) : Integrable (intervalVectorExtension u) := by
  have hfin : volume (Ioo a b) ≠ ∞ :=
    ((measure_mono Ioo_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top).ne
  have hi : Integrable (fun _ : Ioo a b => C) (volume.comap Subtype.val) :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mp (integrableOn_const hfin)
  have hiu : Integrable u (volume.comap Subtype.val) :=
    hi.mono' hu (Eventually.of_forall hb)
  have he : IntegrableOn (intervalVectorExtension u) (Ioo a b) := by
    apply (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mpr
    simpa only [Function.comp_def,intervalVectorExtension_eq] using hiu
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp he
  intro t ht
  by_contra hn
  exact ht (by simp only [intervalVectorExtension,dite_eq_right hn])

theorem bilinear_intervalVectorExtension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ}
    (P : E →L[ℝ] E →L[ℝ] ℝ) (u : Ioo a b → E) (t : ℝ) :
    P (intervalVectorExtension u t) (intervalVectorExtension u t) =
      intervalExtension (fun q => P (u q) (u q)) t := by
  by_cases ht : t ∈ Ioo a b
  · simp only [intervalVectorExtension,intervalExtension,dite_eq_left ht]
  · simp only [intervalVectorExtension,intervalExtension,dite_eq_right ht,map_zero]

end RegularPointCoordinates

end

end OAI
