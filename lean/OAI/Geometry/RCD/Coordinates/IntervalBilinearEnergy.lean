import OAI.Geometry.RCD.Coordinates.PositiveBilinearIntegralLower
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! # Real-time integrals of a bounded measurable Sobolev quadratic form -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates

def intervalExtension {a b : ℝ} (f : Ioo a b → ℝ) (t : ℝ) : ℝ :=
  if ht : t ∈ Ioo a b then f ⟨t,ht⟩ else 0

theorem intervalExtension_eq {a b : ℝ} (f : Ioo a b → ℝ) (t : Ioo a b) :
    intervalExtension f t = f t := by simp only [intervalExtension,dite_eq_left t.property]

theorem integral_intervalExtension {a b : ℝ} (f : Ioo a b → ℝ) (θ : ℝ → ℝ) :
    (∫ t in Ioo a b, θ t*intervalExtension f t) =
      ∫ t : Ioo a b, θ t*f t ∂volume.comap Subtype.val := by
  rw [← integral_subtype_comap measurableSet_Ioo (fun t => θ t*intervalExtension f t)]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    change θ t*intervalExtension f t = θ t*f t
    rw [intervalExtension_eq]

theorem interval_bilinear_energy_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b : ℝ} (P : E →L[ℝ] E →L[ℝ] ℝ)
    (v : Ioo a b → E) (hv : AEStronglyMeasurable v (volume.comap Subtype.val))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ t, ‖v t‖ ≤ C) :
    IntegrableOn (intervalExtension (fun t => P (v t) (v t))) (Ioo a b) := by
  have hfin : volume (Ioo a b) ≠ ∞ :=
    ((measure_mono Ioo_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top).ne
  have hi : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Ioo a b) := integrableOn_const hfin
  have hi' : Integrable (fun _ : Ioo a b => (1:ℝ)) (volume.comap Subtype.val) :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mp hi
  have hp : Integrable (fun t => P (v t) (v t)) (volume.comap Subtype.val) := by
    have hh := hi'.mul_bdd (P.aestronglyMeasurable_comp₂ hv hv)
      (Eventually.of_forall fun t => (P.le_opNorm₂ _ _).trans (show
        ‖P‖*‖v t‖*‖v t‖ ≤ ‖P‖*C*C from by gcongr <;> exact hb t))
    simpa only [one_mul] using hh
  apply (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mpr
  simpa only [Function.comp_def,intervalExtension_eq] using hp

end RegularPointCoordinates

end

end OAI
