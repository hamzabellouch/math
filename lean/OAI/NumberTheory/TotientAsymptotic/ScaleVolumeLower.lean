import OAI.NumberTheory.TotientAsymptotic.SimplexScaling

namespace OAI

/-! The lower-volume bridge for the concrete diagonal prefix contraction. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma simplexScale_volume_lower {N : ℕ} (κ : Fin N → ℝ)
    (hκ : ∀ i,0 < κ i) {S T : Set (Fin N → ℝ)}
    (hT : MeasurableSet T) (hfinite : volume T ≠ ⊤)
    (hmap : Set.MapsTo (simplexScale κ) S T) :
    volume.real S/(∏ i : Fin N,κ i) ≤ volume.real T := by
  have hp : 0 < ∏ i : Fin N,κ i := Finset.prod_pos (fun i _ => hκ i)
  have hdet : LinearMap.det (simplexScale κ) ≠ 0 := by
    rw [simplexScale_det]
    exact inv_ne_zero hp.ne'
  have hh := measure_mono (μ:=volume) (show S ⊆ simplexScale κ ⁻¹' T from hmap)
  rw [←Measure.map_apply (simplexScale κ).continuous_of_finiteDimensional.measurable hT,
    Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet,simplexScale_det,inv_inv,
    abs_of_pos hp,Measure.smul_apply,smul_eq_mul] at hh
  have hr := ENNReal.toReal_mono
    (show ENNReal.ofReal (∏ i : Fin N,κ i)*volume T ≠ ⊤ from
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite) hh
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hp.le] at hr
  apply (div_le_iff₀ hp).mpr
  simpa only [Measure.real,mul_comm] using hr

end TotientAsymptotic

end

end OAI
