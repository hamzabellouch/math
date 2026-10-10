import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod

namespace OAI

/-! Exact product-measure dilation in the horizontal coordinate. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert

def horizontalDilation (r : ℝ) (hr : r ≠ 0) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun z := (r*z.1,z.2)
  invFun z := (z.1/r,z.2)
  left_inv z := by ext <;> simp [hr]
  right_inv z := by
    ext
    · dsimp
      field_simp
    · rfl
  measurable_toFun := (measurable_const.mul measurable_fst).prodMk measurable_snd
  measurable_invFun := (measurable_fst.div_const r).prodMk measurable_snd

@[simp] theorem horizontalDilation_apply (r : ℝ) (hr : r ≠ 0) (z : ℝ × ℝ) :
    horizontalDilation r hr z = (r*z.1,z.2) := rfl

theorem map_horizontalDilation (r : ℝ) (hr : r ≠ 0) :
    Measure.map (horizontalDilation r hr) (volume.prod volume) =
      ENNReal.ofReal |r⁻¹| • (volume.prod volume) := by
  change Measure.map (Prod.map (fun x : ℝ => r*x) id) (volume.prod volume) = _
  rw [← Measure.map_prod_map volume volume (by fun_prop) measurable_id,Measure.map_id]
  have hm : Measure.map (fun x : ℝ => r*x) volume = ENNReal.ofReal |r⁻¹| • volume := by
    simpa only [smul_eq_mul,Module.finrank_self,pow_one] using
      (Measure.map_addHaar_smul (μ := (volume : Measure ℝ)) hr)
  rw [hm,Measure.prod_smul_left]

theorem integral_horizontalDilation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × ℝ → E) (r : ℝ) (hr : r ≠ 0) :
    (∫ z, f (horizontalDilation r hr z) ∂volume.prod volume) =
      |r⁻¹| • (∫ z, f z ∂volume.prod volume) := by
  rw [← integral_map_equiv (horizontalDilation r hr),map_horizontalDilation,integral_smul_measure]
  simp only [ENNReal.toReal_ofReal (abs_nonneg _)]

theorem measure_horizontalDilation_preimage (r : ℝ) (hr : r ≠ 0)
    (s : Set (ℝ × ℝ)) (hs : MeasurableSet s) :
    (volume.prod volume) (horizontalDilation r hr ⁻¹' s) =
      ENNReal.ofReal |r⁻¹| * (volume.prod volume) s := by
  rw [← Measure.map_apply (horizontalDilation r hr).measurable hs,map_horizontalDilation]
  rfl

/-- The same horizontal scaling in the reference packet convention `(y,x)`. -/
def referenceHorizontalDilation (r : ℝ) (hr : r ≠ 0) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun z := (z.1,r*z.2)
  invFun z := (z.1,z.2/r)
  left_inv z := by ext <;> simp [hr]
  right_inv z := by
    ext
    · rfl
    · dsimp
      field_simp
  measurable_toFun := measurable_fst.prodMk (measurable_const.mul measurable_snd)
  measurable_invFun := measurable_fst.prodMk (measurable_snd.div_const r)

theorem map_referenceHorizontalDilation (r : ℝ) (hr : r ≠ 0) :
    Measure.map (referenceHorizontalDilation r hr) (volume.prod volume) =
      ENNReal.ofReal |r⁻¹| • (volume.prod volume) := by
  change Measure.map (Prod.map id (fun x : ℝ => r*x)) (volume.prod volume) = _
  rw [← Measure.map_prod_map volume volume measurable_id (by fun_prop),Measure.map_id]
  have hm : Measure.map (fun x : ℝ => r*x) volume = ENNReal.ofReal |r⁻¹| • volume := by
    simpa only [smul_eq_mul,Module.finrank_self,pow_one] using
      (Measure.map_addHaar_smul (μ := (volume : Measure ℝ)) hr)
  rw [hm,Measure.prod_smul_right]

theorem integral_referenceHorizontalDilation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × ℝ → E) (r : ℝ) (hr : r ≠ 0) :
    (∫ z, f (referenceHorizontalDilation r hr z) ∂volume.prod volume) =
      |r⁻¹| • (∫ z, f z ∂volume.prod volume) := by
  rw [← integral_map_equiv (referenceHorizontalDilation r hr),map_referenceHorizontalDilation,integral_smul_measure]
  simp only [ENNReal.toReal_ofReal (abs_nonneg _)]

end LipschitzHilbert

end

end OAI
