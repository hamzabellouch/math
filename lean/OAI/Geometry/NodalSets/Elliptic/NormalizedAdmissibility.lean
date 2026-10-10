import OAI.Geometry.NodalSets.Elliptic.WeightedHessianStability

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma normalized_strict_to_direction (g H : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (p t : Coord) (hp : 0 < g p p)
    (horth : g (metricNormalize g p) t = 0)
    (hstrict : 0 < (g p p/(g p p+4))*H (metricNormalize g p) (metricNormalize g p)+H t t) :
    g p t = 0 ∧ 0 < H p p+(g p p+4)*H t t := by
  have hs0 : Real.sqrt (g p p) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have horth' : (Real.sqrt (g p p))⁻¹*g p t = 0 := by
    simpa only [metricNormalize,map_smul,smul_apply,smul_eq_mul] using horth
  have hpt : g p t = 0 := (mul_eq_zero.mp horth').resolve_left (inv_ne_zero hs0)
  have hval : 0 < weightedHessianValue g H p t := by
    rw [weightedHessianValue_normalized g H p t hp]
    exact hstrict
  have hd : 0 < g p p+4 := by linarith
  have hmul := mul_pos hd hval
  have heq : (g p p+4)*weightedHessianValue g H p t = H p p+(g p p+4)*H t t := by
    unfold weightedHessianValue
    field_simp
  rw [heq] at hmul
  exact ⟨hpt,hmul⟩

end
end Yau.Geometry

end OAI
