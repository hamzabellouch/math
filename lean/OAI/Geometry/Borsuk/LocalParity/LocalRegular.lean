import Mathlib

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped RealInnerProductSpace Topology
section LocalRegular
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma regular_inner_positive (D : E ≃L[ℝ] E) {g : E → E}
    (h0 : g 0 = 0) (hd : HasFDerivAt g D.toContinuousLinearMap 0) :
    ∃ δ > 0, ∀ v, ‖v‖ < δ → v ≠ 0 → 0 < ⟪v,D.symm (g v)⟫ := by
  let H : E → E := fun v => D.symm (g v)
  have hH : HasFDerivAt H (ContinuousLinearMap.id ℝ E) 0 := by
    convert D.symm.hasFDerivAt.comp 0 hd using 1 <;> ext v <;> simp [H]
  have hH0 : H 0 = 0 := by simp [H,h0]
  have herr := hH.isLittleO.def (show (0:ℝ) < 1/2 by norm_num)
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp herr
  refine ⟨δ,hδ,?_⟩
  intro v hv hv0
  have hb := hball (by simpa only [dist_zero_right] using hv)
  simp only [hH0,sub_zero,ContinuousLinearMap.id_apply] at hb
  have hi : |⟪v,H v - v⟫| ≤ ‖v‖ * ((1/2:ℝ)*‖v‖) :=
    (abs_real_inner_le_norm v _).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
  have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  rw [inner_sub_right,real_inner_self_eq_norm_sq] at hi
  change 0 < ⟪v,H v⟫
  nlinarith [neg_abs_le ⟪v,H v⟫,neg_abs_le (⟪v,H v⟫-‖v‖^2)]

lemma positive_inner_convex {v x y : E} (hx : 0 < ⟪v,x⟫) (hy : 0 < ⟪v,y⟫)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : 0 < ⟪v,(1-t) • x + t • y⟫ := by
  simp only [inner_add_right,real_inner_smul_right]
  by_cases ht0 : t = 0
  · simpa [ht0] using hx
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) hx.le)
      (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) hy)

lemma regular_mixed_zero (D : E ≃L[ℝ] E) {g : E → E} {v b : E} {lam t : ℝ}
    (hp : v ≠ 0 → 0 < ⟪v,D.symm (g v)⟫) (hb : v ≠ 0 → 0 < ⟪v,b⟫)
    (hl : 0 < lam) (ht : t ∈ Set.Icc 0 1)
    (hz : (1-t) • (lam • g v) + t • D b = 0) : v = 0 := by
  by_contra hv
  have hh := positive_inner_convex (by simpa only [real_inner_smul_right] using mul_pos hl (hp hv)) (hb hv) ht
    (v := v) (x := lam • D.symm (g v))
  have he := congrArg D.symm hz
  simp only [map_add,map_smul,D.symm_apply_apply,map_zero] at he
  rw [he,inner_zero_right] at hh
  exact (lt_irrefl (0:ℝ)) hh
end LocalRegular
end BorsukNine

end OAI
