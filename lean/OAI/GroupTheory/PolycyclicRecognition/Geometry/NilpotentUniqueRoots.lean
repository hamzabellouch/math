import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentCentralRoots

namespace OAI

/-! # Unique roots in torsion-free nilpotent groups

Induction through the torsion-free center quotient reduces equality of powers
to a central difference. The two elements then commute, and torsion freeness
kills that difference.
-/

namespace PolycyclicRecognition

variable {G : Type} [Group G] [Group.IsNilpotent G]

theorem nilpotent_isMulTorsionFree (hG : HasNoNontrivialTorsion G) : IsMulTorsionFree G := by
  apply Group.nilpotent_center_quotient_ind G
    (P := fun K _ _ => HasNoNontrivialTorsion K → IsMulTorsionFree K) ?_ ?_ hG
  · intro K _ _ _
    infer_instance
  · intro K _ _ ih hK
    let q := QuotientGroup.mk' (Subgroup.center K)
    let : IsMulTorsionFree (K ⧸ Subgroup.center K) := ih (nilpotent_centerQuotient_torsionFree hK)
    constructor
    intro n hn x y hxy
    change x ^ n = y ^ n at hxy
    have hq : q x = q y := pow_left_injective hn (by simpa only [map_pow] using congrArg q hxy)
    have hcentral : x * y⁻¹ ∈ Subgroup.center K := by
      apply (QuotientGroup.eq_one_iff (x * y⁻¹)).mp
      change q (x * y⁻¹) = 1
      rw [map_mul, map_inv, hq, mul_inv_cancel]
    have hcomm : Commute x y := by
      have hc := Subgroup.mem_center_iff.mp hcentral y
      have hh := congrArg (fun z : K => z * y) hc
      have hyx : y * x = x * y := by simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh
      exact hyx.symm
    have hp : (x * y⁻¹) ^ n = 1 := by
      rw [hcomm.inv_right.mul_pow, inv_pow, hxy, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hK (x * y⁻¹) n hn hp)

end PolycyclicRecognition

end OAI
