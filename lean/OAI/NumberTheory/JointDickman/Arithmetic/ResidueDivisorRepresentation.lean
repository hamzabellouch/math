import OAI.NumberTheory.JointDickman.Probability.FixedResidueReduction

namespace OAI

/-! # Every residue class is a fixed multiple of a unit class -/
namespace JointDickman

theorem residue_fixed_divisor_representation {q : ℕ} [NeZero q] (r : ZMod q) :
    ∃ d e a : ℕ, 0 < d ∧ 0 < e ∧ q = d*e ∧
      r = ((d*a : ℕ) : ZMod q) ∧ a.Coprime e := by
  let d := r.val.gcd q
  let e := q/d
  let a := r.val/d
  have hd : 0 < d := Nat.gcd_pos_of_pos_right r.val (NeZero.pos q)
  have he : 0 < e := Nat.div_gcd_pos_of_pos_right r.val (NeZero.pos q)
  have hq : d*e = q := Nat.mul_div_cancel' (Nat.gcd_dvd_right r.val q)
  have ha : d*a = r.val := Nat.mul_div_cancel' (Nat.gcd_dvd_left r.val q)
  refine ⟨d,e,a,hd,he,hq.symm,?_,?_⟩
  · rw [ha]
    exact (ZMod.natCast_zmod_val r).symm
  · exact Nat.gcd_div_gcd_div_gcd_of_pos_right (NeZero.pos q)

end JointDickman

end OAI
