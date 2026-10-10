import Mathlib
import OAI.Computability.QuantumFactoring.RationalExpressionResources

namespace OAI



section

namespace ExactQuantumFactoring
lemma nat_size_mul_le (a b : ℕ) : (a*b).size ≤ a.size+b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact (Nat.mul_le_mul_left a (Nat.size_le.mp (le_refl b.size)).le).trans_lt
    (Nat.mul_lt_mul_of_pos_right (Nat.size_le.mp (le_refl a.size)) (by positivity))
lemma nat_size_add_le (a b : ℕ) : (a+b).size ≤ a.size+b.size+1 := by
  apply Nat.size_le.mpr
  have ha : a<2^(a.size+b.size) :=
    (Nat.size_le.mp (le_refl a.size)).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have hb : b<2^(a.size+b.size) :=
    (Nat.size_le.mp (le_refl b.size)).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  rw [pow_succ]
  omega
lemma nat_size_pow_le (a k : ℕ) : (a^k).size ≤ k*a.size+1 := by
  apply Nat.size_le.mpr
  have h : a^k ≤ (2^a.size)^k := Nat.pow_le_pow_left (Nat.size_le.mp (le_refl a.size)).le k
  rw [← pow_mul,Nat.mul_comm a.size] at h
  rw [pow_succ]
  have hp : 0<2^(k*a.size) := by positivity
  omega

namespace PolyBound
lemma sizeMul {f g : ℕ → ℕ} (hf : PolyBound (fun n => (f n).size))
    (hg : PolyBound (fun n => (g n).size)) : PolyBound (fun n => (f n*g n).size) :=
  (hf.add hg).of_le (fun n => nat_size_mul_le (f n) (g n))
lemma sizeAdd {f g : ℕ → ℕ} (hf : PolyBound (fun n => (f n).size))
    (hg : PolyBound (fun n => (g n).size)) : PolyBound (fun n => (f n+g n).size) :=
  ((hf.add hg).add (const 1)).of_le (fun n => nat_size_add_le (f n) (g n))
lemma sizePow {f g : ℕ → ℕ} (hf : PolyBound (fun n => (f n).size))
    (hg : PolyBound g) : PolyBound (fun n => (f n^g n).size) :=
  ((hg.mul hf).add (const 1)).of_le (fun n => nat_size_pow_le (f n) (g n))
end PolyBound

/-- Bit-length bounds for exact normalized rational constants appearing in the
emitted circuit. These are not bounds on their exponentially large values. -/
def RatHeightPoly (a : ℕ → ℚ) : Prop :=
  PolyBound (fun n => (a n).num.natAbs.size) ∧ PolyBound (fun n => (a n).den.size)
namespace RatHeightPoly
variable {a b : ℕ → ℚ}
lemma constant (q : ℚ) : RatHeightPoly (fun _=>q) := ⟨PolyBound.const _,PolyBound.const _⟩
lemma natCast {f : ℕ → ℕ} (hf : PolyBound (fun n=>(f n).size)) :
    RatHeightPoly (fun n => (f n : ℚ)) := by
  constructor
  · simpa using hf
  · exact PolyBound.of_le (PolyBound.const 1) (fun n => by simp)
lemma intCast {f : ℕ → ℤ} (hf : PolyBound (fun n=>(f n).natAbs.size)) :
    RatHeightPoly (fun n => (f n : ℚ)) := by
  constructor
  · simpa using hf
  · exact PolyBound.of_le (PolyBound.const 1) (fun n => by simp)
lemma add (ha : RatHeightPoly a) (hb : RatHeightPoly b) : RatHeightPoly (fun n=>a n+b n) := by
  constructor
  · apply ((ha.1.sizeMul hb.2).sizeAdd (hb.1.sizeMul ha.2)).of_le
    intro n
    apply Nat.size_le_size
    rw [Rat.num_add]
    apply (Int.natAbs_ediv_le_natAbs _ _).trans
    simpa only [Int.natAbs_mul,Int.natAbs_natCast] using
      (Int.natAbs_add_le ((a n).num*(b n).den) ((b n).num*(a n).den))
  · apply (ha.2.sizeMul hb.2).of_le
    intro n
    apply Nat.size_le_size
    rw [Rat.den_add]
    exact Nat.div_le_self _ _
lemma neg (ha : RatHeightPoly a) : RatHeightPoly (fun n=> -(a n)) := by
  constructor
  · simpa only [Rat.neg_num,Int.natAbs_neg] using ha.1
  · simpa only [Rat.neg_den] using ha.2
lemma sub (ha : RatHeightPoly a) (hb : RatHeightPoly b) : RatHeightPoly (fun n=>a n-b n) := by
  simpa only [sub_eq_add_neg] using ha.add hb.neg
lemma mul (ha : RatHeightPoly a) (hb : RatHeightPoly b) : RatHeightPoly (fun n=>a n*b n) := by
  constructor
  · apply (ha.1.sizeMul hb.1).of_le
    intro n
    apply Nat.size_le_size
    rw [Rat.mul_num]
    convert Int.natAbs_ediv_le_natAbs ((a n).num*(b n).num) _ using 1
    exact (Int.natAbs_mul _ _).symm
  · apply (ha.2.sizeMul hb.2).of_le
    intro n
    apply Nat.size_le_size
    rw [Rat.mul_den]
    exact Nat.div_le_self _ _
lemma inv (ha : RatHeightPoly a) : RatHeightPoly (fun n=>(a n)⁻¹) := by
  constructor
  · apply ha.2.of_le
    intro n
    apply Nat.size_le_size
    rw [Rat.num_inv,Int.natAbs_mul,Int.natAbs_natCast,Int.natAbs_sign]
    split_ifs <;> simp
  · apply (ha.1.add (PolyBound.const 1)).of_le
    intro n
    rw [Rat.den_inv]
    split_ifs
    · simp only [Nat.size_one]; omega
    · omega
lemma div (ha : RatHeightPoly a) (hb : RatHeightPoly b) : RatHeightPoly (fun n=>a n/b n) := by
  simpa only [div_eq_mul_inv] using ha.mul hb.inv
lemma pow {f : ℕ→ℕ} (ha : RatHeightPoly a) (hf : PolyBound f) :
    RatHeightPoly (fun n=>(a n)^(f n)) := by
  constructor
  · simpa only [Rat.num_pow,Int.natAbs_pow] using ha.1.sizePow hf
  · simpa only [Rat.den_pow] using ha.2.sizePow hf
lemma constExpr {v : ℕ→Type*} (ha : RatHeightPoly a) :
    RatExprPoly (fun n=>RatExpr.const (a n) : ∀ n,RatExpr (v n)) :=
  RatExprPoly.const ha.1 ha.2
end RatHeightPoly
end ExactQuantumFactoring

end



end OAI
