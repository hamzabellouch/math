import OAI.Analysis.LipschitzFree.GraphColoring

namespace OAI

/-!
# Good-vertex density in the all-colorings sequence
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.GraphProducer
open scoped Classical
variable (A C S : Type*) [Fintype A] [DecidableEq A] [Fintype C] [Nonempty C] [Fintype S]

theorem exists_rare_component (Q H V : ℕ) (hQpos : 0 < Q) (hHpos : 0 < H)
    (hDpos : 0 < Nat.card (A × Bool))
    (hk : 2 * Nat.card (A × Bool) * Q * H < Nat.card C)
    (compatible : Vertex A C → S → Prop) (trans : S → S → Prop) (P : S → Finset C)
    (hP : ∀ j, (P j).card ≤ H)
    (hcolor : ∀ z j, compatible z j → sequenceColor A C z ∈ P j)
    (hQ : ∀ j, Fintype.card {k : S // trans j k} ≤ Q) :
    ∃ n : ℕ, 2 ≤ n ∧
      20 * V * Nat.card {z : (Cayley A n → C) × Cayley A n //
        ¬ (sequenceGraph A C).Good compatible trans n (intoSequence A C n z)} <
      Nat.card ((Cayley A n → C) × Cayley A n) := by
  let d := Nat.card (A × Bool)
  let k := Nat.card C
  let s := Nat.card S
  let q := d*Q*H
  have hq : 0 < q := Nat.mul_pos (Nat.mul_pos hDpos hQpos) hHpos
  have hk' : 2*q < k := by simpa only [q, d, k, Nat.mul_assoc] using hk
  have hkp : 0 < k := lt_trans (by omega) hk'
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (20*V*s*H) (by norm_num : 1 < (2 : ℕ))
  let n := m+2
  have hn : 20*V*s*H < 2^n := hm.trans_le (Nat.pow_le_pow_right (by omega) (by dsimp [n]; omega))
  have hcoeff : 20*V*(d^n*(s*Q^n)*H^(n+1)) < k^(n+1) := by
    calc
      _ = (20*V*s*H) * q^n := by dsimp [q]; simp only [mul_pow, pow_succ]; ring
      _ < 2^n * q^n := Nat.mul_lt_mul_of_pos_right hn (pow_pos hq n)
      _ = (2*q)^n := (mul_pow ..).symm
      _ ≤ k^n := Nat.pow_le_pow_left hk'.le n
      _ ≤ k^(n+1) := Nat.pow_le_pow_right hkp (Nat.le_succ _)
  have hcount := rare_matched_bound A C S n n Q H le_rfl
    (fun z => compatible (intoSequence A C n z)) trans P hP
    (fun z j hj => hcolor _ _ hj) hQ
  have heq : {z : (Cayley A n → C) × Cayley A n //
      ¬ (allColoringsGraph A C n).Good (fun z => compatible (intoSequence A C n z)) trans n z} =
      {z : (Cayley A n → C) × Cayley A n //
      ¬ (sequenceGraph A C).Good compatible trans n (intoSequence A C n z)} := by
    congr 1
    funext z
    exact propext (not_congr (sequence_good A C compatible trans n n z).symm)
  rw [heq] at hcount
  change _ * k^(n+1) ≤ d^n*(s*Q^n)*H^(n+1)*_ at hcount
  have hroot : 0 < Nat.card ((Cayley A n → C) × Cayley A n) := Nat.card_pos
  refine ⟨n, by dsimp [n]; omega, ?_⟩
  by_contra h
  have hh := Nat.mul_le_mul_right (k^(n+1)) (Nat.le_of_not_gt h)
  have hc := Nat.mul_le_mul_left (20*V) hcount
  have hf := Nat.mul_lt_mul_of_pos_right hcoeff hroot
  nlinarith

end DiscreteFree.GraphProducer
end

end

end OAI
