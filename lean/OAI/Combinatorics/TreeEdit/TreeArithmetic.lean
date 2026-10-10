import OAI.Combinatorics.TreeEdit.Model

namespace OAI

namespace TreeEdit.FiniteTree

universe u

attribute [local instance] Classical.propDecidable

@[reducible] def length (m T : ℕ) : ℕ → ℕ
  | 0 => 1
  | h + 1 => T * (m * length m T h)

lemma length_eq (m T h : ℕ) : length m T h = (m * T) ^ h := by
  induction h with
  | zero => rfl
  | succ h ih => simp only [length, ih, pow_succ]; ring

lemma few_prime_divisors {m b s T : ℕ} (p : Fin m → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (hb : 1 ≤ b) (hpb : ∀ i, b ≤ p i) (hT : T ≤ b ^ s)
    (d : ℤ) (hd : d ≠ 0) (hdT : d.natAbs < T) :
    (Finset.univ.filter (fun i => (p i : ℤ) ∣ d)).card < s := by
  classical
  let S := Finset.univ.filter (fun i => (p i : ℤ) ∣ d)
  have hcop : (↑S : Set (Fin m)).Pairwise (fun i j => IsCoprime (p i : ℤ) (p j : ℤ)) := by
    intro i _ j _ hij
    exact ((Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hij (hinj h))).isCoprime
  have hprod : (∏ i ∈ S, (p i : ℤ)) ∣ d :=
    Finset.prod_dvd_of_coprime hcop (fun i hi => (Finset.mem_filter.mp hi).2)
  have hprod' : (∏ i ∈ S, p i) ∣ d.natAbs := Int.natCast_dvd.mp (by simpa using hprod)
  have hle : b ^ S.card ≤ d.natAbs := by
    calc
      _ = ∏ _i ∈ S, b := (Finset.prod_const b).symm
      _ ≤ ∏ i ∈ S, p i := Finset.prod_le_prod (fun i _ => hpb i)
      _ ≤ d.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hd) hprod'
  by_contra hn
  have hh := pow_le_pow_right₀ hb (Nat.le_of_not_gt hn)
  exact (not_le_of_gt hdT) (hT.trans (hh.trans hle))

end TreeEdit.FiniteTree

end OAI
