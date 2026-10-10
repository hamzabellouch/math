import OAI.NumberTheory.TwoPoint.Circuits.CircuitDyadicBudgets

namespace OAI

/-! The explicit dyadic independence budget is polynomial in its accuracy
parameter. The closure argument avoids expanding enormous fixed constants. -/

namespace TwoPointCorrelations

def NatPolynomialGrowth (f : ℕ → ℕ) : Prop :=
  ∃ K C : ℕ, ∀ j, f j ≤ K * (j + 1) ^ C

namespace NatPolynomialGrowth

theorem const (a : ℕ) : NatPolynomialGrowth (fun _ => a) :=
  ⟨a, 0, fun _ => by simp⟩

theorem id : NatPolynomialGrowth (fun j => j) :=
  ⟨1, 1, fun _ => by simp⟩

theorem add {f g : ℕ → ℕ} (hf : NatPolynomialGrowth f) (hg : NatPolynomialGrowth g) :
    NatPolynomialGrowth (fun j => f j + g j) := by
  obtain ⟨K, C, hK⟩ := hf
  obtain ⟨L, D, hL⟩ := hg
  refine ⟨K + L, C + D, fun j => ?_⟩
  calc
    _ ≤ K * (j + 1) ^ C + L * (j + 1) ^ D := Nat.add_le_add (hK j) (hL j)
    _ ≤ K * (j + 1) ^ (C + D) + L * (j + 1) ^ (C + D) := by
      gcongr <;> omega
    _ = _ := by ring

theorem mul {f g : ℕ → ℕ} (hf : NatPolynomialGrowth f) (hg : NatPolynomialGrowth g) :
    NatPolynomialGrowth (fun j => f j * g j) := by
  obtain ⟨K, C, hK⟩ := hf
  obtain ⟨L, D, hL⟩ := hg
  refine ⟨K * L, C + D, fun j => ?_⟩
  calc
    _ ≤ (K * (j + 1) ^ C) * (L * (j + 1) ^ D) := Nat.mul_le_mul (hK j) (hL j)
    _ = _ := by rw [pow_add]; ring

theorem pow {f : ℕ → ℕ} (hf : NatPolynomialGrowth f) (k : ℕ) :
    NatPolynomialGrowth (fun j => f j ^ k) := by
  obtain ⟨K, C, hK⟩ := hf
  refine ⟨K ^ k, C * k, fun j => ?_⟩
  calc
    _ ≤ (K * (j + 1) ^ C) ^ k := Nat.pow_le_pow_left (hK j) k
    _ = _ := by rw [mul_pow, pow_mul]

end NatPolynomialGrowth

theorem bravermanDegree_polynomial : NatPolynomialGrowth bravermanDegree := by
  have hid := NatPolynomialGrowth.id
  have hbase : NatPolynomialGrowth bravermanBase :=
    ((NatPolynomialGrowth.const 40).mul (hid.add (NatPolynomialGrowth.const 1))).mul
      (hid.add (NatPolynomialGrowth.const 3))
  have hnorm : NatPolynomialGrowth bravermanNormExponent :=
    ((NatPolynomialGrowth.const 2).mul hid |>.add (NatPolynomialGrowth.const 3)).mul
      (((NatPolynomialGrowth.const 2).mul hbase |>.add (NatPolynomialGrowth.const 2)).pow 22)
  have herror : NatPolynomialGrowth bravermanErrorExponent :=
    (NatPolynomialGrowth.const 20).mul (hid.add (NatPolynomialGrowth.const 3))
  have hr : NatPolynomialGrowth bravermanSwitches :=
    ((((NatPolynomialGrowth.const 2).mul hnorm).add herror).add hid).add
      (NatPolynomialGrowth.const 10)
  have hden : NatPolynomialGrowth (fun j => switchingDenominator (bravermanSwitches j)) :=
    (NatPolynomialGrowth.const 24).mul
      ((((NatPolynomialGrowth.const 2).mul hr).add (NatPolynomialGrowth.const 3)).pow 2)
  have hD : NatPolynomialGrowth (fun j => switchingDegree 89 (bravermanSwitches j)) :=
    (((NatPolynomialGrowth.const 8).mul (hr.add (NatPolynomialGrowth.const 1))).mul
      (hden.pow 89))
  exact (NatPolynomialGrowth.const 2).mul ((hbase.pow 22).add hD)

theorem bravermanDegree_polynomial_positive :
    ∃ K C : ℕ, 0 < K ∧ 0 < C ∧ ∀ j, bravermanDegree j ≤ K * (j + 1) ^ C := by
  obtain ⟨K, C, h⟩ := bravermanDegree_polynomial
  refine ⟨K + 1, C + 1, by omega, by omega, fun j => (h j).trans ?_⟩
  exact Nat.mul_le_mul (Nat.le_succ K) (Nat.pow_le_pow_right (by omega) (Nat.le_succ C))

end TwoPointCorrelations

end OAI
