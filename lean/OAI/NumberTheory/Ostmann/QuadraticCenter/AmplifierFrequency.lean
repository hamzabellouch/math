import OAI.NumberTheory.Ostmann.QuadraticCenter.AmplifiedPoisson
import OAI.NumberTheory.Ostmann.QuadraticCenter.FrequencySplit
import OAI.NumberTheory.Ostmann.QuadraticCenter.NormalizedPoisson

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators ComplexConjugate

def subsetAmplifierFrequency {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (U : Finset ι)
    (lam : ℝ) (q : ℕ) (X a : ℝ) (u : ℤ) : ℂ := by
  let d := ∏ i : U, p i
  letI : NeZero d := ⟨(subset_modulus_pos p U).ne'⟩
  exact (lam : ℂ) ^ U.card * (jacobiSym (d : ℤ) q : ℂ) /
    (Real.sqrt (((q : ℝ) / X) * d) : ℂ) *
    quadraticFourierFrequency q d (subsetCenteredProduct p hcop S U) (q : ZMod d)⁻¹ a ((q : ℝ) / X) u

def amplifierFrequency {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (lam : ℝ) (q : ℕ) (X a : ℝ) (u : ℤ) : ℂ :=
  ∑ U : Finset ι, subsetAmplifierFrequency p hcop S U lam q X a u

theorem subsetAmplifierFrequency_summable {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (U : Finset ι)
    (lam : ℝ) (q : ℕ) [NeZero q] {X : ℝ} (hX : 0 < X) (a : ℝ) :
    Summable (subsetAmplifierFrequency p hcop S U lam q X a) := by
  let : NeZero (∏ i : U, p i) := ⟨(subset_modulus_pos p U).ne'⟩
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_neZero q
  exact (quadraticFourierFrequency_summable q (∏ i : U, p i)
    (subsetCenteredProduct p hcop S U)
    (norm_centeredProduct_le_one (fun i : U => p i) (subset_pairwise_coprime p hcop U)
      (fun i => S i)) (q : ZMod (∏ i : U, p i))⁻¹ a (div_pos hq hX)).mul_left _

theorem amplifierFrequency_summable {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (lam : ℝ) (q : ℕ) [NeZero q]
    {X : ℝ} (hX : 0 < X) (a : ℝ) :
    Summable (amplifierFrequency p hcop S lam q X a) := by
  exact summable_sum (fun U _ => subsetAmplifierFrequency_summable p hcop S U lam q hX a)

theorem subsetAmplifierFrequency_neg {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (U : Finset ι)
    (lam : ℝ) (q : ℕ) (X a : ℝ) (u : ℤ) :
    subsetAmplifierFrequency p hcop S U lam q X a (-u) =
      (jacobiSym (-1) q : ℂ) * conj (subsetAmplifierFrequency p hcop S U lam q X a u) := by
  let : NeZero (∏ i : U, p i) := ⟨(subset_modulus_pos p U).ne'⟩
  have hr := centeredProduct_real (fun i : U => p i) (subset_pairwise_coprime p hcop U) (fun i => S i)
  dsimp only [subsetAmplifierFrequency]
  rw [quadraticFourierFrequency_neg q _ (subsetCenteredProduct p hcop S U) hr]
  simp only [map_mul, map_div₀, map_pow, map_intCast, Complex.conj_ofReal]
  ring

theorem amplifierFrequency_neg {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (lam : ℝ) (q : ℕ) (X a : ℝ) (u : ℤ) :
    amplifierFrequency p hcop S lam q X a (-u) =
      (jacobiSym (-1) q : ℂ) * conj (amplifierFrequency p hcop S lam q X a u) := by
  simp only [amplifierFrequency, subsetAmplifierFrequency_neg, map_sum, Finset.mul_sum]

theorem amplifierFrequency_zero {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (lam : ℝ) {q : ℕ} (hq : 1 < q) (X a : ℝ) :
    amplifierFrequency p hcop S lam q X a 0 = 0 := by
  unfold amplifierFrequency
  apply Finset.sum_eq_zero
  intro U hU
  simp only [subsetAmplifierFrequency, quadraticFourierFrequency, jacobiSym.zero_left hq,
    Int.cast_zero, zero_mul, mul_zero]

theorem amplifierFrequency_two_positive {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (lam : ℝ) {q : ℕ} [NeZero q]
    (hq : 1 < q) {X : ℝ} (hX : 0 < X) (a : ℝ) :
    ‖∑' u : ℤ, amplifierFrequency p hcop S lam q X a u‖ ≤
      2 * ‖∑' n : ℕ, amplifierFrequency p hcop S lam q X a ((n : ℤ) + 1)‖ := by
  apply norm_tsum_le_two_positive (ε := (jacobiSym (-1) q : ℂ))
    (amplifierFrequency_summable p hcop S lam q hX a)
    (amplifierFrequency_zero p hcop S lam hq X a)
  · rcases jacobiSym.trichotomy (-1) q with h | h | h <;> simp [h]
  · exact amplifierFrequency_neg p hcop S lam q X a

end Ostmann.QuadraticCenter

end

end OAI
