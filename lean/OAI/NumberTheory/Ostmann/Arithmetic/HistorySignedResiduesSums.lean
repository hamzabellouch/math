import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesBounds

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidues
open Construction
open scoped BigOperators

theorem sum_norm_actual_primeResidueTest_le {l : ℕ} (d : Decomposition)
    (V : ℕ → ℕ) (outside : List ℕ) (h k : History l) (M : ℕ) [NeZero M]
    (hd : pairModulus h k outside ∣ M) (hout : ∀ q ∈ outside, q.Prime) :
    (∑ u : Bool → (ZMod M)ˣ, ‖primeResidueTest (residueTransform d) V outside h k M hd u‖) ≤
      (M.totient : ℝ)^2 * (outside.prod : ℝ)^(2^(l+1)) := by
  calc
    _ ≤ ∑ _u : Bool → (ZMod M)ˣ, (outside.prod : ℝ)^(2^(l+1)) :=
      Finset.sum_le_sum (fun u _ => norm_actual_liftedResidueTest_le d V outside h k M hd hout _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_fun, Fintype.card_bool, ZMod.card_units_eq_totient, Nat.cast_pow]

theorem sum_norm_actual_mixedResidueTest_le {l : ℕ} (d : Decomposition)
    (V : ℕ → ℕ) (outside : List ℕ) (h k : History l) (M : ℕ) [NeZero M]
    (hd : pairModulus h k outside ∣ M) (hout : ∀ q ∈ outside, q.Prime) :
    (∑ r : ZMod M, ∑ u : Unit → (ZMod M)ˣ,
      ‖mixedResidueTest (residueTransform d) V outside h k M hd r u‖) ≤
      (M : ℝ) * (M.totient : ℝ) * (outside.prod : ℝ)^(2^(l+1)) := by
  calc
    _ ≤ ∑ _r : ZMod M, ∑ _u : Unit → (ZMod M)ˣ, (outside.prod : ℝ)^(2^(l+1)) := by
      apply Finset.sum_le_sum
      intro r _
      exact Finset.sum_le_sum (fun u _ => norm_actual_liftedResidueTest_le d V outside h k M hd hout _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
        Fintype.card_unit, pow_one, ZMod.card_units_eq_totient, ZMod.card]
      ring

end Ostmann.Arithmetic.HistorySignedResidues

end

end OAI
