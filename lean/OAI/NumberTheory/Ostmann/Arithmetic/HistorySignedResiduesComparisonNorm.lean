import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulusBoundComparison
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesSums

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidues
open Construction HistoryCRTIntegration
open scoped BigOperators

lemma outside_prod_dvd_comparisonModulus {l : ℕ} (h k : History l) (outside : List ℕ) (n : ℕ) :
    outside.prod ∣ comparisonModulus h k outside n := by
  apply dvd_trans ?_ (crtModulus_dvd_comparisonModulus h k outside n)
  unfold crtModulus outsideModulus
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _

lemma outside_prod_le_comparisonModulus {l : ℕ} (h k : History l) (outside : List ℕ) (n : ℕ)
    (hp : 0<comparisonModulus h k outside n) : outside.prod≤comparisonModulus h k outside n :=
  Nat.le_of_dvd hp (outside_prod_dvd_comparisonModulus h k outside n)

theorem sum_norm_actual_prime_comparison_le {l : ℕ} (d : Decomposition)
    (V : ℕ → ℕ) (outside : List ℕ) (h k : History l) (n : ℕ)
    [NeZero (comparisonModulus h k outside n)] (hout : ∀q∈outside,q.Prime) :
    (∑u : Bool → (ZMod (comparisonModulus h k outside n))ˣ,
      ‖primeResidueTest (residueTransform d) V outside h k (comparisonModulus h k outside n)
        (pairModulus_dvd_comparisonModulus h k outside n) u‖) ≤
      (comparisonModulus h k outside n:ℝ)^(2+2^(l+1)) := by
  have hp : 0<comparisonModulus h k outside n := Nat.pos_of_ne_zero (NeZero.ne _)
  have ho : (outside.prod:ℝ)≤comparisonModulus h k outside n := by
    exact_mod_cast outside_prod_le_comparisonModulus h k outside n hp
  have ht : ((comparisonModulus h k outside n).totient:ℝ)≤comparisonModulus h k outside n := by
    exact_mod_cast Nat.totient_le (comparisonModulus h k outside n)
  refine (sum_norm_actual_primeResidueTest_le d V outside h k _
    (pairModulus_dvd_comparisonModulus h k outside n) hout).trans ?_
  simp only [pow_add]
  gcongr

theorem sum_norm_actual_mixed_comparison_le {l : ℕ} (d : Decomposition)
    (V : ℕ → ℕ) (outside : List ℕ) (h k : History l) (n : ℕ)
    [NeZero (comparisonModulus h k outside n)] (hout : ∀q∈outside,q.Prime) :
    (∑r : ZMod (comparisonModulus h k outside n),
      ∑u : Unit → (ZMod (comparisonModulus h k outside n))ˣ,
      ‖mixedResidueTest (residueTransform d) V outside h k (comparisonModulus h k outside n)
        (pairModulus_dvd_comparisonModulus h k outside n) r u‖) ≤
      (comparisonModulus h k outside n:ℝ)^(2+2^(l+1)) := by
  have hp : 0<comparisonModulus h k outside n := Nat.pos_of_ne_zero (NeZero.ne _)
  have ho : (outside.prod:ℝ)≤comparisonModulus h k outside n := by
    exact_mod_cast outside_prod_le_comparisonModulus h k outside n hp
  have ht : ((comparisonModulus h k outside n).totient:ℝ)≤comparisonModulus h k outside n := by
    exact_mod_cast Nat.totient_le (comparisonModulus h k outside n)
  refine (sum_norm_actual_mixedResidueTest_le d V outside h k _
    (pairModulus_dvd_comparisonModulus h k outside n) hout).trans ?_
  simp only [pow_add,pow_two]
  gcongr

end Ostmann.Arithmetic.HistorySignedResidues

end

end OAI
