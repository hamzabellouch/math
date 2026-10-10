import Mathlib
import OAI.Combinatorics.IndependentSets.Encoding.Normalizer
import OAI.Combinatorics.IndependentSets.Geometry.Uniform

namespace OAI

namespace LargeIndependentSets.Coefficient
open scoped BigOperators Classical

noncomputable def law (m : ℕ) {ρ : ℚ} (hρ : 0 ≤ ρ) : RationalLaw (Fin (m+1)) where
  weight j := ρ^j.val / ∑ k : Fin (m+1), ρ^k.val
  nonneg j := div_nonneg (pow_nonneg hρ _) (Finset.sum_nonneg (fun k _ => pow_nonneg hρ _))
  total := by
    have hp : 0 < ∑ k : Fin (m+1), ρ^k.val := by
      have h := Finset.single_le_sum (f:=fun k : Fin (m+1) => ρ^k.val)
        (fun j _ => pow_nonneg hρ _) (Finset.mem_univ (0 : Fin (m+1)))
      have h1 : (1:ℚ) ≤ ∑ k : Fin (m+1), ρ^k.val := by simpa using h
      exact lt_of_lt_of_le (by norm_num : (0:ℚ)<1) h1
    rw [← Finset.sum_div, div_self hp.ne']

lemma law_real (m : ℕ) {ρ : ℚ} (hρ : 0 ≤ ρ) (j : Fin (m+1)) :
    ((law m hρ).weight j : ℝ) = levelMass m ρ j := by
  simp [law, levelMass, normalizer]

lemma pi_law_real {I : Type*} [Fintype I] [DecidableEq I] (m : ℕ) {ρ : ℚ} (hρ : 0 ≤ ρ)
    (t : I → Fin (m+1)) :
    ((RationalLaw.pi (fun _ : I => law m hρ)).weight t : ℝ) = mass m ρ t := by
  simp only [RationalLaw.pi, Rat.cast_prod, law_real, mass]

end LargeIndependentSets.Coefficient

end OAI
