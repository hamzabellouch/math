import OAI.NumberTheory.TotientAsymptotic.PPTTotientSquare
import OAI.NumberTheory.TotientAsymptotic.LargeSquareCount

namespace OAI

/-!
Prune squares in a selected bad preimage and in its totient.  Injectivity
of the chosen preimages, rather than of the totient values, preserves the
cardinality bound required by the PPT construction.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

theorem ppt_square_witness_count {N K : ℕ} (hN : 1 ≤ N) (hK : 1 ≤ K)
    (S : Finset ℕ) (F : ℕ → ℕ) (hinj : Set.InjOn F (S : Set ℕ))
    (hsize : ∀ n ∈ S, 0 < F n ∧ F n ≤ N)
    (hsq : ∀ n ∈ S, ∃ p : ℕ, p.Prime ∧ K < p ∧
      (p^2 ∣ F n ∨ p^2 ∣ (F n).totient)) :
    (S.card : ℝ) ≤ 2*(N : ℝ)/(K+1 : ℕ) +
      6*(N : ℝ)*(1+Real.log N)^2/(K : ℝ) := by
  classical
  let Q := S.image F
  let A := Q.filter (fun u => ∃ p : ℕ, K < p ∧ p^2 ∣ u)
  let B := Q.filter (fun u => ∃ p : ℕ, p.Prime ∧ K < p ∧ p^2 ∣ u.totient)
  have hsizeQ (u : ℕ) (hu : u ∈ Q) : 0 < u ∧ u ≤ N := by
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hu
    exact hsize n hn
  have hcover : Q ⊆ A ∪ B := by
    intro u hu
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hu
    obtain ⟨p, hp, hKp, hcase⟩ := hsq n hn
    rcases hcase with hcase | hcase
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hu,
        p, hKp, he ▸ hcase⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hu,
        p, hp, hKp, he ▸ hcase⟩)
  have hA : (A.card : ℝ) ≤ 2*(N : ℝ)/(K+1 : ℕ) := by
    apply large_square_count N K A
    intro u hu
    have hh := Finset.mem_filter.mp hu
    exact ⟨(hsizeQ u hh.1).1, (hsizeQ u hh.1).2, hh.2⟩
  have hB : (B.card : ℝ) ≤ 6*(N : ℝ)*(1+Real.log N)^2/(K : ℝ) := by
    apply ppt_large_totient_square_count hN hK B
    intro u hu
    have hh := Finset.mem_filter.mp hu
    exact ⟨(hsizeQ u hh.1).1, (hsizeQ u hh.1).2, hh.2⟩
  have hcard : (S.card : ℝ) ≤ (A.card : ℝ)+(B.card : ℝ) := by
    rw [← Finset.card_image_of_injOn hinj]
    exact_mod_cast (Finset.card_le_card hcover).trans (Finset.card_union_le A B)
  exact hcard.trans (add_le_add hA hB)

/-- Multiplication by a seed with no prime above the cutoff preserves the
squarefree-above-cutoff property.  This supplies the actual left product
condition after pruning squares from the candidate totient. -/
lemma ppt_seed_squarefreeAbove {d m : ℕ} {Z : ℝ} (hd : d ≠ 0)
    (hseed : (largestPrimeFactor d : ℝ) ≤ Z) (hsq : SquarefreeAbove m Z) :
    SquarefreeAbove (d*m) Z := by
  intro p hp hpZ hpm
  have hpd : ¬p ∣ d := by
    intro hdiv
    have hmem : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hdiv, hd⟩
    have hle : p ≤ largestPrimeFactor d :=
      (Finset.le_sup (f := id) hmem).trans (le_max_right _ _)
    exact (not_lt_of_ge ((Nat.cast_le.mpr hle).trans hseed)) hpZ
  exact hsq p hp hpZ (hp.prime.pow_dvd_of_dvd_mul_left 2 hpd hpm)

end TotientAsymptotic

end

end OAI
