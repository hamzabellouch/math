import OAI.Combinatorics.ExpectationThreshold.SelectorCountingEncodingBound
import OAI.Combinatorics.ExpectationThreshold.SelectorCommonWitness
import OAI.Combinatorics.ExpectationThreshold.SelectorProfile
import OAI.Combinatorics.ExpectationThreshold.SelectorEntropy
import OAI.Combinatorics.ExpectationThreshold.ProbabilityLikelihood
import OAI.Combinatorics.ExpectationThreshold.ColorArithmetic
import Mathlib.Tactic.Positivity

namespace OAI

/-!
# The actual contribution of one full selector profile

The common heavy sets are obtained separately for each occurring profile.
The entropy estimate removes their sizes before profiles are summed, so no
uniform choice of heavy sets across distinct profiles is required.
-/

noncomputable section
open scoped BigOperators

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A finite group with a fixed final coloring and full profile has the
claimed weighted contribution whenever its rows fit the actual heavy sets. -/
theorem profile_group_cost_le (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2)
    (G : Finset (Coloring α s)) (z : Coloring α s) (n : Profile s)
    (R : Fin s → Finset α)
    (hEarlier : ∀ a ∈ G, Earlier a z)
    (hprofile : ∀ a ∈ G, profile a z = n)
    (hrows : ∀ a ∈ G, ∀ i, movedRow a z i ⊆ R i)
    (hR : ∀ i, (R i).card ≤ 2 ^ (i.val + 1) * profileSize n) :
    (∑ a ∈ G, colorMass p s a * p ^ (changes a z).card) ≤
      colorMass p s z *
        (∏ i : Fin s, (3 / (64 : ℝ) ^ (i.val + 1)) ^ (rowCount n i)) *
        (∏ i : Fin s, ((wordCount (rowCount n i) (n i) : ℝ) *
          ∏ h : Color s, colorProb p s h ^ (n i h))) := by
  classical
  let C : ℝ := ∏ i : Fin s, ((R i).card.choose (rowCount n i) : ℝ)
  let W : ℝ := ∏ i : Fin s, (wordCount (rowCount n i) (n i) : ℝ)
  let L : ℝ := ∏ i : Fin s, (p / colorProb p s i.castSucc) ^ (rowCount n i)
  let Q : ℝ := ∏ i : Fin s, ∏ h : Color s, colorProb p s h ^ (n i h)
  let E : ℝ := ∏ i : Fin s, (3 * 4 ^ (i.val + 1) : ℝ) ^ (rowCount n i)
  let K : ℝ := ∏ i : Fin s, (3 / (64 : ℝ) ^ (i.val + 1)) ^ (rowCount n i)
  have hW : 0 ≤ W := Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
  have hL : 0 ≤ L := Finset.prod_nonneg fun i _ =>
    pow_nonneg (div_nonneg hp.le (colorProb_nonneg p s hp hs _)) _
  have hQ : 0 ≤ Q := Finset.prod_nonneg fun i _ =>
    Finset.prod_nonneg fun h _ => pow_nonneg (colorProb_nonneg p s hp hs h) _
  have hP : 0 ≤ colorMass p s z := colorMass_nonneg p s hp hs z
  have hcard : (G.card : ℝ) ≤ C * W := by
    have h := card_le_profile_encoding G z n R hEarlier hprofile hrows
    have hcast : (G.card : ℝ) ≤
        ∏ i : Fin s, ((R i).card.choose (rowCount n i) : ℝ) *
          (wordCount (rowCount n i) (n i) : ℝ) := by
      exact_mod_cast h
    simpa only [Finset.prod_mul_distrib] using hcast
  have hentropy : C ≤ E :=
    selector_entropy_bound s (fun i => (R i).card) (rowCount n) hR
  have hnormalize : E * L = K := by
    dsimp [E, L, K]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    exact profile_coefficient_pow_eq hp s i (rowCount n i)
  have hterm (a : Coloring α s) (ha : a ∈ G) :
      colorMass p s a * p ^ (changes a z).card = colorMass p s z * L * Q := by
    have h := colorMass_profile_likelihood p s hp hs a z (hEarlier a ha)
    rw [hprofile a ha] at h
    have hsize : (changes a z).card = profileSize n := by
      rw [← profileSize_profile, hprofile a ha]
    rw [hsize, mul_comm]
    simpa only [Finset.prod_mul_distrib, mul_assoc] using h
  calc
    (∑ a ∈ G, colorMass p s a * p ^ (changes a z).card) =
        (G.card : ℝ) * (colorMass p s z * L * Q) := by
      simp only [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C * W) * (colorMass p s z * L * Q) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg (mul_nonneg hP hL) hQ)
    _ = C * (W * (colorMass p s z * L * Q)) := by ring
    _ ≤ E * (W * (colorMass p s z * L * Q)) :=
      mul_le_mul_of_nonneg_right hentropy
        (mul_nonneg hW (mul_nonneg (mul_nonneg hP hL) hQ))
    _ = colorMass p s z * (E * L) * (W * Q) := by ring
    _ = colorMass p s z * K * (W * Q) := by rw [hnormalize]
    _ = _ := by
      dsimp [K, W, Q]
      rw [← Finset.prod_mul_distrib]

/-- The contribution of an actual selected profile. All reconstruction and
counting premises are discharged by the concrete selector construction. -/
theorem group_cost_le {F : Family α} (mu : MassFamily F)
    (p : ℝ) (s : ℕ) (hp : 0 < p) (hs : p * scaleSum s ≤ 1 / 2)
    (z : Coloring α s) (n : Profile s) :
    (∑ a ∈ groupOriginals mu z n, colorMass p s a * p ^ (changes a z).card) ≤
      colorMass p s z *
        (∏ i : Fin s, (3 / (64 : ℝ) ^ (i.val + 1)) ^ (rowCount n i)) *
        (∏ i : Fin s, ((wordCount (rowCount n i) (n i) : ℝ) *
          ∏ h : Color s, colorProb p s h ^ (n i h))) := by
  classical
  by_cases hne : (groupOriginals mu z n).Nonempty
  · obtain ⟨R, hR, hrows⟩ := exists_common_heavy_sets mu z n hne
    apply profile_group_cost_le p s hp hs (groupOriginals mu z n) z n R
    · intro a ha
      have h := (Finset.mem_filter.mp ha).2
      obtain ⟨H₀, hmin⟩ := h.2.1
      exact hmin.1.1.1
    · intro a ha
      exact (Finset.mem_filter.mp ha).2.2.2
    · exact hrows
    · exact hR
  · have hempty : groupOriginals mu z n = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty, Finset.sum_empty]
    exact mul_nonneg
      (mul_nonneg (colorMass_nonneg p s hp hs z)
        (Finset.prod_nonneg fun i _ => pow_nonneg (by positivity) _))
      (Finset.prod_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _)
        (Finset.prod_nonneg fun h _ => pow_nonneg (colorProb_nonneg p s hp hs h) _))

end TalagrandThreshold.Selector

end

end OAI
