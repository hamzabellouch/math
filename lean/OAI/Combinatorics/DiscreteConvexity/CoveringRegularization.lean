import OAI.Combinatorics.DiscreteConvexity.CoveringBasic
import OAI.Combinatorics.DiscreteConvexity.CoveringBinomialBounds
import Mathlib.Combinatorics.Enumerative.DoubleCounting

namespace OAI

/-!
# Weighted-degree regularization

The initial family is the actual family of high weighted-degree subsets.
Double counting bounds its cost. An edge surviving this deletion has bounded
weighted degree at every one of its subsets. Grouping surviving edges by their
intersection with `B` gives the extension estimates used for pair sampling and
for residual tuples. No regularity property is assumed separately.
-/

namespace TalagrandDiscreteConvexity.Covering

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Count incidences between edges and subsets of cardinality at most `r`. -/
theorem incidence_count (H : Family V) (r : ℕ)
    (hH : ∀ e ∈ H, e.card = r) :
    (∑ I ∈ Finset.univ.filter (fun I : Finset V => I.card ≤ r),
      (H.filter (fun e => I ⊆ e)).card) = H.card * 2 ^ r := by
  classical
  let K : Finset (Finset V) := Finset.univ.filter (fun I => I.card ≤ r)
  have hbelow (e : Finset V) (he : e ∈ H) :
      K.filter (fun I => I ⊆ e) = e.powerset := by
    apply Finset.ext
    intro I
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset]
    constructor
    · exact fun h => h.2
    · intro hIe
      exact ⟨(Finset.card_le_card hIe).trans_eq (hH e he), hIe⟩
  calc
    (∑ I ∈ K, (H.filter (fun e => I ⊆ e)).card) =
        ∑ e ∈ H, (K.filter (fun I => I ⊆ e)).card := by
      exact Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (fun I e : Finset V => I ⊆ e)
    _ = ∑ _e ∈ H, 2 ^ r := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hbelow e he, Finset.card_powerset, hH e he]
    _ = H.card * 2 ^ r := by simp

omit [Fintype V] in
theorem weightedDegree_nonneg {H : Family V} {rho : ℝ} {r : ℕ} {I : Finset V}
    (hρ : 0 ≤ rho) : 0 ≤ weightedDegree H rho r I := by
  classical
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hρ _)

/-- The weighted incidence identity is valid even at `rho = 0`. -/
theorem weighted_incidence_count (H : Family V) (rho : ℝ) (r : ℕ)
    (hH : ∀ e ∈ H, e.card = r) :
    (∑ I ∈ Finset.univ.filter (fun I : Finset V => I.card ≤ r),
      weightedDegree H rho r I * rho ^ I.card) =
      (2 : ℝ) ^ r * (H.card : ℝ) * rho ^ r := by
  classical
  let K : Finset (Finset V) := Finset.univ.filter (fun I => I.card ≤ r)
  have hcast : (∑ I ∈ K, ((H.filter (fun e => I ⊆ e)).card : ℝ)) =
      (H.card : ℝ) * (2 : ℝ) ^ r := by
    simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      congrArg (fun n : ℕ => (n : ℝ)) (incidence_count H r hH)
  calc
    (∑ I ∈ K, weightedDegree H rho r I * rho ^ I.card) =
        (∑ I ∈ K, ((H.filter (fun e => I ⊆ e)).card : ℝ)) * rho ^ r := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro I hI
      have hIr : I.card ≤ r := (Finset.mem_filter.mp hI).2
      rw [weightedDegree, mul_assoc, ← pow_add, Nat.sub_add_cancel hIr]
    _ = ((H.card : ℝ) * (2 : ℝ) ^ r) * rho ^ r := by rw [hcast]
    _ = (2 : ℝ) ^ r * (H.card : ℝ) * rho ^ r := by
      rw [mul_comm (H.card : ℝ) ((2 : ℝ) ^ r)]

/-- The initial generators cost at most their weighted-incidence budget divided
by the high-degree threshold. -/
theorem initial_cost_le {H : Family V} {rho T : ℝ} {r : ℕ}
    (hρ : 0 ≤ rho) (hT : 0 < T) (hH : ∀ e ∈ H, e.card = r) :
    cost rho (initialFamily H rho r T) ≤
      T⁻¹ * (2 : ℝ) ^ r * (H.card : ℝ) * rho ^ r := by
  classical
  let K : Finset (Finset V) := Finset.univ.filter (fun I => I.card ≤ r)
  have hsub : initialFamily H rho r T ⊆ K := by
    intro I hI
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_initialFamily.mp hI).1⟩
  have hbudget : T * cost rho (initialFamily H rho r T) ≤
      (2 : ℝ) ^ r * (H.card : ℝ) * rho ^ r := by
    calc
      T * cost rho (initialFamily H rho r T) =
          ∑ I ∈ initialFamily H rho r T, T * rho ^ I.card := by
        rw [cost, Finset.mul_sum]
      _ ≤ ∑ I ∈ initialFamily H rho r T,
          weightedDegree H rho r I * rho ^ I.card := by
        apply Finset.sum_le_sum
        intro I hI
        exact mul_le_mul_of_nonneg_right (mem_initialFamily.mp hI).2.le
          (pow_nonneg hρ _)
      _ ≤ ∑ I ∈ K, weightedDegree H rho r I * rho ^ I.card := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro I _ _
        exact mul_nonneg (weightedDegree_nonneg hρ) (pow_nonneg hρ _)
      _ = (2 : ℝ) ^ r * (H.card : ℝ) * rho ^ r :=
        weighted_incidence_count H rho r hH
  calc
    cost rho (initialFamily H rho r T) ≤
        ((2 : ℝ) ^ r * (H.card : ℝ) * rho ^ r) / T := by
      apply (le_div_iff₀ hT).mpr
      simpa only [mul_comm] using hbudget
    _ = T⁻¹ * (2 : ℝ) ^ r * (H.card : ℝ) * rho ^ r := by
      rw [div_eq_mul_inv]
      ac_rfl

/-- Actual survival implies the weighted-degree bound at every subset of the
surviving edge. -/
theorem regular_weightedDegree_le {H : Family V} {rho T : ℝ} {r : ℕ}
    (hH : ∀ e ∈ H, e.card = r) {e I : Finset V}
    (he : e ∈ regularEdges H rho r T) (hIe : I ⊆ e) :
    weightedDegree H rho r I ≤ T := by
  have heH : e ∈ H := (mem_regularEdges.mp he).1
  have hIr : I.card ≤ r := (Finset.card_le_card hIe).trans_eq (hH e heH)
  apply le_of_not_gt
  intro hlarge
  exact (mem_regularEdges.mp he).2 I (mem_initialFamily.mpr ⟨hIr, hlarge⟩) hIe

/-- Each nonempty intersection class contributes at most `T`, and the empty
classes contribute zero. -/
private theorem regular_intersection_sum_le {H : Family V} {rho T : ℝ} {r : ℕ}
    (hρ : 0 ≤ rho) (hT : 0 ≤ T) (hH : ∀ e ∈ H, e.card = r)
    (B I : Finset V) :
    (∑ e ∈ (regularEdges H rho r T).filter (fun e => e ∩ B = I),
      rho ^ (e \ B).card) ≤ T := by
  classical
  let F := (regularEdges H rho r T).filter (fun e => e ∩ B = I)
  by_cases hne : F.Nonempty
  · obtain ⟨e₀, he₀⟩ := hne
    have he₀reg := (Finset.mem_filter.mp he₀).1
    have he₀I : e₀ ∩ B = I := (Finset.mem_filter.mp he₀).2
    have hIe₀ : I ⊆ e₀ := by rw [← he₀I]; exact Finset.inter_subset_left
    have hdegree := regular_weightedDegree_le hH he₀reg hIe₀
    have hsub : F ⊆ H.filter (fun e => I ⊆ e) := by
      intro e he
      obtain ⟨hereg, heI⟩ := Finset.mem_filter.mp he
      refine Finset.mem_filter.mpr ⟨(mem_regularEdges.mp hereg).1, ?_⟩
      rw [← heI]
      exact Finset.inter_subset_left
    have hcards : (F.card : ℝ) ≤ ((H.filter (fun e => I ⊆ e)).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    calc
      (∑ e ∈ F, rho ^ (e \ B).card) = (F.card : ℝ) * rho ^ (r - I.card) := by
        calc
          (∑ e ∈ F, rho ^ (e \ B).card) = ∑ _e ∈ F, rho ^ (r - I.card) := by
            apply Finset.sum_congr rfl
            intro e he
            obtain ⟨hereg, heI⟩ := Finset.mem_filter.mp he
            have hecard := hH e (mem_regularEdges.mp hereg).1
            have hpartition := Finset.card_sdiff_add_card_inter e B
            rw [heI, hecard] at hpartition
            have hdiff : (e \ B).card = r - I.card := by omega
            rw [hdiff]
          _ = (F.card : ℝ) * rho ^ (r - I.card) := by simp
      _ ≤ weightedDegree H rho r I :=
        mul_le_mul_of_nonneg_right hcards (pow_nonneg hρ _)
      _ ≤ T := hdegree
  · have hF : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change (∑ e ∈ F, rho ^ (e \ B).card) ≤ T
    rw [hF, Finset.sum_empty]
    exact hT

/-- Extension cost for actual regular edges, with the exact number of possible
intersections with `B`. -/
theorem regular_extension_le_card {H : Family V} {rho T : ℝ} {r : ℕ}
    (hρ : 0 ≤ rho) (hT : 0 ≤ T) (hH : ∀ e ∈ H, e.card = r) (B : Finset V) :
    (∑ e ∈ regularEdges H rho r T, rho ^ (e \ B).card) ≤
      T * ((B.powerset.filter (fun I => I.card ≤ r)).card : ℝ) := by
  classical
  let D := B.powerset.filter (fun I => I.card ≤ r)
  have hmap : ∀ e ∈ regularEdges H rho r T, e ∩ B ∈ D := by
    intro e he
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right, ?_⟩
    exact (Finset.card_le_card Finset.inter_subset_left).trans_eq
      (hH e (mem_regularEdges.mp he).1)
  calc
    (∑ e ∈ regularEdges H rho r T, rho ^ (e \ B).card) =
        ∑ I ∈ D, ∑ e ∈ (regularEdges H rho r T).filter (fun e => e ∩ B = I),
          rho ^ (e \ B).card :=
      (Finset.sum_fiberwise_of_maps_to hmap (fun e => rho ^ (e \ B).card)).symm
    _ ≤ ∑ _I ∈ D, T := by
      apply Finset.sum_le_sum
      intro I _
      exact regular_intersection_sum_le hρ hT hH B I
    _ = T * (D.card : ℝ) := by simp [mul_comm]

/-- The exact binomial extension bound from the covering lemma. -/
theorem regular_extension_le_choose {H : Family V} {rho T : ℝ} {r : ℕ}
    (hρ : 0 ≤ rho) (hT : 0 ≤ T) (hH : ∀ e ∈ H, e.card = r) (B : Finset V) :
    (∑ e ∈ regularEdges H rho r T, rho ^ (e \ B).card) ≤
      T * (∑ i ∈ Finset.range (r + 1), (Nat.choose B.card i : ℝ)) := by
  calc
    _ ≤ T * ((B.powerset.filter (fun I => I.card ≤ r)).card : ℝ) :=
      regular_extension_le_card hρ hT hH B
    _ = _ := by rw [card_subsets_card_le, Nat.cast_sum]

/-- The polynomial version used for extending a residual tuple prefix. -/
theorem regular_extension_le_pow {H : Family V} {rho T : ℝ} {r : ℕ}
    (hρ : 0 ≤ rho) (hT : 0 ≤ T) (hH : ∀ e ∈ H, e.card = r) (B : Finset V) :
    (∑ e ∈ regularEdges H rho r T, rho ^ (e \ B).card) ≤
      T * (1 + (B.card : ℝ)) ^ r := by
  have hc : ((B.powerset.filter (fun I => I.card ≤ r)).card : ℝ) ≤
      (((1 + B.card) ^ r : ℕ) : ℝ) :=
    Nat.cast_le.mpr (card_subsets_card_le_pow B r)
  have hc' : ((B.powerset.filter (fun I => I.card ≤ r)).card : ℝ) ≤
      (1 + (B.card : ℝ)) ^ r := by
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hc
  exact (regular_extension_le_card hρ hT hH B).trans (mul_le_mul_of_nonneg_left hc' hT)

/-- An `r`-element prefix gives the sharper factor `2^r`, used for pairs. -/
theorem regular_extension_le_two_pow {H : Family V} {rho T : ℝ} {r : ℕ}
    (hρ : 0 ≤ rho) (hT : 0 ≤ T) (hH : ∀ e ∈ H, e.card = r)
    {B : Finset V} (hB : B.card = r) :
    (∑ e ∈ regularEdges H rho r T, rho ^ (e \ B).card) ≤ (2 : ℝ) ^ r * T := by
  have h := regular_extension_le_choose hρ hT hH B
  rw [hB, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat] at h
  simpa only [mul_comm] using h

end TalagrandDiscreteConvexity.Covering

end OAI
