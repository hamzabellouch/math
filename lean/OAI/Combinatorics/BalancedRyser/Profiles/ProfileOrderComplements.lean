import OAI.Combinatorics.BalancedRyser.Incidence.AffinePermutationExposure
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileMarkedOrders

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace Balanced.ProfileOrderComplements

universe u

open ConditionalOrderVariance UncoveredSampling ProfileMarkedOrders

section Finite
variable {α : Type*} [Fintype α] [DecidableEq α]

def future (I : Finset α) (i : α) : Finset α := Finset.univ.erase i \ I

@[simp] theorem current_not_future (I : Finset α) (i : α) : i ∉ future I i := by
  simp [future]

theorem exposed_image_eq (I : Finset α) (i x : α) (hi : i ∉ I)
    (σ : Equiv.Perm α) (hx : σ i = x) :
    Finset.univ.erase x \ (future I i).map σ.toEmbedding = I.map σ.toEmbedding := by
  ext y
  have hix : σ.symm x = i := by rw [← hx]; simp
  simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true,
    Finset.mem_map_equiv, future]
  constructor
  · rintro ⟨hy, h⟩
    by_contra hyI
    apply h
    refine ⟨?_, hyI⟩
    intro hsi
    apply hy
    calc y = σ (σ.symm y) := (σ.apply_symm_apply y).symm
         _ = x := by rw [hsi, hx]
  · intro hyI
    refine ⟨?_, ?_⟩
    · intro hy
      rw [hy, hix] at hyI
      exact hi hyI
    · exact fun h => h.2 hyI

theorem exposed_image_eq_complement (J : Finset α) (τ : Equiv.Perm α) :
    Finset.univ \ (Finset.univ \ J).map τ.toEmbedding = J.map τ.toEmbedding := by
  ext y
  simp [Finset.mem_map_equiv]

theorem future_card_add_one (I : Finset α) (i : α) (hi : i ∉ I) :
    (future I i).card + 1 = Fintype.card α - I.card := by
  have hI : I ⊆ Finset.univ.erase i := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨ne_of_mem_of_not_mem hx hi, Finset.mem_univ _⟩
  have hcard := Finset.card_le_card hI
  simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ] at hcard
  rw [future, Finset.card_sdiff_of_subset hI,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
  have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨i⟩
  omega

end Finite

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem targetFraction_eq_filter (U V : Finset (Line F)) (x : U)
    (S : Finset U) (T : Finset V) :
    targetFraction x.1 (populationLines U S) (populationLines V T) =
      (((linePoints x.1).filter (fun p =>
        (∀ m ∈ S, ¬ OnLine p m.1) ∧ (∀ m ∈ T, ¬ OnLine p m.1))).card : ℝ) /
        Fintype.card F := by
  unfold targetFraction
  apply congrArg (fun A : Finset (Point F) => (A.card : ℝ) / Fintype.card F)
  ext p
  simp only [Finset.mem_inter, uncoveredBy, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.forall_mem_union, populationLines, Finset.forall_mem_map]
  rfl

theorem conditional_targetMean_eq_remaining (U V : Finset (Line F))
    (I : Finset U) (J : Finset V) (i x : U) (hi : i ∉ I) :
    conditionalMean U V i x (targetStatistic U V I J x) =
      AffinePermutationExposure.targetOrderMean U V (future I i)
        (Finset.univ \ J) i x := by
  unfold conditionalMean AffinePermutationExposure.targetOrderMean
  rw [Finset.expect_product, Finset.expect_div]
  apply Finset.expect_congr rfl
  intro σ hσ
  rw [Finset.expect_div]
  apply Finset.expect_congr rfl
  intro τ _
  have hx : σ i = x := (Finset.mem_filter.mp hσ).2
  rw [exposed_image_eq I i x hi σ hx, exposed_image_eq_complement J τ]
  unfold targetStatistic
  rw [targetFraction_eq_filter]
  apply congrArg (fun A : Finset (Point F) => (A.card : ℝ) / Fintype.card F)
  ext p
  simp only [Finset.mem_filter]

theorem uniform_profile_pair_conditional_target_approximation (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)) (I : Finset D) (J : Finset C) (i x : D),
      N₀ ≤ D.card → N₀ ≤ C.card → IsProfilePair k D C → i ∉ I →
      |conditionalMean D C i x (targetStatistic D C I J x) -
        ∑' ij : ℕ × ℕ, lineProfile D C x.1 ij *
          ((((D.card - I.card : ℕ) : ℝ) / D.card) ^ (ij.1 - 1) *
            (((C.card - J.card : ℕ) : ℝ) / C.card) ^ ij.2)| < ε := by
  obtain ⟨N₀, hN₀, happ⟩ :=
    AffinePermutationExposure.uniform_profile_pair_order_target_approximation k hε
  refine ⟨N₀, hN₀, ?_⟩
  intro F hField hFin hDec D C I J i x hD hC hp hi
  rw [conditional_targetMean_eq_remaining D C I J i x hi]
  have h := happ F D C (future I i) (Finset.univ \ J) i x hD hC hp
    (current_not_future I i)
  simpa only [future_card_add_one I i hi, Finset.card_sdiff_of_subset
    (Finset.subset_univ J), Finset.card_univ, Fintype.card_coe] using h

theorem uniform_profile_pair_conditional_cover_target_approximation (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)) (I : Finset C) (J : Finset D) (i x : C),
      N₀ ≤ D.card → N₀ ≤ C.card → IsProfilePair k D C → i ∉ I →
      |conditionalMean C D i x (targetStatistic C D I J x) -
        ∑' ij : ℕ × ℕ, lineProfile D C x.1 ij *
          ((((D.card - J.card : ℕ) : ℝ) / D.card) ^ ij.1 *
            (((C.card - I.card : ℕ) : ℝ) / C.card) ^ (ij.2 - 1))| < ε := by
  obtain ⟨N₀, hN₀, happ⟩ :=
    AffinePermutationExposure.uniform_profile_pair_order_cover_target_approximation k hε
  refine ⟨N₀, hN₀, ?_⟩
  intro F hField hFin hDec D C I J i x hD hC hp hi
  rw [conditional_targetMean_eq_remaining C D I J i x hi]
  have h := happ F D C (future I i) (Finset.univ \ J) i x hD hC hp
    (current_not_future I i)
  simpa only [future_card_add_one I i hi, Finset.card_sdiff_of_subset
    (Finset.subset_univ J), Finset.card_univ, Fintype.card_coe] using h

end Balanced.ProfileOrderComplements

end

end OAI
