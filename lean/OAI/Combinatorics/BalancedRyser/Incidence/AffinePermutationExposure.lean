import OAI.Combinatorics.BalancedRyser.Incidence.AffineProfileExposure
import OAI.Combinatorics.BalancedRyser.Probability.PermutationExposureMean

namespace OAI

namespace Balanced.AffinePermutationExposure

universe u

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem subtype_filter_card {α : Type*} [DecidableEq α]
    (U : Finset α) (P : α → Prop) :
    ((Finset.univ : Finset U).filter (fun x => P x.1)).card =
      (U.filter P).card := by
  classical
  apply Finset.card_bij (fun x _ => x.1)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨x.2, (Finset.mem_filter.mp hx).2⟩
  · intro x _ y _ hxy
    exact Subtype.ext hxy
  · intro y hy
    refine ⟨⟨y, (Finset.mem_filter.mp hy).1⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in

theorem erased_subtype_incidence_card
    (D : Finset (Line F)) (l : D) (p : Point F) (hp : OnLine p l.1) :
    (((Finset.univ : Finset D).erase l).filter (fun m => OnLine p m.1)).card =
      lineMultiplicity D p - 1 := by
  rw [Finset.filter_erase, Finset.card_erase_of_mem
    (Finset.mem_filter.mpr ⟨Finset.mem_univ l, hp⟩)]
  apply congrArg (fun n : ℕ => n - 1)
  unfold lineMultiplicity
  apply Finset.card_bij (fun m _ => m.1)
  · intro m hm
    exact Finset.mem_filter.mpr ⟨m.2, (Finset.mem_filter.mp hm).2⟩
  · intro m _ n _ hmn
    exact Subtype.ext hmn
  · intro m hm
    refine ⟨⟨m, (Finset.mem_filter.mp hm).1⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hm).2⟩

def targetOrderMean (D C : Finset (Line F))
    (I : Finset D) (J : Finset C) (i l : D) : ℝ :=
  (𝔼 σ ∈ Finset.univ.filter (fun σ : Equiv.Perm D => σ i = l),
    𝔼 τ : Equiv.Perm C,
      (((linePoints l.1).filter (fun p =>
        (∀ m ∈ (Finset.univ.erase l) \ I.map σ.toEmbedding, ¬ OnLine p m.1) ∧
        (∀ m ∈ Finset.univ \ J.map τ.toEmbedding, ¬ OnLine p m.1))).card : ℝ)) /
    (Fintype.card F : ℝ)

omit [Field F] [Fintype F] in

theorem remaining_count_le (D : Finset (Line F)) (I : Finset D)
    (i : D) (hi : i ∉ I) : I.card + 1 ≤ D.card := by
  have hsub : I ⊆ (Finset.univ : Finset D).erase i := by
    intro a ha
    exact Finset.mem_erase.mpr ⟨ne_of_mem_of_not_mem ha hi, Finset.mem_univ _⟩
  have h := Finset.card_le_card hsub
  simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_coe] at h
  have hD : 0 < D.card := Finset.card_pos.mpr ⟨i.1, i.2⟩
  omega

theorem targetOrderMean_eq_targetExposureMean
    (D C : Finset (Line F)) (I : Finset D) (J : Finset C)
    (i l : D) (hi : i ∉ I) :
    targetOrderMean D C I J i l =
      AffineProfileExposure.targetExposureMean D C l.1 (I.card + 1) J.card := by
  have hd := remaining_count_le D I i hi
  have hc : J.card ≤ C.card := by
    simpa only [Finset.card_univ, Fintype.card_coe] using
      Finset.card_le_card (Finset.subset_univ J)
  unfold targetOrderMean
  convert (congrArg (fun z : ℝ => z / (Fintype.card F : ℝ))
    (permutation_target_uncovered_mean I J i l hi (linePoints l.1)
      (fun p m => OnLine p m.1) (fun p m => OnLine p m.1))).trans ?_ using 1
  · apply congrArg (fun z : ℝ => z / (Fintype.card F : ℝ))
    apply Finset.expect_congr rfl
    intro σ hσ
    apply Finset.expect_congr rfl
    intro τ hτ
    apply congrArg (fun S : Finset (Point F) => (S.card : ℝ))
    ext p
    simp only [Finset.mem_filter]
  · rw [AffineProfileExposure.targetExposureMean_eq D C l.1 (I.card + 1) J.card
      l.2 hd hc]
    apply congrArg (fun z : ℝ => z / (Fintype.card F : ℝ))
    apply Finset.sum_congr rfl
    intro p hp
    have hon : OnLine p l.1 := (Finset.mem_filter.mp hp).2
    simp only [Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ,
      Fintype.card_coe, Nat.add_sub_cancel]
    congr 4
    · convert erased_subtype_incidence_card D l p hon using 1
      apply congrArg Finset.card
      ext m
      simp only [Finset.mem_filter]
    · convert erased_subtype_incidence_card D l p hon using 1
      apply congrArg Finset.card
      ext m
      simp only [Finset.mem_filter]
    · convert subtype_filter_card C (fun m => OnLine p m) using 1
      apply congrArg Finset.card
      ext m
      simp only [Finset.mem_filter]
    · convert subtype_filter_card C (fun m => OnLine p m) using 1
      apply congrArg Finset.card
      ext m
      simp only [Finset.mem_filter]

theorem uniform_profile_pair_order_target_approximation (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)) (I : Finset D) (J : Finset C) (i l : D),
      N₀ ≤ D.card → N₀ ≤ C.card → IsProfilePair k D C → i ∉ I →
      |targetOrderMean D C I J i l -
        ∑' ij : ℕ × ℕ, lineProfile D C l.1 ij *
          ((((I.card + 1 : ℕ) : ℝ) / D.card) ^ (ij.1 - 1) *
            ((J.card : ℝ) / C.card) ^ ij.2)| < ε := by
  obtain ⟨N₀, hN₀, happrox⟩ :=
    AffineProfileExposure.uniform_profile_pair_target_approximation k hε
  refine ⟨N₀, hN₀, ?_⟩
  intro F hField hFin hDec D C I J i l hD hC hpair hi
  rw [targetOrderMean_eq_targetExposureMean D C I J i l hi,
    ← AffineProfileExposure.targetPowerMean_eq_profile_transform]
  apply happrox F D C l.1 (I.card + 1) J.card hD hC hpair l.2
    (remaining_count_le D I i hi)
  simpa only [Finset.card_univ, Fintype.card_coe] using
    Finset.card_le_card (Finset.subset_univ J)

theorem uniform_deletion_order_target_approximation (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D : Finset (Line F)) (I : Finset D) (i l : D),
      N₀ ≤ D.card → IsDeletionSet k D → i ∉ I →
      |targetOrderMean D ∅ I ∅ i l -
        AffineProfileExposure.targetPowerMean D ∅ l.1 (I.card + 1) 0| < ε := by
  obtain ⟨N₀, hN₀, happrox⟩ :=
    AffineProfileExposure.uniform_deletion_target_approximation k hε
  refine ⟨N₀, hN₀, ?_⟩
  intro F hField hFin hDec D I i l hD hDel hi
  rw [targetOrderMean_eq_targetExposureMean D ∅ I ∅ i l hi, Finset.card_empty]
  exact happrox F D l.1 (I.card + 1) hD hDel l.2 (remaining_count_le D I i hi)

theorem coverTargetPowerMean_eq_profile_transform
    (D C : Finset (Line F)) (l : Line F) (d c : ℕ) :
    AffineProfileExposure.targetPowerMean C D l c d =
      ∑' ij : ℕ × ℕ, lineProfile D C l ij *
        (((d : ℝ) / D.card) ^ ij.1 * ((c : ℝ) / C.card) ^ (ij.2 - 1)) := by
  have h := lineProfile_weighted_hasSum D C l (fun ij =>
    ((d : ℝ) / D.card) ^ ij.1 * ((c : ℝ) / C.card) ^ (ij.2 - 1))
  calc
    _ = (∑ p ∈ linePoints l,
        ((d : ℝ) / D.card) ^ lineMultiplicity D p *
          ((c : ℝ) / C.card) ^ (lineMultiplicity C p - 1)) /
            (Fintype.card F : ℝ) := by
      unfold AffineProfileExposure.targetPowerMean
      apply congrArg (fun z : ℝ => z / (Fintype.card F : ℝ))
      apply Finset.sum_congr rfl
      intro p hp
      exact mul_comm _ _
    _ = _ := h.tsum_eq.symm.trans (tsum_congr (fun ij => mul_comm _ _))

theorem uniform_profile_pair_order_cover_target_approximation (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)) (I : Finset C) (J : Finset D) (i l : C),
      N₀ ≤ D.card → N₀ ≤ C.card → IsProfilePair k D C → i ∉ I →
      |targetOrderMean C D I J i l -
        ∑' ij : ℕ × ℕ, lineProfile D C l.1 ij *
          (((J.card : ℝ) / D.card) ^ ij.1 *
            (((I.card + 1 : ℕ) : ℝ) / C.card) ^ (ij.2 - 1))| < ε := by
  obtain ⟨N₀, hN₀, happrox⟩ :=
    AffineProfileExposure.uniform_profile_pair_cover_target_approximation k hε
  refine ⟨N₀, hN₀, ?_⟩
  intro F hField hFin hDec D C I J i l hD hC hpair hi
  rw [targetOrderMean_eq_targetExposureMean C D I J i l hi,
    ← coverTargetPowerMean_eq_profile_transform]
  apply happrox F D C l.1 J.card (I.card + 1) hD hC hpair l.2
  · simpa only [Finset.card_univ, Fintype.card_coe] using
      Finset.card_le_card (Finset.subset_univ J)
  · exact remaining_count_le C I i hi

end
end Balanced.AffinePermutationExposure

end OAI
