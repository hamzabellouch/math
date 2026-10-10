import OAI.Combinatorics.BalancedRyser.Deletion.DeletionAsymptotics
import OAI.Combinatorics.BalancedRyser.Deletion.DeletionVisibility
import OAI.Combinatorics.BalancedRyser.Profiles.Profile

namespace OAI

namespace Balanced
open scoped _root_.Balanced

universe u

theorem uniformDeletionVanishing_of_profileCounting
    (hcounting : ProfileCountingResult.{u})
    (k : ℕ) (hk : 1 ≤ k) (K : ℝ) (A : ProfileClass.{u})
    (hvalid : ProfileClassValid k A)
    (hgap : ∃ a : ℝ, 0 < a ∧ ProfileClassSizeGap a A)
    (hvisible : ProfileVisibleExcess A) :
    UniformDeletionVanishing.{u} k K
      (fun F _ _ _ D => ∃ C : Finset (Line F), A F D.val C) := by
  classical
  obtain ⟨b, hb, N, hN⟩ := hcounting k hk A hvalid hgap hvisible
  apply uniformDeletionVanishing_of_superexponential_count k K _ hb
  refine ⟨N, ?_⟩
  intro F _ _ _ hn hkq
  have h := hN F hn hkq
  unfold uniformProfileWitnessProbability at h
  unfold deletionEventCard
  convert h using 1
  congr 3
  apply Finset.filter_congr_decidable

def multiplicityFailureClass (k : ℕ) (τ : ℝ) : ProfileClass.{u} :=
  fun _ _ _ _ D C => IsDeletionSet k D ∧ C = ∅ ∧ τ ≤ deletionMultiplicityTV k D

theorem multiplicityFailureClass_valid (k : ℕ) (τ : ℝ) :
    ProfileClassValid k (multiplicityFailureClass.{u} k τ) := by
  intro F _ _ _ D C h
  rcases h with ⟨hD, rfl, hτ⟩
  exact ⟨hD, by simp, by simp⟩

theorem multiplicityFailureClass_sizeGap (k : ℕ) (τ : ℝ) :
    ProfileClassSizeGap 1 (multiplicityFailureClass.{u} k τ) := by
  intro F _ _ _ D C h
  exact Or.inl (by rw [h.2.1]; simp)

theorem multiplicityFailureClass_witness_iff
    (k : ℕ) (τ : ℝ) (F : Type u) [Field F] [Fintype F] [DecidableEq F]
    (D : DeletionSet F k) :
    (∃ C : Finset (Line F), multiplicityFailureClass k τ F D.val C) ↔
      τ ≤ deletionMultiplicityTV k D.val := by
  constructor
  · rintro ⟨C, hD, hC, hτ⟩
    exact hτ
  · intro hτ
    exact ⟨∅, D.property, rfl, hτ⟩

theorem multiplicityVanishing_of_profileCounting
    (hcounting : ProfileCountingResult.{u})
    (k : ℕ) (hk : 1 ≤ k) (K τ : ℝ)
    (hvisible : ProfileVisibleExcess (multiplicityFailureClass.{u} k τ)) :
    UniformDeletionVanishing.{u} k K
      (fun _ _ _ _ D => τ ≤ deletionMultiplicityTV k D.val) := by
  have hclass := uniformDeletionVanishing_of_profileCounting hcounting k hk K
    (multiplicityFailureClass k τ) (multiplicityFailureClass_valid k τ)
    ⟨1, by norm_num, multiplicityFailureClass_sizeGap k τ⟩ hvisible
  apply uniformDeletionVanishing_mono k K _ _ _ hclass
  intro F _ _ _ D hD
  exact (multiplicityFailureClass_witness_iff k τ F D).2 hD

end Balanced

end OAI
