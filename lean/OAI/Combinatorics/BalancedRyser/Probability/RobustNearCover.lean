import OAI.Combinatorics.BalancedRyser.Deletion.RobustDeletionAssembly
import OAI.Combinatorics.BalancedRyser.Deletion.UniformDeletionTolerance
import OAI.Combinatorics.BalancedRyser.Probability.NearCoverLimit

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Balanced
open scoped _root_.Balanced

universe u

theorem exists_uniform_poisson_occupancy_tolerance_le (k : ℕ) (K : ℝ)
    (hTV : ∀ τ : ℝ, 0 < τ → UniformDeletionVanishing.{u} k K
      (fun _ _ _ _ D => τ ≤ deletionMultiplicityTV k D.val))
    (hOcc : ∀ lam η : ℝ, 0 < lam → 0 < η → UniformDeletionVanishing.{u} k K
      (fun F _ _ _ D => η * (Fintype.card F : ℝ) ≤
        ((exceptionalOccupancyLines k lam D.val).card : ℝ)))
    (b : ℝ) (hb : 0 < b) :
    ∃ ε : ℕ → ℝ, (∀ q, 0 < ε q) ∧ (∀ q, ε q ≤ b) ∧ Antitone ε ∧
      Tendsto ε atTop (𝓝 0) ∧
      UniformDeletionVanishing.{u} k K
        (fun F _ _ _ D =>
          ε (Fintype.card F) ≤ deletionMultiplicityTV k D.val ∨
          ε (Fintype.card F) * (Fintype.card F : ℝ) ≤
            ((exceptionalOccupancyLines k (ε (Fintype.card F)) D.val).card : ℝ)) := by
  obtain ⟨ε, hpos, hanti, hlim, hbad⟩ := exists_uniform_deletion_tolerance k K
    (fun t F _ _ _ D =>
      min t b ≤ deletionMultiplicityTV k D.val ∨
      min t b * (Fintype.card F : ℝ) ≤
        ((exceptionalOccupancyLines k (min t b) D.val).card : ℝ)) (by
      intro t ht
      have hmin : 0 < min t b := lt_min ht hb
      exact uniformDeletionVanishing_or k K _ _
        (hTV _ hmin) (hOcc _ _ hmin hmin))
  refine ⟨fun q => min (ε q) b, (fun q => lt_min (hpos q) hb),
    (fun q => min_le_right _ _), ?_, ?_, hbad⟩
  · intro m n hmn
    exact min_le_min_right b (hanti hmn)
  · simpa only [min_eq_left hb.le] using hlim.min (tendsto_const_nhds (x := b))

theorem robust_nearCover_of_profileCounting
    (hcount : ProfileCountingResult.{u}) (k : ℕ) (hk : 1 ≤ k) (K : ℝ)
    (hTV : ∀ τ : ℝ, 0 < τ → UniformDeletionVanishing.{u} k K
      (fun _ _ _ _ D => τ ≤ deletionMultiplicityTV k D.val))
    (hOcc : ∀ lam η : ℝ, 0 < lam → 0 < η → UniformDeletionVanishing.{u} k K
      (fun F _ _ _ D => η * (Fintype.card F : ℝ) ≤
        ((exceptionalOccupancyLines k lam D.val).card : ℝ)))
    (δ : ℝ) (hδ : 0 < δ) :
    UniformDeletionVanishing.{u} k K (fun _ _ _ _ D => BadCoreCover δ D.val) := by
  obtain ⟨ε, hεpos, hεcap, _, hεlim, hbad⟩ :=
    exists_uniform_poisson_occupancy_tolerance_le k K hTV hOcc
      (Real.exp (-(k : ℝ)) / 4) (by positivity)
  let A : ProfileClass.{u} := NearCoverVisibility.NearCoverClass k δ ε
  have hvalid : ProfileClassValid k A := NearCoverVisibility.nearCoverClass_valid k δ ε
  have hgap : ProfileClassSizeGap (Real.exp (-(k : ℝ)) / 2) A :=
    NearCoverVisibility.nearCoverClass_sizeGap k δ ε hεcap
  have hvis : ProfileVisibleExcess A :=
    NearCoverVisibility.nearCoverClass_visibleExcess k δ hδ ε
      (fun q => (hεpos q).le) hεlim
  have hrestricted : UniformDeletionVanishing.{u} k K
      (fun F _ _ _ D => ∃ C, A F D.val C) :=
    uniformDeletionVanishing_of_profileCounting hcount k hk K A hvalid
      ⟨Real.exp (-(k : ℝ)) / 2, by positivity, hgap⟩ hvis
  apply uniformDeletionVanishing_mono k K _ _ _
    (uniformDeletionVanishing_or k K _ _ hrestricted hbad)
  intro F _ _ _ D hcover
  by_cases htv : ε (Fintype.card F) ≤ deletionMultiplicityTV k D.val
  · exact Or.inr (Or.inl htv)
  by_cases hocc : ε (Fintype.card F) * (Fintype.card F : ℝ) ≤
      ((exceptionalOccupancyLines k (ε (Fintype.card F)) D.val).card : ℝ)
  · exact Or.inr (Or.inr hocc)
  apply Or.inl
  exact NearCoverVisibility.nearCoverClass_of_badCoreCover k δ ε D.property hcover
    (le_of_lt (lt_of_not_ge htv)) (le_of_lt (lt_of_not_ge hocc))

end Balanced

end

end OAI
