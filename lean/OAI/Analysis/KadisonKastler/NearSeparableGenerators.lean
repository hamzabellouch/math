import OAI.Analysis.KadisonKastler.SeparableAlgebraPair
import OAI.Analysis.KadisonKastler.SequentialConjugacyTests
import OAI.Analysis.KadisonKastler.PublishedKaplansky
import OAI.Analysis.KadisonKastler.SeparableTests

namespace OAI

/-! # Nearby separable C-star algebras generating the original pair

In a separable representation, the alternating construction can retain
countable strong generators of both original algebras. This supplies
the norm-separable algebras needed for simultaneous fiber representations.
-/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem generated_eq_of_strong_tests (M : VonNeumannAlgebra H)
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (hAM : A ≤ M.toStarSubalgebra)
    (s : StrongUnitBallTestSequence M) (hs : ∀ j, s.op j ∈ A) :
    generatedVonNeumannAlgebra A = M := by
  apply le_antisymm
  · intro T hT
    have h : Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))) ⊆
        Set.centralizer (Set.centralizer (M : Set (H →L[ℂ] H))) :=
      Set.centralizer_subset (Set.centralizer_subset hAM)
    have ht : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))) := by
      change T ∈ (generatedVonNeumannAlgebra A : Set (H →L[ℂ] H)) at hT
      rwa [generatedVonNeumannAlgebra_coe] at hT
    rw [M.centralizer_centralizer] at h
    exact h ht
  · apply (unitBall_subset_algebra_iff _ _).mp
    intro T hT
    change T ∈ generatedVonNeumannAlgebra A
    obtain ⟨S, hS, hlim⟩ := s.dense T hT
    have hm (j : ℕ) : S j ∈ generatedVonNeumannAlgebra A := by
      obtain ⟨k, hk⟩ := hS j
      rw [← hk]
      exact subset_generatedVonNeumannAlgebra A (hs k)
    simpa only [unitaryConj_one] using
      unitaryConj_mem_of_strong_tests (generatedVonNeumannAlgebra A) 1 S T hlim
        (fun j => by simpa only [unitaryConj_one] using hm j)

theorem exists_near_separable_generators [SeparableSpace H]
    (M N : VonNeumannAlgebra H) {g : ℝ} (hg : kkDistance M N < g) :
    ∃ A B : StarSubalgebra ℂ (H →L[ℂ] H),
      IsClosed (A : Set (H →L[ℂ] H)) ∧ IsClosed (B : Set (H →L[ℂ] H)) ∧
      IsSeparable (A : Set (H →L[ℂ] H)) ∧ IsSeparable (B : Set (H →L[ℂ] H)) ∧
      generatedVonNeumannAlgebra A = M ∧ generatedVonNeumannAlgebra B = N ∧
      Metric.hausdorffDist (starAlgebraBall A) (starAlgebraBall B) < g := by
  obtain ⟨s⟩ := exists_strongUnitBallTestSequence M
  obtain ⟨t⟩ := exists_strongUnitBallTestSequence N
  obtain ⟨A, B, hAc, hBc, hAs, hBs, hAM, hBN, hsA, htB, hd⟩ :=
    exists_near_separable_algebra_pair_countable M N (Set.range s.op) (Set.range t.op)
      (Set.countable_range _) (Set.countable_range _)
      (by rintro _ ⟨j, rfl⟩; exact (s.mem j).1)
      (by rintro _ ⟨j, rfl⟩; exact (t.mem j).1) hg
  exact ⟨A, B, hAc, hBc, hAs, hBs,
    generated_eq_of_strong_tests M A hAM s (fun j => hsA _ ⟨j, rfl⟩),
    generated_eq_of_strong_tests N B hBN t (fun j => htB _ ⟨j, rfl⟩), hd⟩

theorem exists_norm_dense_unitBall_sequence (E : Type*) [NormedAddCommGroup E]
    [SeparableSpace E] :
    ∃ s : ℕ → E, (∀ j, ‖s j‖ ≤ 1) ∧
      ∀ x : E, ‖x‖ ≤ 1 → ∀ ε : ℝ, 0 < ε → ∃ j, ‖x - s j‖ < ε := by
  let S := {x : E | ‖x‖ ≤ 1}
  have : Nonempty S := ⟨0, by simp [S]⟩
  obtain ⟨s, hs⟩ := exists_dense_seq (α := S)
  refine ⟨fun j => s j, fun j => (s j).property, ?_⟩
  intro x hx ε hε
  obtain ⟨j, hj⟩ := hs.exists_dist_lt ⟨x, hx⟩ hε
  exact ⟨j, by simpa only [Subtype.dist_eq, dist_eq_norm, norm_sub_rev] using hj⟩

theorem exists_closed_separable_common_superalgebra
    (A B : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : IsSeparable (A : Set (H →L[ℂ] H)))
    (hB : IsSeparable (B : Set (H →L[ℂ] H))) :
    ∃ C : StarSubalgebra ℂ (H →L[ℂ] H),
      IsClosed (C : Set (H →L[ℂ] H)) ∧ IsSeparable (C : Set (H →L[ℂ] H)) ∧
      A ≤ C ∧ B ≤ C := by
  obtain ⟨C, hCs, hAC, hBC⟩ := exists_separable_common_superalgebra A B hA hB
  exact ⟨C.topologicalClosure, StarSubalgebra.isClosed_topologicalClosure C, hCs.closure,
    hAC.trans C.le_topologicalClosure, hBC.trans C.le_topologicalClosure⟩

/-- The common separable algebra can be chosen inside any common ambient
von Neumann algebra, in particular inside the common central commutant. -/
theorem exists_closed_separable_common_superalgebra_in
    (A B : StarSubalgebra ℂ (H →L[ℂ] H)) (D : VonNeumannAlgebra H)
    (hA : IsSeparable (A : Set (H →L[ℂ] H)))
    (hB : IsSeparable (B : Set (H →L[ℂ] H)))
    (hAD : A ≤ D.toStarSubalgebra) (hBD : B ≤ D.toStarSubalgebra) :
    ∃ C : StarSubalgebra ℂ (H →L[ℂ] H),
      IsClosed (C : Set (H →L[ℂ] H)) ∧ IsSeparable (C : Set (H →L[ℂ] H)) ∧
      A ≤ C ∧ B ≤ C ∧ C ≤ D.toStarSubalgebra := by
  obtain ⟨C, hCc, hCs, hAC, hBC⟩ :=
    exists_closed_separable_common_superalgebra A B hA hB
  refine ⟨C ⊓ D.toStarSubalgebra, ?_, hCs.mono (fun _ h => h.1),
    (fun _ h => ⟨hAC h, hAD h⟩), (fun _ h => ⟨hBC h, hBD h⟩), inf_le_right⟩
  exact hCc.inter (isClosed_algebra D)

end

end KadisonKastler

end OAI
