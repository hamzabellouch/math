import OAI.Analysis.KadisonKastler.SeparableAlgebraPair
import OAI.Analysis.KadisonKastler.SeparableReducingSpace

namespace OAI

/-! # Common separable reducing spaces for nearby test algebras

The countable dense generators of both algebras generate one separable
ambient C*-algebra. Its finite-vector orbit supplies the common reducing
space, including when the original Hilbert space is not separable.
-/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_separable_common_superalgebra
    (A B : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : IsSeparable (A : Set (H →L[ℂ] H)))
    (hB : IsSeparable (B : Set (H →L[ℂ] H))) :
    ∃ C : StarSubalgebra ℂ (H →L[ℂ] H),
      IsSeparable (C : Set (H →L[ℂ] H)) ∧ A ≤ C ∧ B ≤ C := by
  obtain ⟨s, hsA, hsc, hAs⟩ := hA.exists_countable_dense_subset
  obtain ⟨t, htB, htc, hBt⟩ := hB.exists_countable_dense_subset
  refine ⟨cstarHull (s ∪ t), isSeparable_cstarHull (hsc.union htc), ?_, ?_⟩
  · exact hAs.trans (closure_minimal
      (Set.subset_union_left.trans (subset_cstarHull (s ∪ t)))
      (StarSubalgebra.isClosed_topologicalClosure _))
  · exact hBt.trans (closure_minimal
      (Set.subset_union_right.trans (subset_cstarHull (s ∪ t)))
      (StarSubalgebra.isClosed_topologicalClosure _))

/-- One closed separable subspace reduces both algebras and contains
the finite prescribed vectors. -/
theorem exists_common_separable_reducingSpace
    (A B : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : IsSeparable (A : Set (H →L[ℂ] H)))
    (hB : IsSeparable (B : Set (H →L[ℂ] H))) (V : Finset H) :
    ∃ K : Submodule ℂ H, IsClosed (K : Set H) ∧ SeparableSpace K ∧
      (∀ v ∈ V, v ∈ K) ∧
      (∀ a : A, ∀ x ∈ K, (a : H →L[ℂ] H) x ∈ K) ∧
      (∀ b : B, ∀ x ∈ K, (b : H →L[ℂ] H) x ∈ K) := by
  obtain ⟨C, hCsep, hAC, hBC⟩ := exists_separable_common_superalgebra A B hA hB
  let : SeparableSpace C := hCsep.separableSpace
  obtain ⟨K, hKclosed, hKsep, hVK, hCK⟩ := exists_separable_reducingSpace C V
  exact ⟨K, hKclosed, hKsep, hVK,
    fun a x hx => hCK ⟨a.val, hAC a.property⟩ x hx,
    fun b x hx => hCK ⟨b.val, hBC b.property⟩ x hx⟩

/-- The algebra and reducing-space portions of the separable tests lemma. -/
theorem exists_near_separable_tests (M N : VonNeumannAlgebra H)
    (E F : Finset (H →L[ℂ] H)) (V : Finset H)
    (hE : ∀ x ∈ E, x ∈ M) (hF : ∀ x ∈ F, x ∈ N)
    {g : ℝ} (hg : kkDistance M N < g) :
    ∃ (A B : StarSubalgebra ℂ (H →L[ℂ] H)) (K : Submodule ℂ H),
      IsClosed (A : Set (H →L[ℂ] H)) ∧ IsClosed (B : Set (H →L[ℂ] H)) ∧
      IsSeparable (A : Set (H →L[ℂ] H)) ∧ IsSeparable (B : Set (H →L[ℂ] H)) ∧
      A ≤ M.toStarSubalgebra ∧ B ≤ N.toStarSubalgebra ∧
      (∀ x ∈ E, x ∈ A) ∧ (∀ x ∈ F, x ∈ B) ∧
      Metric.hausdorffDist (starAlgebraBall A) (starAlgebraBall B) < g ∧
      IsClosed (K : Set H) ∧ SeparableSpace K ∧ (∀ v ∈ V, v ∈ K) ∧
      (∀ a : A, ∀ x ∈ K, (a : H →L[ℂ] H) x ∈ K) ∧
      (∀ b : B, ∀ x ∈ K, (b : H →L[ℂ] H) x ∈ K) := by
  obtain ⟨A, B, hAc, hBc, hAs, hBs, hAM, hBN, hEA, hFB, hdist⟩ :=
    exists_near_separable_algebra_pair M N E F hE hF hg
  obtain ⟨K, hKc, hKs, hVK, hAK, hBK⟩ :=
    exists_common_separable_reducingSpace A B hAs hBs V
  exact ⟨A, B, K, hAc, hBc, hAs, hBs, hAM, hBN, hEA, hFB, hdist,
    hKc, hKs, hVK, hAK, hBK⟩

end

end KadisonKastler

end OAI
