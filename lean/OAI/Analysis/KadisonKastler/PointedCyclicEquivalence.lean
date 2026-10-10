import OAI.Analysis.KadisonKastler.PointedWordMoments
import OAI.Analysis.KadisonKastler.CyclicGeneratorSpan
import OAI.Analysis.KadisonKastler.SpatialAssociatorTransport

namespace OAI

/-! # Unitary reindexing of pointed matrix products

Matching finite-site moments identify the dense spans of all word
vectors. The resulting Hilbert isometry intertwines every site and
therefore the concrete von Neumann algebras they generate.
-/

namespace KadisonKastler

noncomputable section

namespace PointedMatrixSites

variable {I J H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  {Ω : H} {ξ : K} {ν : I → ℝ} {η : J → ℝ}

def siteGenerator (S : PointedMatrixSites M Ω ν) (a : MatrixSiteLetter I) : H →L[ℂ] H :=
  (S.site a.1).entry a.2.1 a.2.2

theorem generates_siteGenerator (S : PointedMatrixSites M Ω ν) :
    M = generatedVonNeumannAlgebra (StarAlgebra.adjoin ℂ (Set.range S.siteGenerator)) := by
  apply S.generates.trans
  apply congrArg generatedVonNeumannAlgebra
  apply le_antisymm
  · apply iSup_le
    intro i
    apply ((S.site i).algebra_le_iff _).mpr
    intro a b
    exact StarAlgebra.subset_adjoin ℂ _ ⟨(i, a, b), rfl⟩
  · apply StarAlgebra.adjoin_le
    rintro _ ⟨⟨i, a, b⟩, rfl⟩
    exact (le_iSup (fun i => (S.site i).algebra) i) ((S.site i).entry_mem a b)

/-- All finite word vectors have dense linear span. -/
theorem wordSpan_dense (S : PointedMatrixSites M Ω ν) :
    DenseRange (Finsupp.linearCombination ℂ S.wordVector) := by
  apply denseRange_linearCombination_of_cyclic_generators M Ω S.siteGenerator S.wordVector
    S.generates_siteGenerator S.cyclic
  · rintro ⟨i, a, b⟩
    exact ⟨(i, b, a), (S.site i).star_entry a b |>.symm⟩
  · exact ⟨Finsupp.single [] 1, by simp⟩
  · intro a w
    exact ⟨Finsupp.single (a :: w) 1, by simp [siteGenerator]⟩

private theorem reindex_symm (e : I ≃ J) (w : MatrixSiteWord J) :
    MatrixSiteWord.reindex e (MatrixSiteWord.reindex e.symm w) = w := by
  simp only [MatrixSiteWord.reindex, List.map_map, Function.comp_def, e.apply_symm_apply]
  change w.map id = w
  exact List.map_id w

private theorem reindexed_wordSpan_dense (T : PointedMatrixSites N ξ η) (e : I ≃ J) :
    DenseRange (Finsupp.linearCombination ℂ
      (fun w : MatrixSiteWord I => T.wordVector (MatrixSiteWord.reindex e w))) := by
  have hr : Set.range (fun w : MatrixSiteWord I =>
      T.wordVector (MatrixSiteWord.reindex e w)) = Set.range T.wordVector := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨MatrixSiteWord.reindex e w, rfl⟩
    · rintro ⟨w, rfl⟩
      exact ⟨MatrixSiteWord.reindex e.symm w, by dsimp only; rw [reindex_symm]⟩
  change Dense ((LinearMap.range (Finsupp.linearCombination ℂ
    (fun w : MatrixSiteWord I => T.wordVector (MatrixSiteWord.reindex e w)))) : Set K)
  rw [Finsupp.range_linearCombination, hr, ← Finsupp.range_linearCombination]
  exact T.wordSpan_dense

/-- The actual Hilbert-space equivalence determined by all finite words. -/
def reindexEquivalence (S : PointedMatrixSites M Ω ν) (T : PointedMatrixSites N ξ η)
    (e : I ≃ J) (hweight : ∀ i, η (e i) = ν i) : H ≃ₗᵢ[ℂ] K :=
  cyclicGramEquivalence S.wordVector
    (fun w => T.wordVector (MatrixSiteWord.reindex e w))
    S.wordSpan_dense (reindexed_wordSpan_dense T e)
    (S.word_inner_eq_of_reindex T e hweight)

@[simp] theorem reindexEquivalence_word (S : PointedMatrixSites M Ω ν)
    (T : PointedMatrixSites N ξ η) (e : I ≃ J) (hweight : ∀ i, η (e i) = ν i)
    (w : MatrixSiteWord I) :
    S.reindexEquivalence T e hweight (S.wordVector w) =
      T.wordVector (MatrixSiteWord.reindex e w) :=
  cyclicGramEquivalence_apply _ _ _ _ _ w

theorem reindexEquivalence_vector (S : PointedMatrixSites M Ω ν)
    (T : PointedMatrixSites N ξ η) (e : I ≃ J) (hweight : ∀ i, η (e i) = ν i) :
    S.reindexEquivalence T e hweight Ω = ξ := by
  simpa only [wordVector_nil, MatrixSiteWord.reindex, List.map_nil] using
    S.reindexEquivalence_word T e hweight []

theorem reindexEquivalence_intertwines (S : PointedMatrixSites M Ω ν)
    (T : PointedMatrixSites N ξ η) (e : I ≃ J) (hweight : ∀ i, η (e i) = ν i)
    (i : I) (a b : Fin 2) (x : H) :
    S.reindexEquivalence T e hweight ((S.site i).entry a b x) =
      (T.site (e i)).entry a b (S.reindexEquivalence T e hweight x) := by
  let U := S.reindexEquivalence T e hweight
  apply S.wordSpan_dense.induction_on (p := fun y =>
    U ((S.site i).entry a b y) = (T.site (e i)).entry a b (U y)) x
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro c
    have hmap : U (Finsupp.linearCombination ℂ S.wordVector c) =
        Finsupp.linearCombination ℂ
          (fun w => T.wordVector (MatrixSiteWord.reindex e w)) c :=
      cyclicGramEquivalence_linearCombination _ _ _ _ _ c
    rw [hmap]
    simp only [Finsupp.linearCombination_apply, map_finsuppSum, map_smul]
    apply Finsupp.sum_congr
    intro w hw
    congr 1
    change U ((S.site i).entry a b (S.wordVector w)) = _
    rw [← S.wordVector_cons (i, a, b) w]
    change S.reindexEquivalence T e hweight (S.wordVector ((i, a, b) :: w)) = _
    rw [reindexEquivalence_word]
    rfl

theorem reindexEquivalence_conjugate_site (S : PointedMatrixSites M Ω ν)
    (T : PointedMatrixSites N ξ η) (e : I ≃ J) (hweight : ∀ i, η (e i) = ν i)
    (i : I) (a b : Fin 2) :
    (S.reindexEquivalence T e hweight).conjStarAlgEquiv ((S.site i).entry a b) =
      (T.site (e i)).entry a b := by
  ext y
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, reindexEquivalence_intertwines,
    LinearIsometryEquiv.apply_symm_apply]

/-- The finite-word Hilbert equivalence transports the generated algebras. -/
theorem reindexEquivalence_algebra (S : PointedMatrixSites M Ω ν)
    (T : PointedMatrixSites N ξ η) (e : I ≃ J) (hweight : ∀ i, η (e i) = ν i) :
    spatialTransportAlgebra (S.reindexEquivalence T e hweight) M = N := by
  let U := S.reindexEquivalence T e hweight
  have hr : U.conjStarAlgEquiv '' Set.range S.siteGenerator = Set.range T.siteGenerator := by
    ext x
    constructor
    · rintro ⟨_, ⟨⟨i, a, b⟩, rfl⟩, rfl⟩
      exact ⟨(e i, a, b), (S.reindexEquivalence_conjugate_site T e hweight i a b).symm⟩
    · rintro ⟨⟨j, a, b⟩, rfl⟩
      refine ⟨S.siteGenerator (e.symm j, a, b), ⟨(e.symm j, a, b), rfl⟩, ?_⟩
      simpa only [U, siteGenerator, e.apply_symm_apply] using
        S.reindexEquivalence_conjugate_site T e hweight (e.symm j) a b
  change spatialTransportAlgebra U M = N
  calc
    spatialTransportAlgebra U M = spatialTransportAlgebra U
        (generatedVonNeumannAlgebra (StarAlgebra.adjoin ℂ (Set.range S.siteGenerator))) :=
      congrArg (spatialTransportAlgebra U) S.generates_siteGenerator
    _ = generatedVonNeumannAlgebra
        ((StarAlgebra.adjoin ℂ (Set.range S.siteGenerator)).map U.conjStarAlgEquiv.toStarAlgHom) :=
      spatialTransport_generated U _
    _ = generatedVonNeumannAlgebra (StarAlgebra.adjoin ℂ (Set.range T.siteGenerator)) := by
      rw [StarAlgHom.map_adjoin]
      exact congrArg (fun s => generatedVonNeumannAlgebra (StarAlgebra.adjoin ℂ s)) hr
    _ = N := T.generates_siteGenerator.symm

/-- The complete reindex clause of the published pointed-product input. -/
theorem exists_reindex_unitary (S : PointedMatrixSites M Ω ν)
    (T : PointedMatrixSites N ξ η) (e : I ≃ J) (hweight : ∀ i, η (e i) = ν i) :
    ∃ U : H ≃ₗᵢ[ℂ] K, U Ω = ξ ∧ ∀ x : H →L[ℂ] H, x ∈ M ↔ U.conjStarAlgEquiv x ∈ N := by
  refine ⟨S.reindexEquivalence T e hweight, S.reindexEquivalence_vector T e hweight, ?_⟩
  intro x
  have h := (mem_spatialTransportAlgebra (S.reindexEquivalence T e hweight) M
    ((S.reindexEquivalence T e hweight).conjStarAlgEquiv x)).symm
  simpa only [S.reindexEquivalence_algebra T e hweight,
    StarAlgEquiv.symm_apply_apply] using h

end PointedMatrixSites

end

end KadisonKastler

end OAI
