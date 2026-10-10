import OAI.Analysis.KadisonSimilarity.Representation.JointFiberCommutants
import OAI.Analysis.KadisonSimilarity.Representation.RankOneFactorCriterion

namespace OAI

/-! Countable rank-one tests in the joint representation force the first
source's represented von Neumann algebra to be a factor. -/

noncomputable section
namespace KadisonSimilarity

variable {A K ι : Type*} [CStarAlgebra A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- No measurable selection is needed: centrality and dense rank-one tests
in the joint bicommutant force each central operator to be scalar. -/
theorem joint_first_scalar_center_of_rankOne
    (B C : StarSubalgebra ℂ A)
    [IsClosed (B : Set A)] [IsClosed (C : Set A)]
    (hBC : ∀ b : B, ∀ c : C, (b : A) * (c : A) = (c : A) * (b : A))
    (σ : jointCStarSource B C →⋆ₐ[ℂ] (K →L[ℂ] K))
    (d : ι → K) (hd : DenseRange d)
    (hRank : ∀ i j, InnerProductSpace.rankOne ℂ (d i) (d j) ∈
      representationVonNeumannAlgebra σ) :
    ∀ a : (representationVonNeumannAlgebra
      (σ.comp (StarSubalgebra.inclusion (le_jointCStarSource_left B C)))).toStarSubalgebra,
      (∀ b, a * b = b * a) → ∃ c : ℂ, a = algebraMap ℂ _ c := by
  intro a ha
  have hcenter : (a : K →L[ℂ] K) ∈ vonNeumannCenter (representationVonNeumannAlgebra
      (σ.comp (StarSubalgebra.inclusion (le_jointCStarSource_left B C)))) := by
    refine ⟨a.property, VonNeumannAlgebra.mem_commutant_iff.mpr ?_⟩
    intro b hb
    exact (congrArg Subtype.val (ha ⟨b, hb⟩)).symm
  obtain ⟨c, hc⟩ := scalar_of_commutes_dense_rankOne d hd (a : K →L[ℂ] K)
    (fun i j => joint_center_commutes_joint_bicommutant B C hBC σ a _ hcenter (hRank i j))
  refine ⟨c, Subtype.ext ?_⟩
  change (a : K →L[ℂ] K) = c • (1 : K →L[ℂ] K)
  exact hc

end KadisonSimilarity

end

end OAI
