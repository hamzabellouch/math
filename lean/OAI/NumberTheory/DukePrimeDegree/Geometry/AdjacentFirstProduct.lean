import OAI.NumberTheory.DukePrimeDegree.Geometry.AdjacentFirstRoot

namespace OAI

/-!
# An unconditional adjacent-root product in actual Gaussian boxes

The neutral weights and remaining elimination chain are constructed
explicitly. Every point of this chart lies in a bounded actual quotient
box whose pulled-back conditional measure splits at the first root.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma adjacentRootNe (d : ℕ) : (0 : Fin (d + 2)) ≠ 1 := by norm_num

theorem adjacent_first_conditional_product
    (d : ℕ) (A : RootBox (adjacentRootNe d) 0)
    (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (hcover : A.transverse ⊆ Set.range (firstRootSliceParam (adjacentRootNe d) (adjacentFirstTail d)))
    (μ : Measure (X (d + 2))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates (d + 1), μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    let σ := rootFactorPullback (adjacentRootNe d) A μ
      (firstRootSliceParam (adjacentRootNe d) (adjacentFirstTail d))
    haveI := rootFactorPullback_finite (adjacentRootNe d) A μ
      (firstRootSliceParam (adjacentRootNe d) (adjacentFirstTail d))
      (firstRootSliceParam_isOpenEmbedding (adjacentRootNe d) (adjacentFirstTail d)).measurableEmbedding
    ∀ᵐ s ∂σ.fst, σ.condKernel s = (σ.condKernel s).fst.prod (σ.condKernel s).snd := by
  obtain ⟨ell, hell, hneutral, hdecay⟩ := exists_adjacent_first_weights d
  exact firstRootChart_conditional_product (d + 1) (adjacentRootNe d) (adjacentFirstTail d)
    (adjacentFirstTail_final d) ell hell hneutral hdecay A R hAR hcover μ hA

theorem exists_adjacent_first_product_box
    (d : ℕ) (z : (adjacentFirstTail d).FinalSlice × (adjacentFirstTail d).Time) (t : ℝ)
    (μ : Measure (X (d + 2))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates (d + 1), μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ (A : RootBox (adjacentRootNe d) 0) (R : ℝ),
      (firstRootSliceParam (adjacentRootNe d) (adjacentFirstTail d) z, t) ∈ A.domain ∧
      A.time ⊆ rootLeafWindow R 0 ∧
      let σ := rootFactorPullback (adjacentRootNe d) A μ
        (firstRootSliceParam (adjacentRootNe d) (adjacentFirstTail d))
      haveI := rootFactorPullback_finite (adjacentRootNe d) A μ
        (firstRootSliceParam (adjacentRootNe d) (adjacentFirstTail d))
        (firstRootSliceParam_isOpenEmbedding (adjacentRootNe d) (adjacentFirstTail d)).measurableEmbedding
      ∀ᵐ s ∂σ.fst, σ.condKernel s = (σ.condKernel s).fst.prod (σ.condKernel s).snd := by
  obtain ⟨A, R, hz, hcover, hbound⟩ := exists_firstRootBox (d + 2)
    (adjacentRootNe d) (adjacentFirstTail d) z t
  exact ⟨A, R, hz, hbound, adjacent_first_conditional_product d A R hbound hcover μ hA⟩

end DukePrimeDegree

end

end OAI
