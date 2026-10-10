import OAI.NumberTheory.DukePrimeDegree.Geometry.RowRootChart

namespace OAI

/-!
# Actual row-root boxes in the lattice quotient

The simultaneous row chart descends through the discrete lattice
covering. Its local product boxes cover every point and disintegrate
the restricted ambient measure along the entire row group.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def rowQuotientParametrization {n : ℕ} (i k : Fin n)
    (z : RowRootSlice i k × RowTime i) : X n :=
  Quotient.mk _ ((rowPivotHomeomorph i k).symm z).val

lemma rowQuotientParametrization_localHomeomorph {n : ℕ} (i k : Fin n) :
    IsLocalHomeomorph (rowQuotientParametrization i k) := by
  exact ((quotient_covering n).isLocalHomeomorph.comp
    (rootPivot_isOpen i k).isOpenEmbedding_subtypeVal.isLocalHomeomorph).comp
    (rowPivotHomeomorph i k).symm.isLocalHomeomorph

lemma rowQuotientParametrization_add {n : ℕ} (i k : Fin n)
    (s : RowRootSlice i k) (a b : RowTime i) :
    rowQuotientParametrization i k (s, a + b) =
      rightAction (rowQuotientParametrization i k (s, a)) (rowRoot i b) := by
  change Quotient.mk _ (s.val * rowRoot i (a + b)) =
    Quotient.mk _ ((s.val * rowRoot i a) * rowRoot i b)
  rw [rowRoot_add, mul_assoc]

structure RowRootBox {n : ℕ} (i k : Fin n) where
  transverse : Set (RowRootSlice i k)
  time : Set (RowTime i)
  transverse_open : IsOpen transverse
  time_open : IsOpen time
  embedding : Topology.IsOpenEmbedding
    ((transverse ×ˢ time).domRestrict (rowQuotientParametrization i k))

namespace RowRootBox
variable {n : ℕ} {i k : Fin n}

abbrev domain (B : RowRootBox i k) := B.transverse ×ˢ B.time
abbrev param (B : RowRootBox i k) := B.domain.domRestrict (rowQuotientParametrization i k)
def range (B : RowRootBox i k) := Set.range B.param

lemma range_open (B : RowRootBox i k) : IsOpen B.range := B.embedding.isOpen_range

def coordinateMeasure (B : RowRootBox i k) (μ : Measure (X n)) :
    Measure (RowRootSlice i k × RowTime i) :=
  Measure.map Subtype.val (Measure.comap B.param μ)

instance coordinateMeasure_finite (B : RowRootBox i k) (μ : Measure (X n))
    [IsFiniteMeasure μ] : IsFiniteMeasure (B.coordinateMeasure μ) := by
  have he := B.embedding.measurableEmbedding
  have : IsFiniteMeasure (Measure.comap B.param μ) := ⟨by
    rw [he.comap_apply]
    exact lt_of_le_of_lt (measure_mono (subset_univ _)) (measure_lt_top μ univ)⟩
  unfold coordinateMeasure
  infer_instance

lemma map_coordinateMeasure (B : RowRootBox i k) (μ : Measure (X n)) :
    Measure.map (rowQuotientParametrization i k) (B.coordinateMeasure μ) =
      μ.restrict B.range := by
  rw [coordinateMeasure, Measure.map_map]
  · exact B.embedding.measurableEmbedding.map_comap μ
  · exact (rowQuotientParametrization_localHomeomorph i k).continuous.measurable
  · exact measurable_subtype_coe

def conditionalKernel (B : RowRootBox i k) (μ : Measure (X n)) [IsFiniteMeasure μ] :
    Kernel (RowRootSlice i k) (RowTime i) := (B.coordinateMeasure μ).condKernel

instance conditionalKernel_markov (B : RowRootBox i k) (μ : Measure (X n))
    [IsFiniteMeasure μ] : IsMarkovKernel (B.conditionalKernel μ) := by
  unfold conditionalKernel
  infer_instance

theorem disintegrate (B : RowRootBox i k) (μ : Measure (X n)) [IsFiniteMeasure μ] :
    Measure.map (rowQuotientParametrization i k)
      ((B.coordinateMeasure μ).fst ⊗ₘ B.conditionalKernel μ) = μ.restrict B.range := by
  rw [conditionalKernel, Measure.disintegrate]
  exact B.map_coordinateMeasure μ

end RowRootBox

theorem exists_rowRootBox_at_coordinates {n : ℕ} (i k : Fin n)
    (z : RowRootSlice i k × RowTime i) : ∃ B : RowRootBox i k, z ∈ B.domain := by
  obtain ⟨U, hUz, hU⟩ := isLocalHomeomorph_iff_isOpenEmbedding_restrict.mp
    (rowQuotientParametrization_localHomeomorph i k) z
  obtain ⟨V, W, hVo, hVz, hWo, hWz, hsub⟩ := mem_nhds_prod_iff'.mp hUz
  have he := hU.comp (Topology.IsOpenEmbedding.inclusion hsub
    ((hVo.prod hWo).preimage continuous_subtype_val))
  exact ⟨⟨V, W, hVo, hWo, he⟩, hVz, hWz⟩

theorem exists_rowRootBox_at {n : ℕ} (i : Fin n) (x : X n) :
    ∃ k : Fin n, ∃ B : RowRootBox i k, x ∈ B.range := by
  induction x using Quotient.inductionOn with
  | h g =>
    obtain ⟨k, hk⟩ := exists_rootPivot i g
    let g' : RootPivot i k := ⟨g, hk⟩
    let z := rowPivotHomeomorph i k g'
    obtain ⟨B, hB⟩ := exists_rowRootBox_at_coordinates i k z
    refine ⟨k, B, ⟨⟨z, hB⟩, ?_⟩⟩
    change Quotient.mk _ ((rowPivotHomeomorph i k).symm (rowPivotHomeomorph i k g')).val = _
    rw [(rowPivotHomeomorph i k).symm_apply_apply]

end DukePrimeDegree

end

end OAI
