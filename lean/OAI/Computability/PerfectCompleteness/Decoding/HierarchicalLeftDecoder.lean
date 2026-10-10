import OAI.Computability.PerfectCompleteness.Algebra.FunctionSpaceLowerRank
import OAI.Computability.PerfectCompleteness.Decoding.LeftDecoderKnownRows
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalFrozenTablesLemmas

namespace OAI

section

namespace PerfectCompleteness.HierarchicalLeftDecoder

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)

abbrev LowerNode (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :=
  (HierarchicalFrozenTables.lowerIndex upper lowerLevel d).val

local instance rowSpaceFintype (node : Nodes branch n) :
    Fintype (NodeEmbedding.RowSpace slots node) := Fintype.ofFinite _

local instance nodeSpaceFintype (node : Nodes branch n) :
    Fintype (NodeEmbedding.NodeH slots node) := Fintype.ofFinite _

local instance upperDualFintype : Fintype (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)

variable (hbranch : ∀ k < n, 0 < branch k)

def squareEmbedding (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :
    squareSpace (NodeEmbedding.NodeH slots (LowerNode upper lowerLevel d)) →ₗ[F2]
      NodeEmbedding.RowSpace slots upper where
  toFun f := ⟨PointwiseSpaces.pullback F2
    (NodeEmbedding.numberedRestriction slots (LowerNode upper lowerLevel d)) f.val, by
      apply RelativeDescendantProducts.squareSpace_le_rowSpace slots hbranch
        (RelativeDescendantProducts.descendantIndex_below upper d.val)
      rw [NodeEmbedding.squareSpace_eq]
      exact Submodule.mem_map_of_mem f.property⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp] theorem squareEmbedding_apply
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (f : squareSpace (NodeEmbedding.NodeH slots (LowerNode upper lowerLevel d)))
    (x : NodeEmbedding.NumberedDomain slots) :
    (squareEmbedding slots upper lowerLevel hbranch d f).val x =
      f.val (NodeEmbedding.numberedRestriction slots (LowerNode upper lowerLevel d) x) := rfl

def output (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (q : Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :
    Module.Dual F2 (squareSpace (NodeEmbedding.NodeH slots (LowerNode upper lowerLevel d))) :=
  q.comp (squareEmbedding slots upper lowerLevel hbranch d)

def lowerOne (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :
    squareSpace (NodeEmbedding.NodeH slots (LowerNode upper lowerLevel d)) :=
  ⟨1, TreeSourceSpaces.one_mem_squareSpace
    (nodeSlots slots (LowerNode upper lowerLevel d))
    (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk
      (Nodes.height_le (LowerNode upper lowerLevel d))))⟩

variable (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)

def testedMatrix (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :
    Module.Dual F2 (NodeEmbedding.NodeH slots (LowerNode upper lowerLevel d)) →ₗ[F2]
      Block rows (LowerNode upper lowerLevel d) :=
  EvaluationMatrix.ofRows (NodeEmbedding.NodeH slots (LowerNode upper lowerLevel d))
    (background (HierarchicalFrozenTables.lowerIndex upper lowerLevel d))

def oneKnown : HierarchicalFrozenTables.knownRows slots upper lowerLevel background :=
  ⟨⟨1, RelativeDescendantProducts.one_mem_rowSpace slots hbranch upper⟩,
    HierarchicalKnownRows.one_mem_knownSpace slots upper background
      (HierarchicalFrozenTables.lowerIndex upper lowerLevel)⟩

def productKnown (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (i j : Fin (rows (Nodes.height (LowerNode upper lowerLevel d)))) :
    HierarchicalFrozenTables.knownRows slots upper lowerLevel background :=
  ⟨squareEmbedding slots upper lowerLevel hbranch d
      (OddListExtraction.productElement
        (NodeEmbedding.NodeH slots (LowerNode upper lowerLevel d))
        (background (HierarchicalFrozenTables.lowerIndex upper lowerLevel d) i)
        (background (HierarchicalFrozenTables.lowerIndex upper lowerLevel d) j)),
    HierarchicalKnownRows.product_mem_knownSpace slots upper background
      (HierarchicalFrozenTables.lowerIndex upper lowerLevel) d i j⟩

theorem output_normalized_of_known_realizer
    (q : Module.Dual F2 (NodeEmbedding.RowSpace slots upper))
    (x : NodeEmbedding.NumberedDomain slots)
    (hknown : ∀ b : HierarchicalFrozenTables.knownRows slots upper lowerLevel background,
      q (b : NodeEmbedding.RowSpace slots upper) = b.val.val x)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :
    output slots upper lowerLevel hbranch d q (lowerOne slots upper lowerLevel hbranch d) = 1 := by
  exact hknown (oneKnown slots upper lowerLevel hbranch background)

theorem tested_rank_le_one_of_known_realizer
    (q : Module.Dual F2 (NodeEmbedding.RowSpace slots upper))
    (x : NodeEmbedding.NumberedDomain slots)
    (hknown : ∀ b : HierarchicalFrozenTables.knownRows slots upper lowerLevel background,
      q (b : NodeEmbedding.RowSpace slots upper) = b.val.val x)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :
    (LowerAffineSliceRank.testedGram
      (FunctionSpaceLowerRank.matrixForm
        (NodeEmbedding.NodeH slots (LowerNode upper lowerLevel d))
        (OddListExtraction.multiplicationForm
          (NodeEmbedding.NodeH slots (LowerNode upper lowerLevel d))
          (output slots upper lowerLevel hbranch d q)))
      (testedMatrix slots upper lowerLevel background d)).rank ≤ 1 := by
  let v := HierarchicalKnownRows.lower slots upper background
    (HierarchicalFrozenTables.lowerIndex upper lowerLevel) x d
  have hgram : LowerAffineSliceRank.testedGram
      (FunctionSpaceLowerRank.matrixForm
        (NodeEmbedding.NodeH slots (LowerNode upper lowerLevel d))
        (OddListExtraction.multiplicationForm
          (NodeEmbedding.NodeH slots (LowerNode upper lowerLevel d))
          (output slots upper lowerLevel hbranch d q)))
      (testedMatrix slots upper lowerLevel background d) = fun i j => v i * v j := by
    rw [FunctionSpaceLowerRank.testedGram_multiplicationForm]
    simp only [testedMatrix, EvaluationMatrix.rows_ofRows]
    funext i j
    exact hknown (productKnown slots upper lowerLevel hbranch background d i j)
  rw [hgram]
  exact Matrix.rank_vecMulVec_le v v

def Valid (q : Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) : Prop :=
  ∀ d : HierarchicalFrozenTables.LowerNodes upper lowerLevel,
    output slots upper lowerLevel hbranch d q (lowerOne slots upper lowerLevel hbranch d) = 1 ∧
    (LowerAffineSliceRank.testedGram
      (FunctionSpaceLowerRank.matrixForm
        (NodeEmbedding.NodeH slots (LowerNode upper lowerLevel d))
        (OddListExtraction.multiplicationForm
          (NodeEmbedding.NodeH slots (LowerNode upper lowerLevel d))
          (output slots upper lowerLevel hbranch d q)))
      (testedMatrix slots upper lowerLevel background d)).rank ≤ 1

theorem valid_of_known_realizer
    (q : Module.Dual F2 (NodeEmbedding.RowSpace slots upper))
    (hreal : ∃ x : NodeEmbedding.NumberedDomain slots,
      ∀ b : HierarchicalFrozenTables.knownRows slots upper lowerLevel background,
        q (b : NodeEmbedding.RowSpace slots upper) = b.val.val x) :
    Valid slots upper lowerLevel hbranch background q := by
  obtain ⟨x, hx⟩ := hreal
  intro d
  exact ⟨output_normalized_of_known_realizer slots upper lowerLevel hbranch background q x hx d,
    tested_rank_le_one_of_known_realizer slots upper lowerLevel hbranch background q x hx d⟩

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : HierarchicalFrozenTables.QuotientMatrix slots upper lowerLevel background → Prop)

def adviceLaw (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
    (U : Module.Dual F2 (NodeEmbedding.RowSpace slots upper ⧸
      HierarchicalFrozenTables.knownRows slots upper lowerLevel background) →ₗ[F2]
        (Fin r → F2)) : FiniteDistribution (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.adviceLaw (TreeCanonical.numberedSlots slots) (NodeEmbedding.RowSpace slots upper)
    (HierarchicalMatrixTable.other slots upper background) σ
    (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
    (HierarchicalFrozenTables.sectionMap slots upper lowerLevel background)
    (HierarchicalFrozenTables.sectionMap_spec slots upper lowerLevel background) useful r ρ A U

theorem adviceLaw_valid (r : Nat) (ρ : ℝ) (hρ : 0 < ρ)
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (U : Module.Dual F2 (NodeEmbedding.RowSpace slots upper ⧸
      HierarchicalFrozenTables.knownRows slots upper lowerLevel background) →ₗ[F2]
        (Fin r → F2)) :
    (adviceLaw slots upper lowerLevel background σ useful r ρ A U).probability
      (fun q => decide (Valid slots upper lowerLevel hbranch background q)) = 1 := by
  unfold adviceLaw
  apply LeftDecoderKnownRows.adviceLaw_probability_eq_one_of_known_realizer
    (TreeCanonical.numberedSlots slots) (NodeEmbedding.RowSpace slots upper)
    (HierarchicalMatrixTable.other slots upper background) σ
    (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
    (HierarchicalFrozenTables.sectionMap slots upper lowerLevel background)
    (HierarchicalFrozenTables.sectionMap_spec slots upper lowerLevel background) useful
    (HierarchicalFrozenTables.determined slots upper lowerLevel background) r ρ hρ A U
  intro q hq
  exact decide_eq_true (valid_of_known_realizer slots upper lowerLevel hbranch background q hq)

variable {r : Nat} {ρ : ℝ} {A : ManyGoodRows.RowMap (Block rows upper) r}
  {U : Module.Dual F2 (NodeEmbedding.RowSpace slots upper ⧸
    HierarchicalFrozenTables.knownRows slots upper lowerLevel background) →ₗ[F2]
      (Fin r → F2)}

theorem candidate_valid
    (w : DenseWitnessRealization.RepresentativeWitness
      (TreeCanonical.numberedSlots slots) (NodeEmbedding.RowSpace slots upper)
      (HierarchicalMatrixTable.other slots upper background) σ
      (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
      (HierarchicalFrozenTables.sectionMap slots upper lowerLevel background) useful
      (r := r) (ρ := ρ) (A := A) (U := U))
    (hρ : 0 < ρ)
    (q : PulledColumnSpace.Candidates
      (HierarchicalFrozenTables.knownRows slots upper lowerLevel background) w.columnSpace
      (LeftDecoder.center (TreeCanonical.numberedSlots slots) (NodeEmbedding.RowSpace slots upper)
        (HierarchicalMatrixTable.other slots upper background) σ
        (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
        (HierarchicalFrozenTables.sectionMap slots upper lowerLevel background)
        (HierarchicalFrozenTables.sectionMap_spec slots upper lowerLevel background) useful w)) :
    Valid slots upper lowerLevel hbranch background q.val := by
  obtain ⟨x, _, hx⟩ := LeftDecoder.exists_candidate_realizer
    (TreeCanonical.numberedSlots slots) (NodeEmbedding.RowSpace slots upper)
    (HierarchicalMatrixTable.other slots upper background) σ
    (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
    (HierarchicalFrozenTables.sectionMap slots upper lowerLevel background)
    (HierarchicalFrozenTables.sectionMap_spec slots upper lowerLevel background) useful
    (HierarchicalFrozenTables.determined slots upper lowerLevel background) w hρ
  exact valid_of_known_realizer slots upper lowerLevel hbranch background q.val ⟨x, hx q⟩

end
end PerfectCompleteness.HierarchicalLeftDecoder

end

end OAI
