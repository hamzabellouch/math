import OAI.Computability.PerfectCompleteness.Algebra.TensorBucketEvaluationLemmas
import OAI.Computability.PerfectCompleteness.Foundations.GoodAdviceEventsLemmas
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalFrozenTablesLemmas
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalPrediction

namespace OAI


namespace PerfectCompleteness.TensorRowAdvice

noncomputable section

open scoped Classical TensorProduct
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

section Algebra

variable {K H H' D : Type*} [AddCommGroup K] [Module F2 K]
  [AddCommGroup H] [Module F2 H] [AddCommGroup H'] [Module F2 H']
  [AddCommGroup D] [Module F2 D] [FiniteDimensional F2 H']
  (i : H' →ₗ[F2] H) (W : Submodule F2 K)

theorem comp_subtype_eq_zero (A : K →ₗ[F2] D) (hW : W ≤ LinearMap.ker A) :
    A.comp W.subtype = 0 := by
  apply LinearMap.ext
  intro w
  exact LinearMap.mem_ker.mp (hW w.property)

theorem rowAdvice_totalMatrix (A : K →ₗ[F2] D) (hW : W ≤ LinearMap.ker A)
    (X₀ : Module.Dual F2 H →ₗ[F2] K) (T : W ⊗[F2] H') :
    A.comp (TensorProjectedSlice.totalMatrix i W X₀ T) = A.comp X₀ := by
  apply LinearMap.ext
  intro z
  change A (X₀ z + (TensorRestriction.tensorEquivHom T (i.dualMap z) : K)) = A (X₀ z)
  rw [map_add]
  have hzero : A (TensorRestriction.tensorEquivHom T (i.dualMap z) : K) = 0 :=
    LinearMap.mem_ker.mp (hW (TensorRestriction.tensorEquivHom T (i.dualMap z)).property)
  rw [hzero, add_zero]

theorem rowAdvice_projectMatrix (A : K →ₗ[F2] D) (hW : W ≤ LinearMap.ker A)
    (B : Submodule F2 H) (X₀ : Module.Dual F2 H →ₗ[F2] K)
    (T : W ⊗[F2] H') :
    A.comp (MatrixRowQuotient.projectMatrix B (TensorProjectedSlice.totalMatrix i W X₀ T)) =
      A.comp (MatrixRowQuotient.projectMatrix B X₀) := by
  apply LinearMap.ext
  intro q
  exact LinearMap.congr_fun (rowAdvice_totalMatrix i W A hW X₀ T) (B.mkQ.dualMap q)

theorem rowAdvice_kernel_totalMatrix (A : K →ₗ[F2] D)
    (X₀ : Module.Dual F2 H →ₗ[F2] K) (T : LinearMap.ker A ⊗[F2] H') :
    A.comp (TensorProjectedSlice.totalMatrix i (LinearMap.ker A) X₀ T) = A.comp X₀ :=
  rowAdvice_totalMatrix i (LinearMap.ker A) A le_rfl X₀ T

end Algebra

section SelectionCongruence

variable {E K Y : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup K] [Module F2 K] [FiniteDimensional F2 E]
  [FiniteDimensional F2 K] [Fintype E] [Fintype K] [Fintype Y]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 K] [Fintype Y] in
theorem goodRow_iff_of_advice_eq (f : (E →ₗ[F2] K) → Option Y)
    (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap K r) (X X₀ : E →ₗ[F2] K)
    (hrow : A.comp X = A.comp X₀) :
    ManyGoodRows.GoodRow f r ρ A (A.comp X) ↔
      ManyGoodRows.GoodRow f r ρ A (A.comp X₀) := by
  rw [hrow]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 K] [Fintype Y] in
theorem selectedValue_eq_of_advice_eq (f : (E →ₗ[F2] K) → Option Y)
    (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap K r) (X X₀ : E →ₗ[F2] K)
    (hrow : A.comp X = A.comp X₀) :
    HierarchicalPrediction.selectedValue f r ρ A X =
      HierarchicalPrediction.selectedValue f r ρ A X₀ := by
  exact congrArg
    (fun U : E →ₗ[F2] (Fin r → F2) =>
      if h : ManyGoodRows.GoodRow f r ρ A U then
        some (ManyGoodRows.selectWitness f r ρ A U h).value
      else none) hrow

omit [FiniteDimensional F2 E] [FiniteDimensional F2 K] [Fintype Y] in
theorem selectWitness_fields_eq_of_advice_eq (f : (E →ₗ[F2] K) → Option Y)
    (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap K r)
    (U U₀ : E →ₗ[F2] (Fin r → F2)) (hrow : U = U₀)
    (h : ManyGoodRows.GoodRow f r ρ A U) (h₀ : ManyGoodRows.GoodRow f r ρ A U₀) :
    (ManyGoodRows.selectWitness f r ρ A U h).columnSpace =
        (ManyGoodRows.selectWitness f r ρ A U₀ h₀).columnSpace ∧
      (ManyGoodRows.selectWitness f r ρ A U h).base =
        (ManyGoodRows.selectWitness f r ρ A U₀ h₀).base ∧
      (ManyGoodRows.selectWitness f r ρ A U h).value =
        (ManyGoodRows.selectWitness f r ρ A U₀ h₀).value := by
  cases hrow
  exact ⟨rfl, rfl, rfl⟩

end SelectionCongruence


variable {K H H' Y : Type*} [AddCommGroup K] [Module F2 K]
  [AddCommGroup H] [Module F2 H] [AddCommGroup H'] [Module F2 H']
  [FiniteDimensional F2 H'] [FiniteDimensional F2 H] [FiniteDimensional F2 K]
  [Fintype H] [Fintype K] [Fintype Y]
  (i : H' →ₗ[F2] H) (W : Submodule F2 K)
  {r : Nat} (A : ManyGoodRows.RowMap K r) (hW : W ≤ LinearMap.ker A)

include hW

omit [FiniteDimensional F2 H] [FiniteDimensional F2 K] [Fintype Y] in
theorem goodRow_totalMatrix_iff
    (f : (Module.Dual F2 H →ₗ[F2] K) → Option Y) (ρ : ℝ)
    (X₀ : Module.Dual F2 H →ₗ[F2] K) (T : W ⊗[F2] H') :
    ManyGoodRows.GoodRow f r ρ A (A.comp (TensorProjectedSlice.totalMatrix i W X₀ T)) ↔
      ManyGoodRows.GoodRow f r ρ A (A.comp X₀) :=
  goodRow_iff_of_advice_eq f r ρ A _ _ (rowAdvice_totalMatrix i W A hW X₀ T)

omit [FiniteDimensional F2 H] [FiniteDimensional F2 K] [Fintype Y] in
theorem selectedValue_totalMatrix_eq
    (f : (Module.Dual F2 H →ₗ[F2] K) → Option Y) (ρ : ℝ)
    (X₀ : Module.Dual F2 H →ₗ[F2] K) (T : W ⊗[F2] H') :
    HierarchicalPrediction.selectedValue f r ρ A (TensorProjectedSlice.totalMatrix i W X₀ T) =
      HierarchicalPrediction.selectedValue f r ρ A X₀ :=
  selectedValue_eq_of_advice_eq f r ρ A _ _ (rowAdvice_totalMatrix i W A hW X₀ T)

omit [FiniteDimensional F2 H] [FiniteDimensional F2 K] [Fintype Y] in
theorem goodRow_projectMatrix_iff (B : Submodule F2 H)
    (f : (Module.Dual F2 (H ⧸ B) →ₗ[F2] K) → Option Y) (ρ : ℝ)
    (X₀ : Module.Dual F2 H →ₗ[F2] K) (T : W ⊗[F2] H') :
    ManyGoodRows.GoodRow f r ρ A
        (A.comp (MatrixRowQuotient.projectMatrix B
          (TensorProjectedSlice.totalMatrix i W X₀ T))) ↔
      ManyGoodRows.GoodRow f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀)) :=
  goodRow_iff_of_advice_eq f r ρ A _ _ (rowAdvice_projectMatrix i W A hW B X₀ T)

omit [FiniteDimensional F2 H] [FiniteDimensional F2 K] [Fintype Y] in
theorem selectedValue_projectMatrix_eq (B : Submodule F2 H)
    (f : (Module.Dual F2 (H ⧸ B) →ₗ[F2] K) → Option Y) (ρ : ℝ)
    (X₀ : Module.Dual F2 H →ₗ[F2] K) (T : W ⊗[F2] H') :
    HierarchicalPrediction.selectedValue f r ρ A
        (MatrixRowQuotient.projectMatrix B (TensorProjectedSlice.totalMatrix i W X₀ T)) =
      HierarchicalPrediction.selectedValue f r ρ A (MatrixRowQuotient.projectMatrix B X₀) :=
  selectedValue_eq_of_advice_eq f r ρ A _ _ (rowAdvice_projectMatrix i W A hW B X₀ T)

omit [FiniteDimensional F2 H] [FiniteDimensional F2 K] [Fintype Y] in
theorem selectWitness_projectMatrix_fields_eq (B : Submodule F2 H)
    (f : (Module.Dual F2 (H ⧸ B) →ₗ[F2] K) → Option Y) (ρ : ℝ)
    (X₀ : Module.Dual F2 H →ₗ[F2] K) (T : W ⊗[F2] H')
    (h : ManyGoodRows.GoodRow f r ρ A
      (A.comp (MatrixRowQuotient.projectMatrix B (TensorProjectedSlice.totalMatrix i W X₀ T))))
    (h₀ : ManyGoodRows.GoodRow f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀))) :
    (ManyGoodRows.selectWitness f r ρ A
        (A.comp (MatrixRowQuotient.projectMatrix B (TensorProjectedSlice.totalMatrix i W X₀ T))) h).columnSpace =
      (ManyGoodRows.selectWitness f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀)) h₀).columnSpace ∧
    (ManyGoodRows.selectWitness f r ρ A
        (A.comp (MatrixRowQuotient.projectMatrix B (TensorProjectedSlice.totalMatrix i W X₀ T))) h).base =
      (ManyGoodRows.selectWitness f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀)) h₀).base ∧
    (ManyGoodRows.selectWitness f r ρ A
        (A.comp (MatrixRowQuotient.projectMatrix B (TensorProjectedSlice.totalMatrix i W X₀ T))) h).value =
      (ManyGoodRows.selectWitness f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀)) h₀).value :=
  selectWitness_fields_eq_of_advice_eq f r ρ A _ _
    (rowAdvice_projectMatrix i W A hW B X₀ T) h h₀

end
end PerfectCompleteness.TensorRowAdvice



namespace PerfectCompleteness.TensorSelectedSlice

noncomputable section

open scoped Classical TensorProduct
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {K H H' Y : Type*} [AddCommGroup K] [Module F2 K]
  [AddCommGroup H] [Module F2 H] [AddCommGroup H'] [Module F2 H']
  [FiniteDimensional F2 H'] [FiniteDimensional F2 H] [FiniteDimensional F2 K]
  [Fintype H] [Fintype K] [Fintype Y]
  (i : H' →ₗ[F2] H) (W : Submodule F2 K) (B : Submodule F2 H)

abbrev projectedMatrix (X₀ : Module.Dual F2 H →ₗ[F2] K) (T : W ⊗[F2] H') :=
  MatrixRowQuotient.projectMatrix B (TensorProjectedSlice.totalMatrix i W X₀ T)

omit [FiniteDimensional F2 H] [FiniteDimensional F2 K] [Fintype H] [Fintype K] in
theorem projectedMatrix_eq_totalMatrix
    (X₀ : Module.Dual F2 H →ₗ[F2] K) (T : W ⊗[F2] H') :
    projectedMatrix i W B X₀ T =
      TensorProjectedSlice.totalMatrix (B.mkQ.comp i) W
        (MatrixRowQuotient.projectMatrix B X₀) T := by
  apply LinearMap.ext
  intro q
  rfl

variable (f : (Module.Dual F2 (H ⧸ B) →ₗ[F2] K) → Option Y)
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap K r)
  (X₀ : Module.Dual F2 H →ₗ[F2] K)

def witness
    (hgood : ManyGoodRows.GoodRow f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀))) :
    ManyGoodRows.Witness f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀)) :=
  ManyGoodRows.selectWitness f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀)) hgood

def columnSpace
    (hgood : ManyGoodRows.GoodRow f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀))) :
    Submodule F2 (Module.Dual F2 H') :=
  ProjectedColumnSlice.projectedColumns (B.mkQ.comp i)
    (witness B f r ρ A X₀ hgood).columnSpace

omit [FiniteDimensional F2 H'] [FiniteDimensional F2 H] [FiniteDimensional F2 K] [Fintype Y] in
theorem columnSpace_eq_sequential_maps
    (hgood : ManyGoodRows.GoodRow f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀))) :
    columnSpace i B f r ρ A X₀ hgood =
      ((witness B f r ρ A X₀ hgood).columnSpace.map B.mkQ.dualMap).map i.dualMap := by
  unfold columnSpace ProjectedColumnSlice.projectedColumns
  exact Submodule.map_comp B.mkQ.dualMap i.dualMap _

omit [FiniteDimensional F2 H'] [FiniteDimensional F2 K] [Fintype Y] in
theorem finrank_columnSpace_le
    (hgood : ManyGoodRows.GoodRow f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀))) :
    Module.finrank F2 (columnSpace i B f r ρ A X₀ hgood) ≤ r :=
  (ProjectedColumnSlice.finrank_projectedColumns_le (B.mkQ.comp i)
    (witness B f r ρ A X₀ hgood).columnSpace).trans
      (witness B f r ρ A X₀ hgood).column_count

variable (hW : W ≤ LinearMap.ker A)

include hW

omit [FiniteDimensional F2 H] [FiniteDimensional F2 K] [Fintype Y] in
theorem J_eq_decide_columns
    (hgood : ManyGoodRows.GoodRow f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀)))
    (T : W ⊗[F2] H') :
    GoodAdviceEvents.J f r ρ (A, projectedMatrix i W B X₀ T) =
      decide ((projectedMatrix i W B X₀ T).domRestrict
          (witness B f r ρ A X₀ hgood).columnSpace =
        (witness B f r ρ A X₀ hgood).base.domRestrict
          (witness B f r ρ A X₀ hgood).columnSpace) := by
  change GoodAdviceEvents.selectedColumn f r ρ A
    (A.comp (projectedMatrix i W B X₀ T)) (projectedMatrix i W B X₀ T) = _
  unfold GoodAdviceEvents.selectedColumn
  have hrow : A.comp (projectedMatrix i W B X₀ T) =
      A.comp (MatrixRowQuotient.projectMatrix B X₀) :=
    TensorRowAdvice.rowAdvice_projectMatrix i W A hW B X₀ T
  rw [hrow]
  simp only [dite_eq_left hgood, witness]
  exact decide_eq_decide.mpr Iff.rfl

omit [FiniteDimensional F2 H] [FiniteDimensional F2 K] [Fintype Y] in
theorem J_false_of_not_good
    (hbad : ¬ ManyGoodRows.GoodRow f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀)))
    (T : W ⊗[F2] H') :
    GoodAdviceEvents.J f r ρ (A, projectedMatrix i W B X₀ T) = false := by
  change GoodAdviceEvents.selectedColumn f r ρ A
    (A.comp (projectedMatrix i W B X₀ T)) (projectedMatrix i W B X₀ T) = false
  unfold GoodAdviceEvents.selectedColumn
  have hrow : A.comp (projectedMatrix i W B X₀ T) =
      A.comp (MatrixRowQuotient.projectMatrix B X₀) :=
    TensorRowAdvice.rowAdvice_projectMatrix i W A hW B X₀ T
  rw [hrow]
  exact dite_eq_right hbad

omit [FiniteDimensional F2 H] [FiniteDimensional F2 K] [Fintype Y] in
theorem J_iff_compatible
    (hgood : ManyGoodRows.GoodRow f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀)))
    (T : W ⊗[F2] H') :
    GoodAdviceEvents.J f r ρ (A, projectedMatrix i W B X₀ T) = true ↔
      TensorProjectedSlice.Compatible (B.mkQ.comp i) W
        (witness B f r ρ A X₀ hgood).columnSpace
        (MatrixRowQuotient.projectMatrix B X₀)
        ((witness B f r ρ A X₀ hgood).base.domRestrict
          (witness B f r ρ A X₀ hgood).columnSpace) T := by
  calc
    _ ↔ (projectedMatrix i W B X₀ T).domRestrict
        (witness B f r ρ A X₀ hgood).columnSpace =
      (witness B f r ρ A X₀ hgood).base.domRestrict
        (witness B f r ρ A X₀ hgood).columnSpace := by
      rw [J_eq_decide_columns i W B f r ρ A X₀ hW hgood T, decide_eq_true_eq]
    _ ↔ _ := Iff.of_eq (congrArg
      (fun X : Module.Dual F2 (H ⧸ B) →ₗ[F2] K =>
        X.domRestrict (witness B f r ρ A X₀ hgood).columnSpace =
          (witness B f r ρ A X₀ hgood).base.domRestrict
            (witness B f r ρ A X₀ hgood).columnSpace)
      (projectedMatrix_eq_totalMatrix i W B X₀ T))

omit [FiniteDimensional F2 H] [FiniteDimensional F2 K] [Fintype Y] in
theorem exists_compatible
    (hgood : ManyGoodRows.GoodRow f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀)))
    (hne : ∃ T : W ⊗[F2] H', GoodAdviceEvents.J f r ρ (A, projectedMatrix i W B X₀ T) = true) :
    ∃ T : W ⊗[F2] H', TensorProjectedSlice.Compatible (B.mkQ.comp i) W
      (witness B f r ρ A X₀ hgood).columnSpace
      (MatrixRowQuotient.projectMatrix B X₀)
      ((witness B f r ρ A X₀ hgood).base.domRestrict
        (witness B f r ρ A X₀ hgood).columnSpace) T := by
  obtain ⟨T, hT⟩ := hne
  exact ⟨T, (J_iff_compatible i W B f r ρ A X₀ hW hgood T).mp hT⟩

def target
    (hgood : ManyGoodRows.GoodRow f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀)))
    (hne : ∃ T : W ⊗[F2] H', GoodAdviceEvents.J f r ρ (A, projectedMatrix i W B X₀ T) = true) :
    columnSpace i B f r ρ A X₀ hgood →ₗ[F2] W :=
  TensorProjectedSlice.inducedTarget (B.mkQ.comp i) W
    (witness B f r ρ A X₀ hgood).columnSpace
    (MatrixRowQuotient.projectMatrix B X₀)
    ((witness B f r ρ A X₀ hgood).base.domRestrict
      (witness B f r ρ A X₀ hgood).columnSpace)
    (exists_compatible i W B f r ρ A X₀ hW hgood hne)

omit [FiniteDimensional F2 H] [FiniteDimensional F2 K] [Fintype Y] in
theorem J_iff_restriction
    (hgood : ManyGoodRows.GoodRow f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀)))
    (hne : ∃ T : W ⊗[F2] H', GoodAdviceEvents.J f r ρ (A, projectedMatrix i W B X₀ T) = true)
    (T : W ⊗[F2] H') :
    GoodAdviceEvents.J f r ρ (A, projectedMatrix i W B X₀ T) = true ↔
      TensorRestriction.restrictionMap (columnSpace i B f r ρ A X₀ hgood) T =
        target i W B f r ρ A X₀ hW hgood hne :=
  (J_iff_compatible i W B f r ρ A X₀ hW hgood T).trans
    (TensorProjectedSlice.columnEquations_iff_inducedTarget (B.mkQ.comp i) W
      (witness B f r ρ A X₀ hgood).columnSpace
      (MatrixRowQuotient.projectMatrix B X₀)
      ((witness B f r ρ A X₀ hgood).base.domRestrict
        (witness B f r ρ A X₀ hgood).columnSpace)
      (exists_compatible i W B f r ρ A X₀ hW hgood hne) T)

omit [FiniteDimensional F2 K] [Fintype Y] in
theorem exists_tensor_slice
    (hgood : ManyGoodRows.GoodRow f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀)))
    (hne : ∃ T : W ⊗[F2] H', GoodAdviceEvents.J f r ρ (A, projectedMatrix i W B X₀ T) = true) :
    ∃ (Q : Submodule F2 (Module.Dual F2 H')) (t : Q →ₗ[F2] W),
      Module.finrank F2 Q ≤ r ∧
      ∀ T : W ⊗[F2] H', GoodAdviceEvents.J f r ρ (A, projectedMatrix i W B X₀ T) = true ↔
        TensorRestriction.restrictionMap Q T = t := by
  exact ⟨columnSpace i B f r ρ A X₀ hgood,
    target i W B f r ρ A X₀ hW hgood hne,
    finrank_columnSpace_le i B f r ρ A X₀ hgood,
    J_iff_restriction i W B f r ρ A X₀ hW hgood hne⟩

end
end PerfectCompleteness.TensorSelectedSlice



namespace PerfectCompleteness.HierarchicalTensorSlice

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)
  (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _

local instance valueFintype : Fintype
    (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  Fintype.ofFinite _

variable {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (arrays : Ω → Arrays slots rows)
  (lowerEvent : Ω → Bool) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  {r : Nat} (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (known : HiddenBucketBias.VisibleDirection (LinearMap.ker A) → NodeEmbedding.NodeH slots upper)

abbrev HiddenTensor := LinearMap.ker A ⊗[F2] NodeEmbedding.NodeH slots upper

abbrev visibleMatrix := HierarchicalTensorMatrix.visibleMatrix slots upper (LinearMap.ker A) known

abbrev matrix (T : HiddenTensor slots upper A) :=
  TensorProjectedSlice.totalMatrix (NodeEmbedding.embed slots upper) (LinearMap.ker A)
    (visibleMatrix slots upper A known) T

abbrev quotientMatrix (T : HiddenTensor slots upper A) :=
  MatrixRowQuotient.projectMatrix
    (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
    (matrix slots upper A known T)

abbrev table :=
  HierarchicalUsefulness.table slots upper lowerLevel original arrays lowerEvent κ σ background

abbrev VisibleGood : Prop :=
  ManyGoodRows.GoodRow (table slots upper lowerLevel background original arrays lowerEvent κ σ)
    r ρ A (A.comp (MatrixRowQuotient.projectMatrix
      (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
      (visibleMatrix slots upper A known)))

def witness
    (hgood : VisibleGood slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :=
  TensorSelectedSlice.witness
    (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
    (table slots upper lowerLevel background original arrays lowerEvent κ σ)
    r ρ A (visibleMatrix slots upper A known) hgood

def columnSpace
    (hgood : VisibleGood slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :
    Submodule F2 (Module.Dual F2 (NodeEmbedding.NodeH slots upper)) :=
  TensorSelectedSlice.columnSpace (NodeEmbedding.embed slots upper)
    (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
    (table slots upper lowerLevel background original arrays lowerEvent κ σ)
    r ρ A (visibleMatrix slots upper A known) hgood

theorem columnSpace_eq_pulled
    (hgood : VisibleGood slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :
    columnSpace slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood =
      ((witness slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).columnSpace.map
        (HierarchicalFrozenTables.knownRows slots upper lowerLevel background).mkQ.dualMap).map
        (NodeEmbedding.embed slots upper).dualMap :=
  TensorSelectedSlice.columnSpace_eq_sequential_maps (NodeEmbedding.embed slots upper)
    (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
    (table slots upper lowerLevel background original arrays lowerEvent κ σ)
    r ρ A (visibleMatrix slots upper A known) hgood

theorem finrank_columnSpace_le
    (hgood : VisibleGood slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :
    Module.finrank F2
      (columnSpace slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood) ≤ r :=
  TensorSelectedSlice.finrank_columnSpace_le (NodeEmbedding.embed slots upper)
    (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
    (table slots upper lowerLevel background original arrays lowerEvent κ σ)
    r ρ A (visibleMatrix slots upper A known) hgood

def J (T : HiddenTensor slots upper A) : Bool :=
  GoodAdviceEvents.J (table slots upper lowerLevel background original arrays lowerEvent κ σ)
    r ρ (A, quotientMatrix slots upper lowerLevel background A known T)

def target
    (hgood : VisibleGood slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known)
    (hne : ∃ T, J slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known T = true) :
    columnSpace slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood →ₗ[F2]
      LinearMap.ker A :=
  TensorSelectedSlice.target (NodeEmbedding.embed slots upper) (LinearMap.ker A)
    (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
    (table slots upper lowerLevel background original arrays lowerEvent κ σ)
    r ρ A (visibleMatrix slots upper A known) le_rfl hgood hne

theorem J_iff_restriction
    (hgood : VisibleGood slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known)
    (hne : ∃ T, J slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known T = true)
    (T : HiddenTensor slots upper A) :
    J slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known T = true ↔
      TensorRestriction.restrictionMap
        (columnSpace slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood) T =
      target slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood hne :=
  TensorSelectedSlice.J_iff_restriction (NodeEmbedding.embed slots upper) (LinearMap.ker A)
    (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
    (table slots upper lowerLevel background original arrays lowerEvent κ σ)
    r ρ A (visibleMatrix slots upper A known) le_rfl hgood hne T

theorem J_false_of_not_good
    (hbad : ¬ VisibleGood slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known)
    (T : HiddenTensor slots upper A) :
    J slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known T = false :=
  TensorSelectedSlice.J_false_of_not_good (NodeEmbedding.embed slots upper) (LinearMap.ker A)
    (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
    (table slots upper lowerLevel background original arrays lowerEvent κ σ)
    r ρ A (visibleMatrix slots upper A known) le_rfl hbad T

theorem selectedValue_eq_some
    (hgood : VisibleGood slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known)
    (T : HiddenTensor slots upper A) :
    HierarchicalPrediction.selectedValue
        (table slots upper lowerLevel background original arrays lowerEvent κ σ) r ρ A
        (quotientMatrix slots upper lowerLevel background A known T) =
      some (witness slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value := by
  change HierarchicalPrediction.selectedValue _ r ρ A
    (MatrixRowQuotient.projectMatrix _ (TensorProjectedSlice.totalMatrix _ _ _ T)) = _
  rw [TensorRowAdvice.selectedValue_projectMatrix_eq (NodeEmbedding.embed slots upper)
    (LinearMap.ker A) A le_rfl
    (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
    (table slots upper lowerLevel background original arrays lowerEvent κ σ) ρ
    (visibleMatrix slots upper A known) T]
  simp only [HierarchicalPrediction.selectedValue, dite_eq_left hgood, witness,
    TensorSelectedSlice.witness]

def correction
    (y : Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :
    Module.Dual F2 (NodeEmbedding.RowSpace slots upper) :=
  RepresentativeMatrixTable.correctionFunctional (TreeCanonical.numberedSlots slots)
    (NodeEmbedding.RowSpace slots upper) (HierarchicalMatrixTable.other slots upper background)
    (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
    (HierarchicalFrozenTables.sectionMap slots upper lowerLevel background)
    (HierarchicalFrozenTables.sectionMap_spec slots upper lowerLevel background) y.2

def nativeCorrection
    (hgood : VisibleGood slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :
    Module.Dual F2 (NodeEmbedding.NodeH slots upper) :=
  (correction slots upper lowerLevel background
    (witness slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value).comp
      (NodeEmbedding.embed slots upper)

def visibleOffset
    (hgood : VisibleGood slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :
    Block rows upper :=
  visibleMatrix slots upper A known
      (correction slots upper lowerLevel background
        (witness slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value) +
    (witness slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value.1

theorem selectedCorrection_eq_some
    (hgood : VisibleGood slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known)
    (T : HiddenTensor slots upper A) :
    (HierarchicalPrediction.selectedValue
      (table slots upper lowerLevel background original arrays lowerEvent κ σ) r ρ A
      (quotientMatrix slots upper lowerLevel background A known T)).map
        (fun y => (correction slots upper lowerLevel background y).comp
          (NodeEmbedding.embed slots upper)) =
      some (nativeCorrection slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood) := by
  simp only [selectedValue_eq_some slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood T,
    Option.map_some, nativeCorrection]

theorem affinePrediction_eq_tensor
    (hgood : VisibleGood slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known)
    (T : HiddenTensor slots upper A) :
    HierarchicalPrediction.affinePrediction slots upper lowerLevel background
        (matrix slots upper A known T)
        (witness slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value =
      visibleOffset slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood +
        TensorBucketEvaluation.tensorOutput (LinearMap.ker A)
          (nativeCorrection slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood) T :=
  TensorProjectedSlice.prediction_eq_visible_add_tensorOutput (NodeEmbedding.embed slots upper)
    (LinearMap.ker A) (visibleMatrix slots upper A known) T
    (correction slots upper lowerLevel background
      (witness slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value)
    (witness slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value.1

end
end PerfectCompleteness.HierarchicalTensorSlice

end OAI
