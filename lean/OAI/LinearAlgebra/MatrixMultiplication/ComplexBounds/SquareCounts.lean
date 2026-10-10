import OAI.LinearAlgebra.MatrixMultiplication.Completion.Cardinality
import OAI.LinearAlgebra.MatrixMultiplication.Completion.Termination
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.BaseTensorBudgets
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexEntropyContinuity

namespace OAI

/-! Explicit complex square and rectangular matrix multiplication bounds. -/

noncomputable section

namespace MatrixMultiplication.SquareCounts

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels CompletionCardinality
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

universe uCoord

private theorem colorBA : Color.B ≠ Color.A := by intro h; cases h
private theorem colorBC : Color.B ≠ Color.C := by intro h; cases h
private theorem colorAB : Color.A ≠ Color.B := by intro h; cases h
private theorem colorAC : Color.A ≠ Color.C := by intro h; cases h
private theorem colorCB : Color.C ≠ Color.B := by intro h; cases h
private theorem colorCA : Color.C ≠ Color.A := by intro h; cases h

attribute [local simp] colorBA colorBC colorAB colorAC colorCB colorCA

def baseLeaf (i : Fin 5) : CompletionLabels.Leaf BaseThree.flagged :=
  ⟨BaseThree.point i, by
    change BaseThree.tensor _ _ _ ≠ 0
    rw [BaseThree.point_supported]
    exact one_ne_zero⟩

def baseLeafEquiv : Fin 5 ≃ CompletionLabels.Leaf BaseThree.flagged :=
  Equiv.ofBijective baseLeaf ⟨by
    intro i j h
    exact BaseThree.point_injective (congrArg Subtype.val h), by
    intro a
    obtain ⟨i, hi⟩ := (BaseThree.support_enumeration _ _ _).mp a.property
    exact ⟨i, Subtype.ext hi⟩⟩

theorem baseLeaf_color (i : Fin 5) :
    leafColor BaseThree.flagged (baseLeaf i) = BaseThree.leafColor i := by
  fin_cases i <;>
    norm_num [leafColor, baseLeaf, BaseThree.flagged, BaseThree.flagB, BaseThree.flagA,
      BaseThree.point, BaseThree.leafColor, Fin.ext_iff]

def initialCount : Color → ℕ
  | .B => 2
  | .A => 2
  | .C => 1

theorem base_conditionalCount (c : Color) :
    conditionalCount BaseThree.flagged c = initialCount c := by
  have h := Fintype.card_congr
    (baseLeafEquiv.subtypeEquiv
      (p := fun i => BaseThree.leafColor i = c)
      (q := fun a => leafColor BaseThree.flagged a = c)
      (fun i => by change _ ↔ leafColor BaseThree.flagged (baseLeaf i) = c
                   rw [baseLeaf_color]))
  change Fintype.card {a : CompletionLabels.Leaf BaseThree.flagged //
    leafColor BaseThree.flagged a = c} = _
  rw [← h]
  simp only [Fintype.card_subtype, Finset.card_filter, Fin.sum_univ_five]
  cases c <;>
    norm_num [BaseThree.leafColor, initialCount,
      show (3 : Fin 5).val = 3 from rfl, show (4 : Fin 5).val = 4 from rfl]

def counts : Script → Color → ℕ
  | .base => initialCount
  | .step prior center m => fun c =>
      if c = center then counts prior center ^ m
      else (counts prior center + counts prior c) ^ m - counts prior center ^ m

theorem conditionalCount_script (s : Script) (c : Color) :
    conditionalCount (Script.tensor BaseThree.flagged s) c = counts s c := by
  induction s generalizing c with
  | base => exact base_conditionalCount c
  | step prior center m ih =>
      change conditionalCount (complete (Script.tensor BaseThree.flagged prior) center m) c = _
      rw [CompletionCardinality.count_complete]
      simp only [counts, ih]

def stageOne : Script := Script.step Script.base .B 2
def stageTwo : Script := stageOne.step .A 3
def stageThree : Script := stageTwo.step .C 2
def stageFour : Script := stageThree.step .B 2

theorem factors_at_every_stage :
    stageOne.factors = 2 ∧ stageTwo.factors = 6 ∧ stageThree.factors = 12 ∧
      stageFour.factors = 24 ∧ Script.square.factors = 72 := by
  norm_num [stageOne, stageTwo, stageThree, stageFour, Script.factors, Script.square]

theorem counts_after_three :
    counts stageThree .B = 20691584 ∧ counts stageThree .A = 13993344 ∧
      counts stageThree .C = 10144225 := by
  norm_num [counts, initialCount, stageThree, stageTwo, stageOne, reduceCtorEq]

theorem counts_after_four :
    counts stageFour .B = 428141648429056 ∧
      counts stageFour .A = 774902581936128 ∧
      counts stageFour .C = 522705468255425 := by
  norm_num [counts, initialCount, stageFour, stageThree, stageTwo, stageOne, reduceCtorEq]

theorem actual_counts_after_three :
    conditionalCount (Script.tensor BaseThree.flagged stageThree) .B = 20691584 ∧
    conditionalCount (Script.tensor BaseThree.flagged stageThree) .A = 13993344 ∧
    conditionalCount (Script.tensor BaseThree.flagged stageThree) .C = 10144225 := by
  simpa only [conditionalCount_script] using counts_after_three

theorem actual_counts_after_four :
    conditionalCount (Script.tensor BaseThree.flagged stageFour) .B = 428141648429056 ∧
    conditionalCount (Script.tensor BaseThree.flagged stageFour) .A = 774902581936128 ∧
    conditionalCount (Script.tensor BaseThree.flagged stageFour) .C = 522705468255425 := by
  simpa only [conditionalCount_script] using counts_after_four

def completed := Script.tensor BaseThree.flagged Script.square

theorem completion_unit_coefficients {X Y Z : Type uCoord}
    (S : FlaggedTensor X Y Z)
    (unit : ∀ x y z, S.tensor x y z ≠ 0 → S.tensor x y z = 1)
    (center : Color) (m : ℕ) (x y z)
    (supported : (complete S center m).tensor x y z ≠ 0) :
    (complete S center m).tensor x y z = 1 := by
  rw [complete_tensor] at supported ⊢
  split_ifs at supported ⊢ with h
  · apply Finset.prod_eq_one
    intro i hi
    exact unit _ _ _ ((Finset.prod_ne_zero_iff.mp supported) i hi)
  · exact False.elim (supported rfl)

theorem script_unit_coefficients (s : Script) :
    ∀ x y z, (Script.tensor BaseThree.flagged s).tensor x y z ≠ 0 →
      (Script.tensor BaseThree.flagged s).tensor x y z = 1 := by
  induction s with
  | base =>
      intro x y z hs
      obtain ⟨i, hi⟩ := (BaseThree.support_enumeration x y z).mp hs
      have hp := BaseThree.point_supported i
      simpa only [Script.tensor, BaseThree.flagged, hi] using hp
  | step prior center m ih =>
      exact completion_unit_coefficients (Script.tensor BaseThree.flagged prior)
        ih center m

def tensor := CompletionTermination.tensor completed .A

theorem tensor_unit_coefficients (x y z) (hs : tensor x y z ≠ 0) :
    tensor x y z = 1 := by
  have h := (CompletionTermination.support_iff completed .A x y z).mp hs
  rw [tensor, CompletionTermination.tensor, ite_eq_right h.2]
  exact script_unit_coefficients Script.square x y z h.1

abbrev Leaf := CompletionTermination.Leaf completed .A

def retainedLeafEquiv : Leaf ≃ RetainedLeaf completed .B .C :=
  CompletionTermination.retainedLeafEquiv completed .A .B .C
    (by intro c; cases c <;> simp)

@[simp] theorem retainedLeafEquiv_coordinates (a : Leaf) :
    (retainedLeafEquiv a).val.val = a.val := rfl

def leafCount : ℕ := 2995461856366867388223311649574852466276480577

theorem leafCount_pos : 0 < leafCount := by norm_num [leafCount]

theorem card_termination_A {X Y Z : Type uCoord} [Fintype X] [Fintype Y] [Fintype Z]
    (S : FlaggedTensor X Y Z) :
    Fintype.card (CompletionTermination.Leaf S .A) =
      conditionalCount S .B + conditionalCount S .C := by
  rw [Fintype.card_congr (CompletionTermination.leafEquiv S .A)]
  simp only [conditionalCount, Fintype.card_subtype, Finset.card_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  cases leafColor S a <;> simp

theorem card_leaf : Fintype.card Leaf = leafCount := by
  rw [card_termination_A, completed, conditionalCount_script, conditionalCount_script]
  norm_num [counts, initialCount, Script.square, leafCount, reduceCtorEq]

instance leafNonempty : Nonempty Leaf :=
  Fintype.card_pos_iff.mp (by rw [card_leaf]; exact leafCount_pos)

def uniformLaw : FiniteLaw Leaf := FiniteLaw.uniform Leaf

theorem uniformLaw_mass (a : Leaf) : uniformLaw.mass a = (leafCount : ℝ)⁻¹ := by
  simp [uniformLaw, card_leaf]

theorem uniformLaw_pos (a : Leaf) : 0 < uniformLaw.mass a := by
  rw [uniformLaw_mass]
  exact inv_pos.mpr (Nat.cast_pos.mpr leafCount_pos)

theorem uniformLaw_entropy : finiteEntropy uniformLaw.mass = Real.log leafCount := by
  rw [uniformLaw, FiniteLaw.uniform_entropy, card_leaf]

def leafMultiplicity (_ : Leaf) : ℕ := 1

theorem totalMultiplicity : (∑ a : Leaf, leafMultiplicity a) = leafCount := by
  exact (Finset.card_eq_sum_ones (Finset.univ : Finset Leaf)).symm.trans card_leaf

theorem totalMultiplicity_pos : 0 < ∑ a : Leaf, leafMultiplicity a := by
  rw [totalMultiplicity]
  exact leafCount_pos

theorem uniformLaw_mass_counts (a : Leaf) :
    uniformLaw.mass a = (leafMultiplicity a : ℝ) /
      (∑ b : Leaf, leafMultiplicity b : ℕ) := by
  rw [uniformLaw_mass, totalMultiplicity]
  simp [leafMultiplicity, one_div]

def retainedUniformLaw : FiniteLaw (RetainedLeaf completed .B .C) :=
  uniformLaw.map retainedLeafEquiv

theorem retainedUniformLaw_mass (a : RetainedLeaf completed .B .C) :
    retainedUniformLaw.mass a = (leafCount : ℝ)⁻¹ := by
  have h := uniformLaw.map_mass_apply retainedLeafEquiv retainedLeafEquiv.injective
    (retainedLeafEquiv.symm a)
  simpa only [retainedUniformLaw, Equiv.apply_symm_apply, uniformLaw_mass] using h

theorem retainedUniformLaw_entropy :
    finiteEntropy retainedUniformLaw.mass = Real.log leafCount := by
  rw [retainedUniformLaw, FiniteLaw.map_entropy_of_injective uniformLaw
    retainedLeafEquiv retainedLeafEquiv.injective, uniformLaw_entropy]

theorem uniform_pairRate_sum {Label : ℕ → Type*} [∀ n, Fintype (Label n)]
    (labels : ∀ n, Leaf → Label n) (depth : ℕ)
    (reader : Fin depth → ReaderPair)
    (complete : Function.Injective (labelRecordOf labels depth)) :
    ConditionalLabels.lawPairingRate uniformLaw labels depth reader .xy +
      ConditionalLabels.lawPairingRate uniformLaw labels depth reader .xz +
      ConditionalLabels.lawPairingRate uniformLaw labels depth reader .yz =
        Real.log leafCount := by
  rw [ConditionalLabels.lawPairingRate_sum uniformLaw labels depth reader complete,
    uniformLaw_entropy]

def approximation :
    Tensor.PolynomialApproximation tensor (3 ^ 72)
      (Script.order 5 Script.square) (Script.degree 15 Script.square) :=
  CompletionTermination.approximation completed .A
    (Script.approximation BaseThree.flagged BaseThree.approximation Script.square)

theorem rank_power (n : ℕ) :
    Tensor.RankAtMost (Tensor.power tensor n)
      ((Script.degree 15 Script.square * n + 1) * (3 ^ 72) ^ n) :=
  approximation.rank_power n

end MatrixMultiplication.SquareCounts

end

end OAI
