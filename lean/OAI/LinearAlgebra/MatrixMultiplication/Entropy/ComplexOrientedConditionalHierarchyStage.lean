import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexConditionalHierarchyStage
import OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexPrefixSeparationOrientations

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.Foundation.OrientedConditionalHierarchyStage

open Tensor PolynomialLocalConstruction PolynomialKernelExecution
open PrefixSeparationPolynomialStage PrefixSeparationOrientations LabelHierarchySeparation
open ConditionalHierarchyStage

variable {Prefix RawLabel X Y Z : Type*} [DecidableEq RawLabel]

section ExecutionStage

variable {PX PY PZ AX AY AZ : Type*}
variable [Fintype AX] [Fintype AY] [Fintype AZ]
variable {support : X → Y → Z → Prop}

theorem exists_rawPoolStage_XZ
    (E : Execution X Y Z Prefix PX PY PZ AX AY AZ support)
    (pool : Prefix → Finset RawLabel) (k : ℕ) (positive : 0 < k)
    (counts : ∀ p, (pool p).card = k)
    (readX : Prefix → X → RawLabel) (readZ : Prefix → Z → RawLabel)
    (eligible : Prefix → X → Y → Z → Prop)
    (previous : ∀ x y z, support x.1 y.1 z.1 → E.value x y z ≠ 0 →
      eligible x.2.1 x.1 y.1 z.1)
    (agree : ∀ p x y z, eligible p x y z → readX p x = readZ p z) :
    ∃ S : Stage E (Fin k) (Fin k) PUnit (Fin k)
        (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k),
      S.auxiliary = auxiliaryXZ k ∧
      S.rankBound = poolAuxiliaryCost k ∧ S.order = 0 ∧
      S.leftDegree = 0 ∧ S.middleDegree = 0 ∧ S.rightDegree = 0 ∧
      S.value = rawPoolLeadingXZ pool k positive counts readX readZ := by
  classical
  obtain ⟨MX, MY, MZ, hMX, hMY, hMZ, hkernel⟩ :=
    exists_raw_pool_stage_XZ pool k positive counts readX readZ eligible agree
  let S : Stage E (Fin k) (Fin k) PUnit (Fin k)
      (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) := {
    auxiliary := auxiliaryXZ k
    rankBound := poolAuxiliaryCost k
    auxiliary_rank := auxiliaryXZ_rankAtMost k
    order := 0
    leftDegree := 0
    middleDegree := 0
    rightDegree := 0
    leftMap := MX
    middleMap := MY
    rightMap := MZ
    left_degree := hMX
    middle_degree := hMY
    right_degree := hMZ
    eligible := eligible
    previous_eligible := previous
    value := rawPoolLeadingXZ pool k positive counts readX readZ
    vanishes := by
      intro _ _ _ _ _ j hj
      exact (Nat.not_lt_zero j hj).elim
    leading := by
      intro p x y z he
      rw [hkernel p x y z he]
      exact Polynomial.coeff_C_zero
    synchronized := by
      intro p x y z he hn
      have hread := agree p x.1 y.1 z.1 he
      have hcodes : maskedPoolCode pool k positive counts p (readX p x.1) =
          maskedPoolCode pool k positive counts p (readZ p z.1) := congrArg _ hread
      have hsync := stageLeadingXZ_synchronized k _ _ _ _ _ p x y z hcodes hn
      exact ⟨hsync.1, hsync.2.1⟩
  }
  exact ⟨S, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem exists_rawPoolStage_YZ
    (E : Execution X Y Z Prefix PX PY PZ AX AY AZ support)
    (pool : Prefix → Finset RawLabel) (k : ℕ) (positive : 0 < k)
    (counts : ∀ p, (pool p).card = k)
    (readY : Prefix → Y → RawLabel) (readZ : Prefix → Z → RawLabel)
    (eligible : Prefix → X → Y → Z → Prop)
    (previous : ∀ x y z, support x.1 y.1 z.1 → E.value x y z ≠ 0 →
      eligible x.2.1 x.1 y.1 z.1)
    (agree : ∀ p x y z, eligible p x y z → readY p y = readZ p z) :
    ∃ S : Stage E (Fin k) PUnit (Fin k) (Fin k)
        (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k),
      S.auxiliary = auxiliaryYZ k ∧
      S.rankBound = poolAuxiliaryCost k ∧ S.order = 0 ∧
      S.leftDegree = 0 ∧ S.middleDegree = 0 ∧ S.rightDegree = 0 ∧
      S.value = rawPoolLeadingYZ pool k positive counts readY readZ := by
  classical
  obtain ⟨MX, MY, MZ, hMX, hMY, hMZ, hkernel⟩ :=
    exists_raw_pool_stage_YZ pool k positive counts readY readZ eligible agree
  let S : Stage E (Fin k) PUnit (Fin k) (Fin k)
      (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) := {
    auxiliary := auxiliaryYZ k
    rankBound := poolAuxiliaryCost k
    auxiliary_rank := auxiliaryYZ_rankAtMost k
    order := 0
    leftDegree := 0
    middleDegree := 0
    rightDegree := 0
    leftMap := MX
    middleMap := MY
    rightMap := MZ
    left_degree := hMX
    middle_degree := hMY
    right_degree := hMZ
    eligible := eligible
    previous_eligible := previous
    value := rawPoolLeadingYZ pool k positive counts readY readZ
    vanishes := by
      intro _ _ _ _ _ j hj
      exact (Nat.not_lt_zero j hj).elim
    leading := by
      intro p x y z he
      rw [hkernel p x y z he]
      exact Polynomial.coeff_C_zero
    synchronized := by
      intro p x y z he hn
      have hread := agree p x.1 y.1 z.1 he
      have hcodes : maskedPoolCode pool k positive counts p (readY p y.1) =
          maskedPoolCode pool k positive counts p (readZ p z.1) := congrArg _ hread
      have hsync := stageLeadingYZ_synchronized k _ _ _ _ _ p x y z hcodes hn
      exact ⟨hsync.1, hsync.2.1⟩
  }
  exact ⟨S, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end ExecutionStage

section ExactConditionalPools

open ConditionalPrefixWords StageHierarchyResources LabelHierarchyCounts

variable {A Position : Type*} [Fintype A] [Fintype Position]
variable {Label : ℕ → Type*} [∀ n, Fintype (Label n)]
variable (counts : A → ℕ) (labels : ∀ n, A → Label n) (n t : ℕ)

local instance (priority := low) {B : Type*} : DecidableEq B := Classical.decEq B

theorem exists_actualPoolStage_XZ
    {PX PY PZ AX AY AZ : Type*} [Fintype AX] [Fintype AY] [Fintype AZ]
    {support : X → Y → Z → Prop}
    (E : Execution X Y Z Prefix PX PY PZ AX AY AZ support)
    (priorWord : Prefix → ExactPrefix counts labels n t Position)
    (readX : Prefix → X → Position → Label n)
    (readZ : Prefix → Z → Position → Label n)
    (eligible : Prefix → X → Y → Z → Prop)
    (previous : ∀ x y z, support x.1 y.1 z.1 → E.value x y z ≠ 0 →
      eligible x.2.1 x.1 y.1 z.1)
    (agree : ∀ p x y z, eligible p x y z → readX p x = readZ p z) :
    ∃ S : Stage E (Fin (stageRefinementCount counts labels n t))
        (Fin (stageRefinementCount counts labels n t)) PUnit
        (Fin (stageRefinementCount counts labels n t))
        (PoolAuxiliaryGroup (stageRefinementCount counts labels n t))
        (PoolAuxiliaryGroup (stageRefinementCount counts labels n t))
        (PoolAuxiliaryGroup (stageRefinementCount counts labels n t)),
      S.auxiliary = auxiliaryXZ (stageRefinementCount counts labels n t) ∧
      S.rankBound = stageCost counts labels n t ∧ S.order = 0 ∧
      S.leftDegree = 0 ∧ S.middleDegree = 0 ∧ S.rightDegree = 0 ∧
      S.value = rawPoolLeadingXZ (actualPool counts labels n t priorWord)
        (stageRefinementCount counts labels n t) (stageRefinementCount_pos counts labels n t)
        (actualPool_card counts labels n t priorWord) readX readZ := by
  exact exists_rawPoolStage_XZ E (actualPool counts labels n t priorWord)
    (stageRefinementCount counts labels n t) (stageRefinementCount_pos counts labels n t)
    (actualPool_card counts labels n t priorWord) readX readZ eligible previous agree

theorem exists_actualPoolStage_YZ
    {PX PY PZ AX AY AZ : Type*} [Fintype AX] [Fintype AY] [Fintype AZ]
    {support : X → Y → Z → Prop}
    (E : Execution X Y Z Prefix PX PY PZ AX AY AZ support)
    (priorWord : Prefix → ExactPrefix counts labels n t Position)
    (readY : Prefix → Y → Position → Label n)
    (readZ : Prefix → Z → Position → Label n)
    (eligible : Prefix → X → Y → Z → Prop)
    (previous : ∀ x y z, support x.1 y.1 z.1 → E.value x y z ≠ 0 →
      eligible x.2.1 x.1 y.1 z.1)
    (agree : ∀ p x y z, eligible p x y z → readY p y = readZ p z) :
    ∃ S : Stage E (Fin (stageRefinementCount counts labels n t)) PUnit
        (Fin (stageRefinementCount counts labels n t))
        (Fin (stageRefinementCount counts labels n t))
        (PoolAuxiliaryGroup (stageRefinementCount counts labels n t))
        (PoolAuxiliaryGroup (stageRefinementCount counts labels n t))
        (PoolAuxiliaryGroup (stageRefinementCount counts labels n t)),
      S.auxiliary = auxiliaryYZ (stageRefinementCount counts labels n t) ∧
      S.rankBound = stageCost counts labels n t ∧ S.order = 0 ∧
      S.leftDegree = 0 ∧ S.middleDegree = 0 ∧ S.rightDegree = 0 ∧
      S.value = rawPoolLeadingYZ (actualPool counts labels n t priorWord)
        (stageRefinementCount counts labels n t) (stageRefinementCount_pos counts labels n t)
        (actualPool_card counts labels n t priorWord) readY readZ := by
  exact exists_rawPoolStage_YZ E (actualPool counts labels n t priorWord)
    (stageRefinementCount counts labels n t) (stageRefinementCount_pos counts labels n t)
    (actualPool_card counts labels n t priorWord) readY readZ eligible previous agree

end ExactConditionalPools
end MatrixMultiplication.Foundation.OrientedConditionalHierarchyStage

end

end OAI
