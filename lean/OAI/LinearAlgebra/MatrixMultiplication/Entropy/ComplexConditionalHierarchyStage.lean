import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPrefixSeparationPolynomialStage
import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialKernelExecution
import OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexStageHierarchyResources
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexConditionalPrefixWords

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.Foundation.ConditionalHierarchyStage

open Tensor PolynomialLocalConstruction PolynomialKernelExecution
open PrefixSeparationPolynomialStage LabelHierarchySeparation

variable {Prefix RawLabel X Y Z : Type*} [DecidableEq RawLabel]

def decodePool (pool : Prefix → Finset RawLabel) (k : ℕ)
    (counts : ∀ p, (pool p).card = k) (p : Prefix) (q : Fin k) : RawLabel :=
  ((poolEnumeration pool k counts p).symm q).val

omit [DecidableEq RawLabel] in
theorem decodePool_mem (pool : Prefix → Finset RawLabel) (k : ℕ)
    (counts : ∀ p, (pool p).card = k) (p : Prefix) (q : Fin k) :
    decodePool pool k counts p q ∈ pool p :=
  ((poolEnumeration pool k counts p).symm q).property

theorem decodePool_eq_iff (pool : Prefix → Finset RawLabel) (k : ℕ)
    (positive : 0 < k) (counts : ∀ p, (pool p).card = k)
    (p : Prefix) (q : Fin k) (s : RawLabel) :
    decodePool pool k counts p q = s ↔
      s ∈ pool p ∧ q = maskedPoolCode pool k positive counts p s := by
  classical
  constructor
  · intro h
    have hs : s ∈ pool p := h ▸ decodePool_mem pool k counts p q
    refine ⟨hs, ?_⟩
    have hsub : (poolEnumeration pool k counts p).symm q = ⟨s, hs⟩ :=
      Subtype.ext h
    have hcode := congrArg (poolEnumeration pool k counts p) hsub
    simpa [maskedPoolCode, hs] using hcode
  · rintro ⟨hs, rfl⟩
    exact maskedPoolCode_decode pool k positive counts p s hs

def decodedLeading (pool : Prefix → Finset RawLabel) (k : ℕ)
    (counts : ∀ p, (pool p).card = k)
    (fine : Prefix → X → Y → Z → RawLabel) (p : Prefix) :
    Tensor ℂ (X × InformedOutput k) (Y × InformedOutput k)
      (Z × MissingOutput k) := by
  classical
  exact fun x y z => if
    x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
      decodePool pool k counts p x.2.1 = fine p x.1 y.1 z.1 ∧ x.2.2 = y.2.2
    then 1 else 0

theorem rawPoolLeading_eq_decodedLeading (pool : Prefix → Finset RawLabel) (k : ℕ)
    (positive : 0 < k) (counts : ∀ p, (pool p).card = k)
    (readX : Prefix → X → RawLabel) (readY : Prefix → Y → RawLabel)
    (fine : Prefix → X → Y → Z → RawLabel) (p : Prefix)
    (x : X × InformedOutput k) (y : Y × InformedOutput k) (z : Z × MissingOutput k)
    (hx : readX p x.1 = fine p x.1 y.1 z.1)
    (hy : readY p y.1 = fine p x.1 y.1 z.1) :
    rawPoolLeading pool k positive counts readX readY p x y z =
      decodedLeading pool k counts fine p x y z := by
  classical
  unfold rawPoolLeading stageLeading decodedLeading
  simp only [hx, hy]
  congr 1
  apply propext
  constructor
  · rintro ⟨⟨hmem, hxc⟩, ⟨_, hyc⟩, _, hcz, hij⟩
    exact ⟨hxc.trans hyc.symm, hxc.trans hcz,
      (decodePool_eq_iff pool k positive counts p x.2.1 _).mpr ⟨hmem, hxc⟩, hij⟩
  · rintro ⟨hxy, hxz, hdecode, hij⟩
    obtain ⟨hmem, hxc⟩ := (decodePool_eq_iff pool k positive counts p x.2.1 _).mp hdecode
    exact ⟨⟨hmem, hxc⟩, ⟨hmem, hxy.symm.trans hxc⟩, trivial,
      hxc.symm.trans hxz, hij⟩

section ExecutionStage

variable {PX PY PZ AX AY AZ : Type*}
variable [Fintype AX] [Fintype AY] [Fintype AZ]
variable {support : X → Y → Z → Prop}

theorem exists_rawPoolStage
    (E : Execution X Y Z Prefix PX PY PZ AX AY AZ support)
    (pool : Prefix → Finset RawLabel) (k : ℕ) (positive : 0 < k)
    (counts : ∀ p, (pool p).card = k)
    (readX : Prefix → X → RawLabel) (readY : Prefix → Y → RawLabel)
    (eligible : Prefix → X → Y → Z → Prop)
    (previous : ∀ x y z, support x.1 y.1 z.1 → E.value x y z ≠ 0 →
      eligible x.2.1 x.1 y.1 z.1)
    (agree : ∀ p x y z, eligible p x y z → readX p x = readY p y) :
    ∃ S : Stage E (Fin k) (Fin k) (Fin k) PUnit
        (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k),
      S.auxiliary = poolAuxiliaryTensor k ∧
      S.rankBound = poolAuxiliaryCost k ∧ S.order = 0 ∧
      S.leftDegree = 0 ∧ S.middleDegree = 0 ∧ S.rightDegree = 0 ∧
      S.value = rawPoolLeading pool k positive counts readX readY := by
  classical
  obtain ⟨MX, MY, MZ, hMX, hMY, hMZ, hkernel⟩ :=
    exists_raw_pool_stage pool k positive counts readX readY eligible agree
  let S : Stage E (Fin k) (Fin k) (Fin k) PUnit
      (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) := {
    auxiliary := poolAuxiliaryTensor k
    rankBound := poolAuxiliaryCost k
    auxiliary_rank := poolAuxiliaryTensor_rankAtMost k
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
    value := rawPoolLeading pool k positive counts readX readY
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
          maskedPoolCode pool k positive counts p (readY p y.1) := congrArg _ hread
      have hsync := stageLeading_synchronized k _ _ _ _ _ p x y z hcodes hn
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

def actualPool
    (priorWord : Prefix → ExactPrefix counts labels n t Position) :
    Prefix → Finset (Position → Label n) :=
  fun p => conditionalFinset (priorWord p)

theorem actualPool_card
    (priorWord : Prefix → ExactPrefix counts labels n t Position) (p : Prefix) :
    (actualPool counts labels n t priorWord p).card = stageRefinementCount counts labels n t :=
  conditionalFinset_card (priorWord p)

def nextPrefixDecoder
    (priorWord : Prefix → ExactPrefix counts labels n t Position) :
    Prefix × Fin (stageRefinementCount counts labels n t) →
      ExactPrefix counts labels (n + 1) t Position :=
  fun p => appendCode (priorWord p.1) p.2

theorem nextPrefixDecoder_injective
    (priorWord : Prefix → ExactPrefix counts labels n t Position)
    (hinj : Function.Injective priorWord) :
    Function.Injective (nextPrefixDecoder counts labels n t priorWord) := by
  intro p q hpq
  have h : (priorWord p.1, p.2) = (priorWord q.1, q.2) := by
    apply appendCode_injective
    exact hpq
  obtain ⟨hprior, hcode⟩ := Prod.mk.inj h
  exact Prod.ext (hinj hprior) hcode

theorem nextPrefixDecoder_surjective
    (priorWord : Prefix → ExactPrefix counts labels n t Position)
    (hsurj : Function.Surjective priorWord) :
    Function.Surjective (nextPrefixDecoder counts labels n t priorWord) := by
  intro next
  obtain ⟨⟨old, code⟩, hnext⟩ := appendCode_surjective next
  obtain ⟨p, hp⟩ := hsurj old
  exact ⟨(p, code), by simpa only [nextPrefixDecoder, hp] using hnext⟩

theorem nextPrefixDecoder_val
    (priorWord : Prefix → ExactPrefix counts labels n t Position)
    (p : Prefix) (q : Fin (stageRefinementCount counts labels n t)) (i : Position) :
    (nextPrefixDecoder counts labels n t priorWord (p, q)).val i =
      ((priorWord p).val i,
        decodePool (actualPool counts labels n t priorWord)
          (stageRefinementCount counts labels n t)
          (actualPool_card counts labels n t priorWord) p q i) := rfl

theorem surviving_nextPrefix
    (priorWord : Prefix → ExactPrefix counts labels n t Position)
    (readX : Prefix → X → Position → Label n)
    (readY : Prefix → Y → Position → Label n)
    (p : Prefix) (word : Position → A)
    (x : X × InformedOutput (stageRefinementCount counts labels n t))
    (y : Y × InformedOutput (stageRefinementCount counts labels n t))
    (z : Z × MissingOutput (stageRefinementCount counts labels n t))
    (hprior : ∀ i, (priorWord p).val i = labelRecordOf labels n (word i))
    (hx : readX p x.1 = fun i => labels n (word i))
    (hy : readY p y.1 = fun i => labels n (word i))
    (hn : rawPoolLeading (actualPool counts labels n t priorWord)
      (stageRefinementCount counts labels n t) (stageRefinementCount_pos counts labels n t)
      (actualPool_card counts labels n t priorWord) readX readY p x y z ≠ 0) :
    ∀ i, (nextPrefixDecoder counts labels n t priorWord (p, x.2.1)).val i =
      labelRecordOf labels (n + 1) (word i) := by
  classical
  have heq := rawPoolLeading_eq_decodedLeading
    (actualPool counts labels n t priorWord) (stageRefinementCount counts labels n t)
    (stageRefinementCount_pos counts labels n t) (actualPool_card counts labels n t priorWord)
    readX readY (fun _ _ _ _ => fun i => labels n (word i)) p x y z hx hy
  rw [heq] at hn
  have hdecode : decodePool (actualPool counts labels n t priorWord)
      (stageRefinementCount counts labels n t)
      (actualPool_card counts labels n t priorWord) p x.2.1 =
      fun i => labels n (word i) := by
    by_contra h
    exact hn (by simp [decodedLeading, h])
  intro i
  rw [nextPrefixDecoder_val, hprior, hdecode]
  rfl

theorem exists_actualPoolStage
    {PX PY PZ AX AY AZ : Type*} [Fintype AX] [Fintype AY] [Fintype AZ]
    {support : X → Y → Z → Prop}
    (E : Execution X Y Z Prefix PX PY PZ AX AY AZ support)
    (priorWord : Prefix → ExactPrefix counts labels n t Position)
    (readX : Prefix → X → Position → Label n)
    (readY : Prefix → Y → Position → Label n)
    (eligible : Prefix → X → Y → Z → Prop)
    (previous : ∀ x y z, support x.1 y.1 z.1 → E.value x y z ≠ 0 →
      eligible x.2.1 x.1 y.1 z.1)
    (agree : ∀ p x y z, eligible p x y z → readX p x = readY p y) :
    ∃ S : Stage E (Fin (stageRefinementCount counts labels n t))
        (Fin (stageRefinementCount counts labels n t))
        (Fin (stageRefinementCount counts labels n t)) PUnit
        (PoolAuxiliaryGroup (stageRefinementCount counts labels n t))
        (PoolAuxiliaryGroup (stageRefinementCount counts labels n t))
        (PoolAuxiliaryGroup (stageRefinementCount counts labels n t)),
      S.auxiliary = poolAuxiliaryTensor (stageRefinementCount counts labels n t) ∧
      S.rankBound = stageCost counts labels n t ∧ S.order = 0 ∧
      S.leftDegree = 0 ∧ S.middleDegree = 0 ∧ S.rightDegree = 0 ∧
      S.value = rawPoolLeading (actualPool counts labels n t priorWord)
        (stageRefinementCount counts labels n t) (stageRefinementCount_pos counts labels n t)
        (actualPool_card counts labels n t priorWord) readX readY := by
  exact exists_rawPoolStage E (actualPool counts labels n t priorWord)
    (stageRefinementCount counts labels n t) (stageRefinementCount_pos counts labels n t)
    (actualPool_card counts labels n t priorWord) readX readY eligible previous agree

end ExactConditionalPools

end MatrixMultiplication.Foundation.ConditionalHierarchyStage

end

end OAI
