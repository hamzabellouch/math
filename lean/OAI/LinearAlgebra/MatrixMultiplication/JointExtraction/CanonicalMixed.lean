import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.CanonicalCW
import Mathlib.Tactic.FinCases

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

namespace MatrixMultiplication.JointCanonicalMixed

open MatrixMultiplication.Foundation JointPopulation JointCanonicalization JointCanonicalCW
open CWStrands HistorySymmetry InheritedMasks
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H F : Type*} [Fintype H] [DecidableEq H] [CommRing F]
    (counts : H → Shape → ℕ) (leftLength rightLength : H → ℕ)
    (parentShape : H → Fin 3 → ℕ) (sharing : H → Bool)
    (hleft : ∀ h, leftLength h ≤ 8)

def inputTensor (h : H) : Tensor F
    (Left leftLength h × Right rightLength h)
    (Left leftLength h × Right rightLength h)
    (Left leftLength h × Right rightLength h) :=
  if sharing h then parentTensor leftLength rightLength parentShape h
  else Tensor.product (strand (Fin (leftLength h))) (strand (Fin (rightLength h)))

def childRight (c : ClassKey (H := H)) :
    Tensor F (Right rightLength c.1) (Right rightLength c.1) (Right rightLength c.1) :=
  if sharing c.1 then rightTensor rightLength parentShape c
  else strand (Fin (rightLength c.1))

omit [Fintype H] [DecidableEq H] in
theorem block_eq_children (h : H) (u : Shape)
    (hu : sharing h = true → ∀ s, shapeNat u s ≤ parentShape h s) :
    block (Left leftLength) (Right rightLength)
      (inputTensor leftLength rightLength parentShape sharing)
      (coarse leftLength rightLength hleft) (h, u) =
      Tensor.product (leftTensor (F := F) leftLength (h, u))
        (childRight rightLength parentShape sharing (h, u)) := by
  by_cases hs : sharing h = true
  · funext x y z
    have hh := congrFun (congrFun (congrFun
      (block_eq_product (F := F) leftLength rightLength parentShape hleft h u (hu hs)) x) y) z
    simpa only [block, inputTensor, childRight, hs, ↓reduceIte] using hh
  · funext x y z
    simp [block, inputTensor, childRight, hs, leftTensor, shapeTensor,
      coarse, CWCoarseIndices.coarseIndex, Fin.ext_iff, shapeNat, shapeSide,
      Tensor.product, ite_mul]

omit [DecidableEq H] in
theorem canonicalBase_eq_children
    (hsupport : ∀ h u, 0 < counts h u → sharing h = true →
      ∀ s, shapeNat u s ≤ parentShape h s) :
    canonicalBase counts (Left leftLength) (Right rightLength)
      (inputTensor leftLength rightLength parentShape sharing)
      (coarse leftLength rightLength hleft) =
      pairClassProduct (leftTensor (F := F) leftLength)
        (childRight rightLength parentShape sharing) := by
  funext x y z
  unfold canonicalBase
  have hf : (∏ c : ClassKey (H := H), ∏ j : ClassPositions counts c,
      block (Left leftLength) (Right rightLength)
        (inputTensor leftLength rightLength parentShape sharing)
        (coarse leftLength rightLength hleft) c
        (x.left c j, x.right c j) (y.left c j, y.right c j) (z.left c j, z.right c j)) =
      ∏ c : ClassKey (H := H), ∏ j : ClassPositions counts c,
        (leftTensor (F := F) leftLength c (x.left c j) (y.left c j) (z.left c j) *
          childRight rightLength parentShape sharing c
            (x.right c j) (y.right c j) (z.right c j)) := by
    apply Finset.prod_congr rfl
    intro c _
    apply Finset.prod_congr rfl
    intro j _
    have hc : 0 < counts c.1 c.2 := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
    rw [block_eq_children leftLength rightLength parentShape sharing hleft c.1 c.2
      (hsupport c.1 c.2 hc)]
    rfl
  rw [hf]
  simp only [pairClassProduct, classProduct, Finset.prod_mul_distrib]

def rawSource : Tensor F (RawStrands counts leftLength rightLength)
    (RawStrands counts leftLength rightLength) (RawStrands counts leftLength rightLength) :=
  classProduct (fun h => if sharing h then
    shapeTensor (Fin (leftLength h) ⊕ Fin (rightLength h)) (parentShape h)
    else strand (Fin (leftLength h) ⊕ Fin (rightLength h)))

theorem inputTensor_restrict :
    Tensor.restrict (joinMatrix (F := F) counts leftLength rightLength)
      (joinMatrix counts leftLength rightLength) (joinMatrix counts leftLength rightLength)
      (rawSource counts leftLength rightLength parentShape sharing) =
      sourceTensor counts (Left leftLength) (Right rightLength)
        (inputTensor leftLength rightLength parentShape sharing) := by
  classical
  funext x y z
  simp only [Tensor.restrict, joinMatrix]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, one_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  unfold rawSource sourceTensor classProduct inputTensor
  apply Finset.prod_congr rfl
  intro h _
  apply Finset.prod_congr rfl
  intro i _
  by_cases hs : sharing h = true
  · simp [hs, joinWords, parentTensor]
  · simp [hs, joinWords, strand_sum_elim]

omit [Fintype H] [DecidableEq H] in
theorem coarse_support (h : H)
    (x y z : Left leftLength h × Right rightLength h)
    (hT : inputTensor (F := F) leftLength rightLength parentShape sharing h x y z ≠ 0) :
    (coarse leftLength rightLength hleft 0 h x).val +
      (coarse leftLength rightLength hleft 1 h y).val +
      (coarse leftLength rightLength hleft 2 h z).val = 2 * leftLength h := by
  by_cases hs : sharing h = true
  · have hp : parentTensor (F := F) leftLength rightLength parentShape h x y z ≠ 0 := by
      simpa [inputTensor, hs] using hT
    have hh := CWCoarseIndices.split_coarse_support
      (F := F) (by simpa using hleft h) (parentShape h) x y z hp
    simpa only [coarse, Fintype.card_fin] using hh.1
  · have ht : strand (F := F) (Fin (leftLength h)) x.1 y.1 z.1 ≠ 0 := by
      intro hz
      apply hT
      simp [inputTensor, hs, Tensor.product, hz]
    simpa only [coarse, Fintype.card_fin] using
      CWCoarseIndices.strand_coarse_support (F := F) (by simpa using hleft h) x.1 y.1 z.1 ht

theorem typeWindow_zero_one {P A : Type*} [Fintype P] [DecidableEq P]
    [Fintype A] [DecidableEq A] (w : P → A) : typeWindow (fun _ => 0) 1 w := by
  intro a
  dsimp [empiricalLaw]
  have h0 : (0 : ℝ) ≤ (wordPopulation w a : ℝ) / Fintype.card P := by positivity
  rw [sub_zero, abs_of_nonneg h0]
  by_cases hp : Fintype.card P = 0
  · simp [hp]
  · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hp)).2
    exact_mod_cast (Fintype.card_subtype_le (fun i : P => w i = a))

abbrev MixedWords := RawPairs counts (Left leftLength) (Right rightLength)

def coarseWord (w : MixedWords counts leftLength rightLength) : Position counts → Fin 17 :=
  JointCanonicalization.coarseWord counts (Left leftLength) (Right rightLength)
    (coarse leftLength rightLength hleft) 0 w

def sideMask (s : Fin 3) (w : MixedWords counts leftLength rightLength) : Prop :=
  ∀ h a, wordPopulation (fun i => coarseWord counts leftLength rightLength hleft w ⟨h, i⟩) a =
    wordPopulation (sideWord counts s (triple counts (canonicalTarget counts)) h) a

def maskedSource : Tensor F (MixedWords counts leftLength rightLength)
    (MixedWords counts leftLength rightLength) (MixedWords counts leftLength rightLength) :=
  ExactRecovery.delete
    (sourceTensor counts (Left leftLength) (Right rightLength)
      (inputTensor leftLength rightLength parentShape sharing))
    (sideMask counts leftLength rightLength hleft 0)
    (sideMask counts leftLength rightLength hleft 1)
    (sideMask counts leftLength rightLength hleft 2)

omit [Fintype H] [DecidableEq H] in
theorem sideMask_of_target (s : Fin 3) (e : Target counts)
    (w : MixedWords counts leftLength rightLength)
    (he : coarseWord counts leftLength rightLength hleft w =
      fun i => sideWord counts s (triple counts e) i.1 i.2) :
    sideMask counts leftLength rightLength hleft s w := by
  intro h a
  rw [he]
  exact marginal_population_eq counts e (canonicalTarget counts) h s a

theorem maskedSource_support (x y z : MixedWords counts leftLength rightLength)
    (hT : maskedSource (F := F) counts leftLength rightLength parentShape sharing hleft x y z ≠ 0) :
    (coarseWord counts leftLength rightLength hleft x,
      coarseWord counts leftLength rightLength hleft y,
      coarseWord counts leftLength rightLength hleft z) ∈
      ambientSet counts (fun h => 2 * leftLength h) := by
  have hm : sideMask counts leftLength rightLength hleft 0 x ∧
      sideMask counts leftLength rightLength hleft 1 y ∧
      sideMask counts leftLength rightLength hleft 2 z := by
    by_contra hn
    simp [maskedSource, ExactRecovery.delete, hn] at hT
  have hr : sourceTensor counts (Left leftLength) (Right rightLength)
      (inputTensor (F := F) leftLength rightLength parentShape sharing) x y z ≠ 0 := by
    simpa [maskedSource, ExactRecovery.delete, hm] using hT
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · intro i
    have hi : inputTensor (F := F) leftLength rightLength parentShape sharing i.1
        (x i.1 i.2) (y i.1 i.2) (z i.1 i.2) ≠ 0 := by
      intro hz
      apply hr
      unfold sourceTensor classProduct
      apply Finset.prod_eq_zero (Finset.mem_univ i.1)
      exact Finset.prod_eq_zero (Finset.mem_univ i.2) hz
    exact coarse_support leftLength rightLength parentShape sharing hleft i.1
      (x i.1 i.2) (y i.1 i.2) (z i.1 i.2) hi
  · intro h s a
    fin_cases s
    · refine Eq.trans ?_ (hm.1 h a)
      apply congrArg (fun v : Positions counts h → Fin 17 => wordPopulation v a)
      funext i
      simp [sideWord, shapeSide]
    · refine Eq.trans ?_ (hm.2.1 h a)
      apply congrArg (fun v : Positions counts h → Fin 17 => wordPopulation v a)
      funext i
      simp [sideWord, shapeSide]
    · refine Eq.trans ?_ (hm.2.2 h a)
      apply congrArg (fun v : Positions counts h → Fin 17 => wordPopulation v a)
      funext i
      simp [sideWord, shapeSide]

omit [DecidableEq H] in
theorem coarseIdeal_support_masks (e : Target counts)
    (x y z : MixedWords counts leftLength rightLength)
    (hT : coarseIdeal counts (Left leftLength) (Right rightLength)
      (inputTensor (F := F) leftLength rightLength parentShape sharing)
      (coarse leftLength rightLength hleft) e x y z ≠ 0) :
    sideMask counts leftLength rightLength hleft 0 x ∧
      sideMask counts leftLength rightLength hleft 1 y ∧
      sideMask counts leftLength rightLength hleft 2 z := by
  have hc : coarseMask counts (Left leftLength) (Right rightLength)
      (coarse leftLength rightLength hleft) 0 e x ∧
      coarseMask counts (Left leftLength) (Right rightLength)
        (coarse leftLength rightLength hleft) 1 e y ∧
      coarseMask counts (Left leftLength) (Right rightLength)
        (coarse leftLength rightLength hleft) 2 e z := by
    by_contra hn
    simp [coarseIdeal, ExactRecovery.delete, hn] at hT
  constructor
  · apply sideMask_of_target counts leftLength rightLength hleft 0 e x
    funext i
    exact hc.1 i.1 i.2
  constructor
  · apply sideMask_of_target counts leftLength rightLength hleft 1 e y
    funext i
    exact hc.2.1 i.1 i.2
  · apply sideMask_of_target counts leftLength rightLength hleft 2 e z
    funext i
    exact hc.2.2 i.1 i.2

omit [DecidableEq H] in
theorem ideal_support_masks (e : Target counts)
    (px py pz : MixedWords counts leftLength rightLength → Prop)
    (x y z : MixedWords counts leftLength rightLength)
    (hT : ExactRecovery.delete
      (coarseIdeal counts (Left leftLength) (Right rightLength)
        (inputTensor (F := F) leftLength rightLength parentShape sharing)
        (coarse leftLength rightLength hleft) e) px py pz x y z ≠ 0) :
    sideMask counts leftLength rightLength hleft 0 x ∧
      sideMask counts leftLength rightLength hleft 1 y ∧
      sideMask counts leftLength rightLength hleft 2 z := by
  apply coarseIdeal_support_masks (F := F) counts leftLength rightLength parentShape sharing hleft e x y z
  intro hz
  simp [ExactRecovery.delete, hz] at hT

omit [DecidableEq H] in
theorem delete_ideal_eq (e : Target counts)
    (px py pz : MixedWords counts leftLength rightLength → Prop) :
    let Q := ExactRecovery.delete
      (coarseIdeal counts (Left leftLength) (Right rightLength)
        (inputTensor (F := F) leftLength rightLength parentShape sharing)
        (coarse leftLength rightLength hleft) e) px py pz
    ExactRecovery.delete Q (sideMask counts leftLength rightLength hleft 0)
      (sideMask counts leftLength rightLength hleft 1)
      (sideMask counts leftLength rightLength hleft 2) = Q := by
  dsimp only
  funext x y z
  by_cases h : ExactRecovery.delete
      (coarseIdeal counts (Left leftLength) (Right rightLength)
        (inputTensor (F := F) leftLength rightLength parentShape sharing)
        (coarse leftLength rightLength hleft) e) px py pz x y z = 0
  · rw [ExactRecovery.delete, h]
    simp
  · have hm := ideal_support_masks (F := F) counts leftLength rightLength parentShape sharing hleft
      e px py pz x y z h
    rw [ExactRecovery.delete, ite_eq_left hm]

end MatrixMultiplication.JointCanonicalMixed

end

end OAI
