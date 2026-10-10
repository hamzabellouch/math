import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.CanonicalCW
import Mathlib.Tactic.FinCases

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

namespace MatrixMultiplication.JointCanonicalInitial

open MatrixMultiplication.Foundation JointPopulation JointCanonicalization JointCanonicalCW
open InheritedMasks CWStrands
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H F : Type*} [Fintype H] [DecidableEq H] [CommRing F]
    (counts : H → Shape → ℕ)

abbrev Word := Fin 8 → Fin 7
abbrev RawWords := ∀ h, Positions counts h → Word
abbrev CanonicalWords := ∀ c : ClassKey (H := H), ClassPositions counts c → Word

def wholeEquiv (e : Target counts) : RawWords counts ≃ CanonicalWords counts where
  toFun w := fun c j => w c.1 ((positionEquiv counts e c.1).symm ⟨c.2, j⟩)
  invFun w := fun h i => w (h, (e h).val i) (positionEquiv counts e h i).2
  left_inv w := by
    funext h i
    change w h ((positionEquiv counts e h).symm (positionEquiv counts e h i)) = w h i
    simp
  right_inv w := by
    funext c j
    exact congrArg (fun p : Σ u, Fin (counts c.1 u) => w (c.1, p.1) p.2)
      ((positionEquiv counts e c.1).apply_symm_apply ⟨c.2, j⟩)

def rawSource : Tensor F (RawWords counts) (RawWords counts) (RawWords counts) :=
  classProduct (fun _ : H => strand (Fin 8))

def coarseWord (w : RawWords counts) : Position counts → Fin 17 :=
  fun i => CWCoarseIndices.coarseIndex (by simp) (w i.1 i.2)

def ideal (e : Target counts) : Tensor F (RawWords counts) (RawWords counts)
    (RawWords counts) :=
  JointIdealBranches.ideal (rawSource counts) (coarseWord counts) (coarseWord counts)
    (coarseWord counts) (fun _ _ => True) (fun _ _ => True) (fun _ _ => True)
    (triple counts e)

def canonical : Tensor F (CanonicalWords counts) (CanonicalWords counts)
    (CanonicalWords counts) :=
  classProduct (fun c : ClassKey (H := H) => shapeTensor (Fin 8) (shapeNat c.2))

omit [DecidableEq H] in
theorem canonical_pack (e : Target counts) (x y z : RawWords counts) :
    canonical counts (wholeEquiv counts e x) (wholeEquiv counts e y)
      (wholeEquiv counts e z) =
      ∏ h, ∏ i, shapeTensor (F := F) (Fin 8) (shapeNat ((e h).val i))
        (x h i) (y h i) (z h i) := by
  unfold canonical classProduct
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro h _
  rw [← Fintype.prod_sigma']
  apply Fintype.prod_equiv (positionEquiv counts e h).symm
  intro i
  simp only [wholeEquiv, Equiv.coe_fn_mk, positionEquiv_symm_shape]

omit [DecidableEq H] in
theorem ideal_eq_canonical (e : Target counts) (x y z : RawWords counts) :
    ideal (F := F) counts e x y z = canonical counts (wholeEquiv counts e x)
      (wholeEquiv counts e y) (wholeEquiv counts e z) := by
  rw [canonical_pack]
  simp only [ideal, JointIdealBranches.ideal, ExactRecovery.delete, and_true,
    rawSource, classProduct, shapeTensor, Fintype.prod_ite_zero, forall_and]
  congr 1
  simp [coarseWord, triple, shapeNat, shapeSide, CWCoarseIndices.coarseIndex,
    funext_iff, Fin.ext_iff, Sigma.forall]

def coordinateMatrix (e : Target counts) : CanonicalWords counts → RawWords counts → F :=
  fun x v => if v = (wholeEquiv counts e).symm x then 1 else 0

theorem ideal_restrict (e : Target counts) :
    Tensor.restrict (coordinateMatrix (F := F) counts e) (coordinateMatrix counts e)
      (coordinateMatrix counts e) (ideal counts e) = canonical counts := by
  funext x y z
  simp only [Tensor.restrict, coordinateMatrix]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, one_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  rw [ideal_eq_canonical]
  simp

omit [DecidableEq H] in
theorem coarse_support (x y z : RawWords counts)
    (hT : rawSource (F := F) counts x y z ≠ 0) (i : Position counts) :
    (coarseWord counts x i).val + (coarseWord counts y i).val +
      (coarseWord counts z i).val = 16 := by
  have hh : strand (F := F) (Fin 8) (x i.1 i.2) (y i.1 i.2) (z i.1 i.2) ≠ 0 := by
    intro hz
    apply hT
    unfold rawSource classProduct
    apply Finset.prod_eq_zero (Finset.mem_univ i.1)
    exact Finset.prod_eq_zero (Finset.mem_univ i.2) hz
  simpa [coarseWord] using
    CWCoarseIndices.strand_coarse_support (F := F) (by simp)
      (x i.1 i.2) (y i.1 i.2) (z i.1 i.2) hh

def sideMask (s : Fin 3) (w : RawWords counts) : Prop :=
  ∀ h a, wordPopulation (fun i => coarseWord counts w ⟨h, i⟩) a =
    wordPopulation (sideWord counts s (triple counts (canonicalTarget counts)) h) a

def maskedSource : Tensor F (RawWords counts) (RawWords counts) (RawWords counts) :=
  ExactRecovery.delete (rawSource counts) (sideMask counts 0) (sideMask counts 1)
    (sideMask counts 2)

omit [Fintype H] [DecidableEq H] in
theorem sideMask_of_target (s : Fin 3) (e : Target counts) (w : RawWords counts)
    (he : coarseWord counts w =
      fun i => sideWord counts s (triple counts e) i.1 i.2) :
    sideMask counts s w := by
  intro h a
  rw [he]
  exact marginal_population_eq counts e (canonicalTarget counts) h s a

theorem maskedSource_support (x y z : RawWords counts)
    (hT : maskedSource (F := F) counts x y z ≠ 0) :
    (coarseWord counts x, coarseWord counts y, coarseWord counts z) ∈
      ambientSet counts (fun _ => 16) := by
  have hm : sideMask counts 0 x ∧ sideMask counts 1 y ∧ sideMask counts 2 z := by
    by_contra hn
    simp [maskedSource, ExactRecovery.delete, hn] at hT
  have hr : rawSource (F := F) counts x y z ≠ 0 := by
    simpa [maskedSource, ExactRecovery.delete, hm] using hT
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · intro i
    exact coarse_support counts x y z hr i
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
theorem ideal_support_masks (e : Target counts) (x y z : RawWords counts)
    (hT : ideal (F := F) counts e x y z ≠ 0) :
    sideMask counts 0 x ∧ sideMask counts 1 y ∧ sideMask counts 2 z := by
  have hc : coarseWord counts x = (triple counts e).1 ∧
      coarseWord counts y = (triple counts e).2.1 ∧
      coarseWord counts z = (triple counts e).2.2 := by
    by_contra hn
    simp [ideal, JointIdealBranches.ideal, ExactRecovery.delete, hn] at hT
  constructor
  · apply sideMask_of_target counts 0 e x
    simpa [sideWord, shapeSide] using hc.1
  constructor
  · apply sideMask_of_target counts 1 e y
    simpa [sideWord, shapeSide] using hc.2.1
  · apply sideMask_of_target counts 2 e z
    simpa [sideWord, shapeSide] using hc.2.2

omit [DecidableEq H] in
theorem delete_ideal_eq (e : Target counts) :
    ExactRecovery.delete (ideal (F := F) counts e) (sideMask counts 0)
      (sideMask counts 1) (sideMask counts 2) = ideal counts e := by
  funext x y z
  by_cases h : ideal (F := F) counts e x y z = 0
  · rw [ExactRecovery.delete, h]
    simp
  · rw [ExactRecovery.delete, ite_eq_left (ideal_support_masks counts e x y z h)]

end MatrixMultiplication.JointCanonicalInitial

end

end OAI
