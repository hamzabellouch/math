import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.Population
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.HistorySymmetry
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.IdealBranches
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

namespace MatrixMultiplication.JointCanonicalization

open MatrixMultiplication.Foundation JointPopulation InheritedMasks
open PermutationMatching HistorySymmetry
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H : Type*} (counts : H → Shape → ℕ)

def fiberEquiv (e : Target counts) (h : H) (u : Shape) :
    Class counts e h u ≃ Fin (counts h u) :=
  Fintype.equivOfCardEq (by rw [class_card, Fintype.card_fin])

def positionEquiv (e : Target counts) (h : H) :
    Positions counts h ≃ (Σ u, Fin (counts h u)) :=
  (Equiv.sigmaFiberEquiv (e h).val).symm.trans
    (Equiv.sigmaCongrRight (fiberEquiv counts e h))

@[simp] theorem positionEquiv_shape (e : Target counts) (h : H) (i : Positions counts h) :
    (positionEquiv counts e h i).1 = (e h).val i := rfl

@[simp] theorem positionEquiv_symm_shape (e : Target counts) (h : H)
    (i : Σ u, Fin (counts h u)) :
    (e h).val ((positionEquiv counts e h).symm i) = i.1 := by
  have hh := congrArg Sigma.fst ((positionEquiv counts e h).apply_symm_apply i)
  simpa only [positionEquiv_shape] using hh

abbrev ClassKey := H × Shape
abbrev ClassPositions (c : ClassKey (H := H)) := Fin (counts c.1 c.2)

variable (L R : H → Type*)

abbrev RawPairs := ∀ h, Positions counts h → L h × R h
abbrev CanonicalPairs := CompleteWordPair (ClassPositions counts)
  (fun c => L c.1) (fun c => R c.1)

def pairEquiv (e : Target counts) : RawPairs counts L R ≃ CanonicalPairs counts L R where
  toFun w :=
    { left := fun c j => (w c.1 ((positionEquiv counts e c.1).symm ⟨c.2, j⟩)).1
      right := fun c j => (w c.1 ((positionEquiv counts e c.1).symm ⟨c.2, j⟩)).2 }
  invFun w := fun h i =>
    (w.left (h, (e h).val i) (positionEquiv counts e h i).2,
      w.right (h, (e h).val i) (positionEquiv counts e h i).2)
  left_inv w := by
    funext h i
    change ((w h ((positionEquiv counts e h).symm
      (positionEquiv counts e h i))).1,
      (w h ((positionEquiv counts e h).symm (positionEquiv counts e h i))).2) = w h i
    simp
  right_inv w := by
    cases w with
    | mk wl wr =>
      dsimp only
      congr 1 <;> funext c j
      · exact congrArg (β := L c.1)
          (fun p : Σ u, Fin (counts c.1 u) => wl (c.1, p.1) p.2)
          ((positionEquiv counts e c.1).apply_symm_apply ⟨c.2, j⟩)
      · exact congrArg (β := R c.1)
          (fun p : Σ u, Fin (counts c.1 u) => wr (c.1, p.1) p.2)
          ((positionEquiv counts e c.1).apply_symm_apply ⟨c.2, j⟩)

theorem pairEquiv_fiber_left (e : Target counts) (w : RawPairs counts L R)
    (h : H) (u : Shape) (j : Fin (counts h u)) :
    (pairEquiv counts L R e w).left (h, u) j =
      (w h ((fiberEquiv counts e h u).symm j).val).1 := rfl

theorem pairEquiv_fiber_right (e : Target counts) (w : RawPairs counts L R)
    (h : H) (u : Shape) (j : Fin (counts h u)) :
    (pairEquiv counts L R e w).right (h, u) j =
      (w h ((fiberEquiv counts e h u).symm j).val).2 := rfl

theorem typeWindow_reindex {P Q A : Type*}
    [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q]
    [Fintype A] [DecidableEq A]
    (ν : A → ℝ) (η : ℝ) (w : P → A) (p : Q ≃ P) :
    typeWindow ν η (w ∘ p) ↔ typeWindow ν η w := by
  simp only [typeWindow, empiricalLaw, wordPopulation_reindex, Fintype.card_congr p]

section Windows

variable {SL SR : H → Type*}
    [∀ h, Fintype (SL h)] [∀ h, Fintype (SR h)]
    [∀ h, DecidableEq (SL h)] [∀ h, DecidableEq (SR h)]
    (sl : ∀ c : ClassKey (H := H), L c.1 → SL c.1)
    (sr : ∀ c : ClassKey (H := H), R c.1 → SR c.1)
    (νl : ∀ c : ClassKey (H := H), SL c.1 → ℝ)
    (νr : ∀ c : ClassKey (H := H), SR c.1 → ℝ)
    (ηl ηr : ClassKey (H := H) → ℝ)

def activeLaw {S : H → Type*} (ν : ∀ c : ClassKey (H := H), S c.1 → ℝ)
    (c : ClassKey (H := H)) : S c.1 → ℝ :=
  fun a => if 0 < counts c.1 c.2 then ν c a else 0

def activeWidth (η : ClassKey (H := H) → ℝ) (c : ClassKey (H := H)) : ℝ :=
  if 0 < counts c.1 c.2 then η c else 0

theorem activeLaw_of_pos {S : H → Type*}
    (ν : ∀ c : ClassKey (H := H), S c.1 → ℝ) (c : ClassKey (H := H))
    (hc : 0 < counts c.1 c.2) : activeLaw counts ν c = ν c := by
  funext a
  simp [activeLaw, hc]

def rawWindows (e : Target counts) (w : RawPairs counts L R) : Prop :=
  ∀ h u, 0 < counts h u →
    typeWindow (νl (h, u)) (ηl (h, u))
      (fun i : Class counts e h u => sl (h, u) (w h i.val).1) ∧
    typeWindow (νr (h, u)) (ηr (h, u))
      (fun i : Class counts e h u => sr (h, u) (w h i.val).2)

theorem rawWindows_iff_childWindows (e : Target counts) (w : RawPairs counts L R) :
    rawWindows counts L R sl sr νl νr ηl ηr e w ↔
      childWindows sl sr (activeLaw counts νl) (activeLaw counts νr)
        (activeWidth counts ηl) (activeWidth counts ηr) (pairEquiv counts L R e w) := by
  unfold rawWindows childWindows
  conv_rhs => rw [Prod.forall]
  apply forall_congr'
  intro h
  apply forall_congr'
  intro u
  by_cases hp : 0 < counts h u
  · simp only [hp, true_implies, activeLaw_of_pos counts _ (h, u) hp,
      activeWidth]
    change (_ ∧ _) ↔
      (typeWindow (νl (h, u)) (ηl (h, u))
        ((fun i : Class counts e h u => sl (h, u) (w h i.val).1) ∘
          (fiberEquiv counts e h u).symm) ∧
      typeWindow (νr (h, u)) (ηr (h, u))
        ((fun i : Class counts e h u => sr (h, u) (w h i.val).2) ∘
          (fiberEquiv counts e h u).symm))
    rw [typeWindow_reindex, typeWindow_reindex]
  · have hn : counts h u = 0 := Nat.eq_zero_of_not_pos hp
    have hcard : Fintype.card (ClassPositions counts (h, u)) = 0 :=
      (Fintype.card_fin _).trans hn
    simp only [hp, false_implies, true_iff]
    constructor <;> intro a
    all_goals
      simp only [activeLaw, activeWidth, ite_eq_right hp]
      unfold empiricalLaw
      rw [hcard]
      simp only [Nat.cast_zero, div_zero, sub_zero, abs_zero, le_refl]

end Windows

section Coefficients

variable [Fintype H] [DecidableEq H] {F : Type*} [CommSemiring F]
    (T : ∀ h, Tensor F (L h × R h) (L h × R h) (L h × R h))
    (coarse : Fin 3 → ∀ h, L h × R h → Fin 17)

def coarseMask (s : Fin 3) (e : Target counts) (w : RawPairs counts L R) : Prop :=
  ∀ h i, coarse s h (w h i) = shapeSide s ((e h).val i)

def coarseWord (s : Fin 3) (w : RawPairs counts L R) : Position counts → Fin 17 :=
  fun p => coarse s p.1 (w p.1 p.2)

def sourceTensor : Tensor F (RawPairs counts L R) (RawPairs counts L R)
    (RawPairs counts L R) := classProduct T

def coarseIdeal (e : Target counts) : Tensor F (RawPairs counts L R)
    (RawPairs counts L R) (RawPairs counts L R) :=
  ExactRecovery.delete (sourceTensor counts L R T)
    (coarseMask counts L R coarse 0 e) (coarseMask counts L R coarse 1 e)
    (coarseMask counts L R coarse 2 e)

def block (c : ClassKey (H := H)) :
    Tensor F (L c.1 × R c.1) (L c.1 × R c.1) (L c.1 × R c.1) :=
  fun x y z => if coarse 0 c.1 x = c.2.1 ∧ coarse 1 c.1 y = c.2.2.1 ∧
      coarse 2 c.1 z = c.2.2.2 then T c.1 x y z else 0

def canonicalBase : Tensor F (CanonicalPairs counts L R) (CanonicalPairs counts L R)
    (CanonicalPairs counts L R) :=
  fun x y z => ∏ c, ∏ j, block L R T coarse c
    (x.left c j, x.right c j) (y.left c j, y.right c j) (z.left c j, z.right c j)

omit [DecidableEq H] in
theorem product_pack (e : Target counts)
    (f : ∀ h, Shape → (L h × R h) → (L h × R h) → (L h × R h) → F)
    (x y z : RawPairs counts L R) :
    (∏ c : ClassKey (H := H), ∏ j : ClassPositions counts c,
      f c.1 c.2
        ((pairEquiv counts L R e x).left c j, (pairEquiv counts L R e x).right c j)
        ((pairEquiv counts L R e y).left c j, (pairEquiv counts L R e y).right c j)
        ((pairEquiv counts L R e z).left c j, (pairEquiv counts L R e z).right c j)) =
      ∏ h, ∏ i, f h ((e h).val i) (x h i) (y h i) (z h i) := by
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro h _
  rw [← Fintype.prod_sigma']
  apply Fintype.prod_equiv (positionEquiv counts e h).symm
  intro i
  simp only [pairEquiv, Equiv.coe_fn_mk, Prod.mk.eta, positionEquiv_symm_shape]

omit [DecidableEq H] in
theorem coarseIdeal_eq_canonicalBase (e : Target counts) (x y z : RawPairs counts L R) :
    coarseIdeal counts L R T coarse e x y z = canonicalBase counts L R T coarse
      (pairEquiv counts L R e x) (pairEquiv counts L R e y) (pairEquiv counts L R e z) := by
  unfold canonicalBase
  rw [product_pack counts L R e (fun h u => block L R T coarse (h, u))]
  simp [block, Fintype.prod_ite_zero, coarseIdeal, ExactRecovery.delete,
    sourceTensor, classProduct, coarseMask, shapeSide, Fin.isValue, ↓reduceIte,
    forall_and]

def coordinateMatrix (e : Target counts) :
    CanonicalPairs counts L R → RawPairs counts L R → F :=
  fun w v => if v = (pairEquiv counts L R e).symm w then 1 else 0

theorem coordinateMatrix_restrict
    [∀ h, Fintype (L h)] [∀ h, Fintype (R h)]
    (e : Target counts) (Q : Tensor F (RawPairs counts L R) (RawPairs counts L R)
      (RawPairs counts L R)) (x y z : CanonicalPairs counts L R) :
    Tensor.restrict (coordinateMatrix counts L R e) (coordinateMatrix counts L R e)
      (coordinateMatrix counts L R e) Q x y z =
      Q ((pairEquiv counts L R e).symm x) ((pairEquiv counts L R e).symm y)
        ((pairEquiv counts L R e).symm z) := by
  classical
  simp [Tensor.restrict, coordinateMatrix, ite_mul, mul_ite]

theorem coarseIdeal_restrict
    [∀ h, Fintype (L h)] [∀ h, Fintype (R h)] (e : Target counts) :
    Tensor.restrict (coordinateMatrix counts L R e) (coordinateMatrix counts L R e)
      (coordinateMatrix counts L R e) (coarseIdeal counts L R T coarse e) =
      canonicalBase counts L R T coarse := by
  funext x y z
  rw [coordinateMatrix_restrict, coarseIdeal_eq_canonicalBase]
  simp

omit [DecidableEq H] in
theorem canonicalBase_eq_pairClassProduct
    (TL : ∀ c : ClassKey (H := H), Tensor F (L c.1) (L c.1) (L c.1))
    (TR : ∀ c : ClassKey (H := H), Tensor F (R c.1) (R c.1) (R c.1))
    (hblock : ∀ c, block L R T coarse c = Tensor.product (TL c) (TR c)) :
    canonicalBase counts L R T coarse = pairClassProduct TL TR := by
  funext x y z
  simp only [canonicalBase, hblock, Tensor.product, pairClassProduct, classProduct,
    Finset.prod_mul_distrib]

section ChildWindows

variable {SL SR : H → Type*}
    [∀ h, Fintype (SL h)] [∀ h, Fintype (SR h)]
    [∀ h, DecidableEq (SL h)] [∀ h, DecidableEq (SR h)]
    (sl : Fin 3 → ∀ c : ClassKey (H := H), L c.1 → SL c.1)
    (sr : Fin 3 → ∀ c : ClassKey (H := H), R c.1 → SR c.1)
    (νl : Fin 3 → ∀ c : ClassKey (H := H), SL c.1 → ℝ)
    (νr : Fin 3 → ∀ c : ClassKey (H := H), SR c.1 → ℝ)
    (ηl ηr : Fin 3 → ClassKey (H := H) → ℝ)

def ideal (e : Target counts) : Tensor F (RawPairs counts L R)
    (RawPairs counts L R) (RawPairs counts L R) :=
  ExactRecovery.delete (coarseIdeal counts L R T coarse e)
    (rawWindows counts L R (sl 0) (sr 0) (νl 0) (νr 0) (ηl 0) (ηr 0) e)
    (rawWindows counts L R (sl 1) (sr 1) (νl 1) (νr 1) (ηl 1) (ηr 1) e)
    (rawWindows counts L R (sl 2) (sr 2) (νl 2) (νr 2) (ηl 2) (ηr 2) e)

def canonicalIdeal : Tensor F (CanonicalPairs counts L R) (CanonicalPairs counts L R)
    (CanonicalPairs counts L R) :=
  ExactRecovery.delete (canonicalBase counts L R T coarse)
    (childWindows (sl 0) (sr 0) (activeLaw counts (νl 0)) (activeLaw counts (νr 0))
      (activeWidth counts (ηl 0)) (activeWidth counts (ηr 0)))
    (childWindows (sl 1) (sr 1) (activeLaw counts (νl 1)) (activeLaw counts (νr 1))
      (activeWidth counts (ηl 1)) (activeWidth counts (ηr 1)))
    (childWindows (sl 2) (sr 2) (activeLaw counts (νl 2)) (activeLaw counts (νr 2))
      (activeWidth counts (ηl 2)) (activeWidth counts (ηr 2)))

def usefulByTriple (s : Fin 3)
    (t : JointCoarseHashing.Triple (Position counts)) (w : RawPairs counts L R) : Prop :=
  ∃ e : Target counts, triple counts e = t ∧
    rawWindows counts L R (sl s) (sr s) (νl s) (νr s) (ηl s) (ηr s) e w

omit [Fintype H] [DecidableEq H]
  [∀ index, Fintype (SL index)] [∀ index, Fintype (SR index)] in
theorem usefulByTriple_target (s : Fin 3) (e : Target counts) (w : RawPairs counts L R) :
    usefulByTriple counts L R sl sr νl νr ηl ηr s (triple counts e) w ↔
      rawWindows counts L R (sl s) (sr s) (νl s) (νr s) (ηl s) (ηr s) e w := by
  constructor
  · rintro ⟨f, hf, hw⟩
    have he : f = e := triple_injective counts hf
    subst f
    exact hw
  · intro hw
    exact ⟨e, rfl, hw⟩

omit [DecidableEq H] [∀ index, Fintype (SL index)] [∀ index, Fintype (SR index)] in
theorem ideal_eq_jointIdeal (e : Target counts) :
    ideal counts L R T coarse sl sr νl νr ηl ηr e =
      JointIdealBranches.ideal (sourceTensor counts L R T)
        (coarseWord counts L R coarse 0) (coarseWord counts L R coarse 1)
        (coarseWord counts L R coarse 2)
        (usefulByTriple counts L R sl sr νl νr ηl ηr 0)
        (usefulByTriple counts L R sl sr νl νr ηl ηr 1)
        (usefulByTriple counts L R sl sr νl νr ηl ηr 2) (triple counts e) := by
  funext x y z
  have hx : coarseWord counts L R coarse 0 x = (triple counts e).1 ↔
      coarseMask counts L R coarse 0 e x := by
    simp [coarseWord, triple, coarseMask, shapeSide, funext_iff, Sigma.forall]
  have hy : coarseWord counts L R coarse 1 y = (triple counts e).2.1 ↔
      coarseMask counts L R coarse 1 e y := by
    simp [coarseWord, triple, coarseMask, shapeSide, funext_iff, Sigma.forall]
  have hz : coarseWord counts L R coarse 2 z = (triple counts e).2.2 ↔
      coarseMask counts L R coarse 2 e z := by
    simp [coarseWord, triple, coarseMask, shapeSide, funext_iff, Sigma.forall]
  simp only [ideal, coarseIdeal, JointIdealBranches.ideal, ExactRecovery.delete,
    usefulByTriple_target, hx, hy, hz]
  split_ifs <;> simp_all

omit [DecidableEq H] in
theorem ideal_eq_canonicalIdeal (e : Target counts)
    (x y z : RawPairs counts L R) :
    ideal counts L R T coarse sl sr νl νr ηl ηr e x y z =
      canonicalIdeal counts L R T coarse sl sr νl νr ηl ηr
        (pairEquiv counts L R e x) (pairEquiv counts L R e y)
        (pairEquiv counts L R e z) := by
  simp only [ideal, canonicalIdeal, ExactRecovery.delete, rawWindows_iff_childWindows,
    coarseIdeal_eq_canonicalBase]

theorem ideal_restrict
    [∀ h, Fintype (L h)] [∀ h, Fintype (R h)] (e : Target counts) :
    Tensor.restrict (coordinateMatrix counts L R e) (coordinateMatrix counts L R e)
      (coordinateMatrix counts L R e) (ideal counts L R T coarse sl sr νl νr ηl ηr e) =
      canonicalIdeal counts L R T coarse sl sr νl νr ηl ηr := by
  funext x y z
  rw [coordinateMatrix_restrict]
  simp only [ideal, canonicalIdeal, ExactRecovery.delete, rawWindows_iff_childWindows,
    coarseIdeal_eq_canonicalBase, Equiv.apply_symm_apply]

end ChildWindows

end Coefficients

end MatrixMultiplication.JointCanonicalization

end

end OAI
