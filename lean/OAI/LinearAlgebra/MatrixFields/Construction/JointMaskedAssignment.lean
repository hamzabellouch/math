import Mathlib
import OAI.LinearAlgebra.MatrixFields.Extraction.JointExtraction
import OAI.LinearAlgebra.MatrixFields.Histories.InheritedMaskMargins
import OAI.LinearAlgebra.MatrixFields.Parameters.JointPopulation

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointCoarseAssignment

open MatrixMultiplication.Foundation JointExtraction

attribute [local instance] Classical.propDecidable

variable {F X Y Z A B C I V : Type*} [CommSemiring F]

abbrev Triple (A B C : Type*) := A × B × C

def survives (hx : A → Prop) (hy : B → Prop) (hz : C → Prop)
    (e : Triple A B C) : Prop := hx e.1 ∧ hy e.2.1 ∧ hz e.2.2

def eligible (ambient targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop) : Finset (Triple A B C) :=
  ambient.filter fun e => e ∈ targets ∧ survives hx hy hz e ∧
    ∀ f ∈ ambient, survives hx hy hz f → f.1 = e.1 → f = e

theorem mem_eligible_iff (ambient targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop) (e : Triple A B C) :
    e ∈ eligible ambient targets hx hy hz ↔
      e ∈ ambient ∧ e ∈ targets ∧ survives hx hy hz e ∧
        ∀ f ∈ ambient, survives hx hy hz f → f.1 = e.1 → f = e := by
  simp [eligible]

def assignUseful (eligible : Finset I) (compatible useful : I → V → Prop)
    (v : V) : Option I :=
  retainAssignment (uniqueAssignment eligible compatible)
    (fun v => ∃ i, uniqueAssignment eligible compatible v = some i ∧ useful i v) v

theorem assignUseful_spec (eligible : Finset I) (compatible useful : I → V → Prop)
    (v : V) (i : I) (h : assignUseful eligible compatible useful v = some i) :
    i ∈ eligible ∧ compatible i v ∧ useful i v ∧
      ∀ j, j ∈ eligible → compatible j v → j = i := by
  classical
  have hu : uniqueAssignment eligible compatible v = some i :=
    retainAssignment_some _ _ v i h
  have hh := uniqueAssignment_spec eligible compatible v i hu
  have huse : useful i v := by
    unfold assignUseful retainAssignment at h
    split_ifs at h with hk
    obtain ⟨j, hj, hju⟩ := hk
    have hji : j = i := Option.some.inj (hj.symm.trans hu)
    exact hji ▸ hju
  exact ⟨hh.1, hh.2.1, huse, hh.2.2⟩

def assignments (ambient targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop)
    (cx : X → A) (cy : Y → B) (cz : Z → C)
    (compatibleY : Triple A B C → Y → Prop)
    (compatibleZ : Triple A B C → Z → Prop)
    (usefulX : Triple A B C → X → Prop)
    (usefulY : Triple A B C → Y → Prop)
    (usefulZ : Triple A B C → Z → Prop) : Assignment X Y Z (Triple A B C) where
  x := assignUseful (eligible ambient targets hx hy hz) (fun e x => cx x = e.1) usefulX
  y := assignUseful (eligible ambient targets hx hy hz)
    (fun e y => cy y = e.2.1 ∧ compatibleY e y) usefulY
  z := assignUseful (eligible ambient targets hx hy hz)
    (fun e z => cz z = e.2.2 ∧ compatibleZ e z) usefulZ

theorem assignments_coherent
    (T : Tensor F X Y Z) (ambient targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop)
    (cx : X → A) (cy : Y → B) (cz : Z → C)
    (compatibleY : Triple A B C → Y → Prop)
    (compatibleZ : Triple A B C → Z → Prop)
    (usefulX : Triple A B C → X → Prop)
    (usefulY : Triple A B C → Y → Prop)
    (usefulZ : Triple A B C → Z → Prop)
    (support : ∀ x y z, T x y z ≠ 0 → (cx x, cy y, cz z) ∈ ambient)
    (transferY : ∀ x y z e, T x y z ≠ 0 → (cx x, cy y, cz z) = e →
      usefulX e x → compatibleY e y)
    (transferZ : ∀ x y z e, T x y z ≠ 0 → (cx x, cy y, cz z) = e →
      usefulX e x → usefulY e y → compatibleZ e z) :
    Coherent T (assignments ambient targets hx hy hz cx cy cz
      compatibleY compatibleZ usefulX usefulY usefulZ) := by
  intro x y z i j k hT hxi hyj hzk
  have hi := assignUseful_spec (eligible ambient targets hx hy hz)
    (fun e x => cx x = e.1) usefulX x i hxi
  have hj := assignUseful_spec (eligible ambient targets hx hy hz)
    (fun e y => cy y = e.2.1 ∧ compatibleY e y) usefulY y j hyj
  have hk := assignUseful_spec (eligible ambient targets hx hy hz)
    (fun e z => cz z = e.2.2 ∧ compatibleZ e z) usefulZ z k hzk
  have hie := (mem_eligible_iff ambient targets hx hy hz i).mp hi.1
  have hje := (mem_eligible_iff ambient targets hx hy hz j).mp hj.1
  have hke := (mem_eligible_iff ambient targets hx hy hz k).mp hk.1
  have hs : survives hx hy hz (cx x, cy y, cz z) :=
    ⟨hi.2.1.symm ▸ hie.2.2.1.1, hj.2.1.1.symm ▸ hje.2.2.1.2.1,
      hk.2.1.1.symm ▸ hke.2.2.1.2.2⟩
  have he : (cx x, cy y, cz z) = i :=
    hie.2.2.2 _ (support x y z hT) hs hi.2.1
  have hyi : cy y = i.2.1 := congrArg (fun e : Triple A B C => e.2.1) he
  have hzi : cz z = i.2.2 := congrArg (fun e : Triple A B C => e.2.2) he
  have hij : i = j := hj.2.2.2 i hi.1
    ⟨hyi, transferY x y z i hT he hi.2.2.1⟩
  have huy : usefulY i y := hij.symm ▸ hj.2.2.1
  have hik : i = k := hk.2.2.2 i hi.1
    ⟨hzi, transferZ x y z i hT he hi.2.2.1 huy⟩
  exact ⟨hij, hik⟩

end MatrixMultiplication.JointCoarseAssignment






namespace MatrixMultiplication.JointIdealBranches

open MatrixMultiplication.Foundation JointExtraction JointCoarseAssignment

attribute [local instance] Classical.propDecidable

variable {F X Y Z A B C : Type*} [CommSemiring F]

def ideal (T : Tensor F X Y Z)
    (cx : X → A) (cy : Y → B) (cz : Z → C)
    (usefulX : Triple A B C → X → Prop)
    (usefulY : Triple A B C → Y → Prop)
    (usefulZ : Triple A B C → Z → Prop) (e : Triple A B C) : Tensor F X Y Z :=
  ExactRecovery.delete T (fun x => cx x = e.1 ∧ usefulX e x)
    (fun y => cy y = e.2.1 ∧ usefulY e y)
    (fun z => cz z = e.2.2 ∧ usefulZ e z)

theorem branch_eq_delete_ideal
    (T : Tensor F X Y Z) (ambient targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop)
    (cx : X → A) (cy : Y → B) (cz : Z → C)
    (compatibleY : Triple A B C → Y → Prop)
    (compatibleZ : Triple A B C → Z → Prop)
    (usefulX : Triple A B C → X → Prop)
    (usefulY : Triple A B C → Y → Prop)
    (usefulZ : Triple A B C → Z → Prop) (e : Triple A B C) :
    let a := assignments ambient targets hx hy hz cx cy cz
      compatibleY compatibleZ usefulX usefulY usefulZ
    branch T a e = ExactRecovery.delete (ideal T cx cy cz usefulX usefulY usefulZ e)
      (fun x => a.x x = some e) (fun y => a.y y = some e) (fun z => a.z z = some e) := by
  classical
  dsimp only
  funext x y z
  by_cases h :
      (assignments ambient targets hx hy hz cx cy cz compatibleY compatibleZ
        usefulX usefulY usefulZ).x x = some e ∧
      (assignments ambient targets hx hy hz cx cy cz compatibleY compatibleZ
        usefulX usefulY usefulZ).y y = some e ∧
      (assignments ambient targets hx hy hz cx cy cz compatibleY compatibleZ
        usefulX usefulY usefulZ).z z = some e
  · have hX := assignUseful_spec (eligible ambient targets hx hy hz)
      (fun e x => cx x = e.1) usefulX x e h.1
    have hY := assignUseful_spec (eligible ambient targets hx hy hz)
      (fun e y => cy y = e.2.1 ∧ compatibleY e y) usefulY y e h.2.1
    have hZ := assignUseful_spec (eligible ambient targets hx hy hz)
      (fun e z => cz z = e.2.2 ∧ compatibleZ e z) usefulZ z e h.2.2
    simp [branch, ExactRecovery.delete, ideal, h, hX.2.1, hX.2.2.1,
      hY.2.1.1, hY.2.2.1, hZ.2.1.1, hZ.2.2.1]
  · simp [branch, ExactRecovery.delete, h]

theorem ideal_delete (T : Tensor F X Y Z)
    (px : X → Prop) (py : Y → Prop) (pz : Z → Prop)
    (cx : X → A) (cy : Y → B) (cz : Z → C)
    (usefulX : Triple A B C → X → Prop)
    (usefulY : Triple A B C → Y → Prop)
    (usefulZ : Triple A B C → Z → Prop) (e : Triple A B C) :
    ideal (ExactRecovery.delete T px py pz) cx cy cz usefulX usefulY usefulZ e =
      ExactRecovery.delete (ideal T cx cy cz usefulX usefulY usefulZ e) px py pz := by
  funext x y z
  simp only [ideal, ExactRecovery.delete]
  split_ifs <;> simp_all

theorem branch_masked_eq_delete_ideal
    (T : Tensor F X Y Z) (px : X → Prop) (py : Y → Prop) (pz : Z → Prop)
    (ambient targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop)
    (cx : X → A) (cy : Y → B) (cz : Z → C)
    (compatibleY : Triple A B C → Y → Prop)
    (compatibleZ : Triple A B C → Z → Prop)
    (usefulX : Triple A B C → X → Prop)
    (usefulY : Triple A B C → Y → Prop)
    (usefulZ : Triple A B C → Z → Prop) (e : Triple A B C) :
    let a := assignments ambient targets hx hy hz cx cy cz
      compatibleY compatibleZ usefulX usefulY usefulZ
    branch (ExactRecovery.delete T px py pz) a e =
      ExactRecovery.delete (ideal T cx cy cz usefulX usefulY usefulZ e)
        (fun x => a.x x = some e ∧ px x)
        (fun y => a.y y = some e ∧ py y)
        (fun z => a.z z = some e ∧ pz z) := by
  dsimp only
  rw [branch_eq_delete_ideal, ideal_delete]
  funext x y z
  simp only [ExactRecovery.delete]
  split_ifs <;> simp_all

theorem masked_source_restriction [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (T : Tensor F X Y Z) (a : Assignment X Y Z (Triple A B C))
    (hcoherent : Coherent T a) (px : X → Prop) (py : Y → Prop) (pz : Z → Prop) :
    Tensor.restrict (assignmentMatrix a.x) (assignmentMatrix a.y) (assignmentMatrix a.z)
      (ExactRecovery.delete T px py pz) =
      Tensor.directSum (branch (ExactRecovery.delete T px py pz) a) := by
  apply restrict_assignments_eq_directSum
  apply coherent_of_support_subset T _ a hcoherent
  intro x y z h ht
  exact h (by simp [ExactRecovery.delete, ht])

end MatrixMultiplication.JointIdealBranches






namespace MatrixMultiplication.JointCanonicalization

open MatrixMultiplication.Foundation JointPopulation InheritedMasks
open PermutationMatching HistorySymmetry
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H : Type*} [Fintype H] [DecidableEq H]
    (counts : H → Shape → ℕ)

def fiberEquiv (e : Target counts) (h : H) (u : Shape) :
    Class counts e h u ≃ Fin (counts h u) :=
  Fintype.equivOfCardEq (by rw [class_card, Fintype.card_fin])

def positionEquiv (e : Target counts) (h : H) :
    Positions counts h ≃ (Σ u, Fin (counts h u)) :=
  (Equiv.sigmaFiberEquiv (e h).val).symm.trans
    (Equiv.sigmaCongrRight (fiberEquiv counts e h))

omit [Fintype H] [DecidableEq H] in
@[simp] theorem positionEquiv_shape (e : Target counts) (h : H) (i : Positions counts h) :
    (positionEquiv counts e h i).1 = (e h).val i := rfl

omit [Fintype H] [DecidableEq H] in
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

omit [Fintype H] [DecidableEq H] in
theorem pairEquiv_fiber_left (e : Target counts) (w : RawPairs counts L R)
    (h : H) (u : Shape) (j : Fin (counts h u)) :
    (pairEquiv counts L R e w).left (h, u) j =
      (w h ((fiberEquiv counts e h u).symm j).val).1 := rfl

omit [Fintype H] [DecidableEq H] in
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

omit [Fintype H] [DecidableEq H] in
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

omit [Fintype H] [DecidableEq H] in
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
    simp only [hp, false_implies, true_iff]
    simp only [activeLaw, activeWidth, typeWindow, empiricalLaw, ClassPositions,
      Fintype.card_fin, hn, Nat.cast_zero, div_zero]
    simp

end Windows

section Coefficients

variable {F : Type*} [CommSemiring F]
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

omit [Fintype H] [DecidableEq H] [∀ h, Fintype (SL h)] [∀ h, Fintype (SR h)] in
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

omit [DecidableEq H] [∀ h, Fintype (SL h)] [∀ h, Fintype (SR h)] in
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






namespace MatrixMultiplication.JointAssignmentLoss

open JointExtraction JointCoarseAssignment

attribute [local instance] Classical.propDecidable

variable {A B C I V Ω : Type*}

theorem uniqueAssignment_of_unique (candidates : Finset I)
    (compatible : I → V → Prop) (v : V) (i : I)
    (hi : i ∈ candidates) (hc : compatible i v)
    (hu : ∀ j, j ∈ candidates → compatible j v → j = i) :
    uniqueAssignment candidates compatible v = some i := by
  classical
  have hex : ∃ j, j ∈ candidates ∧ compatible j v ∧
      ∀ k, k ∈ candidates → compatible k v → k = j := ⟨i, hi, hc, hu⟩
  unfold uniqueAssignment
  rw [dite_eq_left hex]
  exact congrArg some (hu _ (Classical.choose_spec hex).1 (Classical.choose_spec hex).2.1)

theorem assignUseful_of_unique (candidates : Finset I)
    (compatible useful : I → V → Prop) (v : V) (i : I)
    (hi : i ∈ candidates) (hc : compatible i v) (huse : useful i v)
    (hu : ∀ j, j ∈ candidates → compatible j v → j = i) :
    assignUseful candidates compatible useful v = some i := by
  have hassign := uniqueAssignment_of_unique candidates compatible v i hi hc hu
  have hkeep : ∃ j, uniqueAssignment candidates compatible v = some j ∧ useful j v :=
    ⟨i, hassign, huse⟩
  simp only [assignUseful, retainAssignment, ite_eq_left hkeep]
  exact hassign

def ambientXCollision (ambient : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop) (e : Triple A B C) : Prop :=
  ∃ f ∈ ambient, f ≠ e ∧ survives hx hy hz f ∧ f.1 = e.1

def targetCompatibleCollision (targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop)
    (compatible : Triple A B C → V → Prop) (e : Triple A B C) (v : V) : Prop :=
  ∃ f ∈ targets, f ≠ e ∧ survives hx hy hz f ∧ compatible f v

theorem eligible_of_no_ambientXCollision
    (ambient targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop) (e : Triple A B C)
    (ha : e ∈ ambient) (ht : e ∈ targets) (hs : survives hx hy hz e)
    (hno : ¬ ambientXCollision ambient hx hy hz e) :
    e ∈ eligible ambient targets hx hy hz := by
  apply (mem_eligible_iff ambient targets hx hy hz e).2
  refine ⟨ha, ht, hs, ?_⟩
  intro f hf hfs hfx
  by_contra hne
  exact hno ⟨f, hf, hne, hfs, hfx⟩

theorem not_eligible_iff_ambientXCollision
    (ambient targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop) (e : Triple A B C)
    (ha : e ∈ ambient) (ht : e ∈ targets) (hs : survives hx hy hz e) :
    e ∉ eligible ambient targets hx hy hz ↔ ambientXCollision ambient hx hy hz e := by
  constructor
  · intro h
    by_contra hno
    exact h (eligible_of_no_ambientXCollision ambient targets hx hy hz e ha ht hs hno)
  · rintro ⟨f, hf, hne, hfs, hfx⟩ he
    exact hne (((mem_eligible_iff ambient targets hx hy hz e).1 he).2.2.2 f hf hfs hfx)

theorem assignUseful_of_no_targetCollision
    (ambient targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop)
    (compatible useful : Triple A B C → V → Prop) (e : Triple A B C) (v : V)
    (he : e ∈ eligible ambient targets hx hy hz)
    (hc : compatible e v) (hu : useful e v)
    (hno : ¬ targetCompatibleCollision targets hx hy hz compatible e v) :
    assignUseful (eligible ambient targets hx hy hz) compatible useful v = some e := by
  apply assignUseful_of_unique _ _ _ _ _ he hc hu
  intro f hf hcf
  have hfe := (mem_eligible_iff ambient targets hx hy hz f).1 hf
  by_contra hne
  exact hno ⟨f, hfe.2.1, hne, hfe.2.2.1, hcf⟩

theorem assignment_failure_implies_collision
    (ambient targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop)
    (compatible useful : Triple A B C → V → Prop) (e : Triple A B C) (v : V)
    (ha : e ∈ ambient) (ht : e ∈ targets) (hs : survives hx hy hz e)
    (hc : compatible e v) (hu : useful e v)
    (hfail : assignUseful (eligible ambient targets hx hy hz) compatible useful v ≠ some e) :
    ambientXCollision ambient hx hy hz e ∨
      targetCompatibleCollision targets hx hy hz compatible e v := by
  by_cases hX : ambientXCollision ambient hx hy hz e
  · exact Or.inl hX
  apply Or.inr
  by_contra hC
  have he := eligible_of_no_ambientXCollision ambient targets hx hy hz e ha ht hs hX
  exact hfail (assignUseful_of_no_targetCollision ambient targets hx hy hz
    compatible useful e v he hc hu hC)

theorem retained_assignment_of_no_collision
    (ambient targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop)
    (compatible useful : Triple A B C → V → Prop) (keep : V → Prop)
    (e : Triple A B C) (v : V)
    (ha : e ∈ ambient) (ht : e ∈ targets) (hs : survives hx hy hz e)
    (hc : compatible e v) (hu : useful e v) (hk : keep v)
    (hX : ¬ ambientXCollision ambient hx hy hz e)
    (hC : ¬ targetCompatibleCollision targets hx hy hz compatible e v) :
    retainAssignment (assignUseful (eligible ambient targets hx hy hz) compatible useful)
      keep v = some e := by
  have he := eligible_of_no_ambientXCollision ambient targets hx hy hz e ha ht hs hX
  have hassign := assignUseful_of_no_targetCollision ambient targets hx hy hz
    compatible useful e v he hc hu hC
  simpa only [retainAssignment, ite_eq_left hk] using hassign

theorem passing_assignment_failure_subset
    (samples : Finset Ω) (ambient targets : Finset (Triple A B C))
    (hx : Ω → A → Prop) (hy : Ω → B → Prop) (hz : Ω → C → Prop)
    (compatible useful : Triple A B C → V → Prop) (keep : V → Prop)
    (e : Triple A B C) (v : V) (ha : e ∈ ambient) (ht : e ∈ targets)
    (hc : compatible e v) (hu : useful e v) (hk : keep v) :
    samples.filter (fun ω => survives (hx ω) (hy ω) (hz ω) e ∧
      retainAssignment
        (assignUseful (eligible ambient targets (hx ω) (hy ω) (hz ω)) compatible useful)
        keep v ≠ some e) ⊆
    samples.filter (fun ω => survives (hx ω) (hy ω) (hz ω) e ∧
      (ambientXCollision ambient (hx ω) (hy ω) (hz ω) e ∨
        targetCompatibleCollision targets (hx ω) (hy ω) (hz ω) compatible e v)) := by
  intro ω hω
  obtain ⟨hωs, hs, hfail⟩ := Finset.mem_filter.1 hω
  apply Finset.mem_filter.2
  refine ⟨hωs, hs, ?_⟩
  have hfail' : assignUseful (eligible ambient targets (hx ω) (hy ω) (hz ω))
      compatible useful v ≠ some e := by
    simpa only [retainAssignment, ite_eq_left hk] using hfail
  exact assignment_failure_implies_collision ambient targets (hx ω) (hy ω) (hz ω)
    compatible useful e v ha ht hs hc hu hfail'

end MatrixMultiplication.JointAssignmentLoss






namespace MatrixMultiplication.JointMaskedSelection.OrbitData

open JointCoarseHashing

attribute [local instance] Classical.propDecidable

variable {P E O V : Type*} [Fintype P] [Fintype E]

def actualTargets (d : OrbitData P E O V) : Finset (Triple P) :=
  Finset.univ.image d.coarse

theorem coarse_mem_actualTargets (d : OrbitData P E O V) (e : E) :
    d.coarse e ∈ d.actualTargets :=
  Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩

def xFlag (k : ℕ) (U : Finset (ZMod (37 ^ k))) (s : Sample P k) (I : Word P) : Prop :=
  JointHashing.xHash s (castWord k I) ∈ U

def yFlag (k : ℕ) (U : Finset (ZMod (37 ^ k))) (s : Sample P k) (J : Word P) : Prop :=
  JointHashing.yHash s (castWord k J) ∈ U

def zFlag (d : OrbitData P E O V) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (s : Sample P k) (K : Word P) : Prop :=
  JointHashing.zHash (twoUnit k) s (fun p => (d.support p : ZMod (37 ^ k))) (castWord k K) ∈ U

omit [Fintype E] in
theorem actual_survival_iff (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (s : Sample P k) (f : Triple P) (hf : f ∈ d.ambient) :
    JointCoarseAssignment.survives (xFlag k U s) (yFlag k U s) (d.zFlag k U s) f ↔
      Survives k U f s :=
  full_survival_iff k U hAP d.support f (d.support_ambient f hf) s

def actualEligible (d : OrbitData P E O V) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (s : Sample P k) : Finset (Triple P) :=
  JointCoarseAssignment.eligible d.ambient d.actualTargets
    (xFlag k U s) (yFlag k U s) (d.zFlag k U s)

theorem good_mem_actualEligible (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (N : ℝ) (e : E) (s : Sample P k) (hg : d.Good k U N e s) :
    d.coarse e ∈ d.actualEligible k U s := by
  apply JointAssignmentLoss.eligible_of_no_ambientXCollision d.ambient d.actualTargets
    (xFlag k U s) (yFlag k U s) (d.zFlag k U s) (d.coarse e)
    (d.target_mem e) (d.coarse_mem_actualTargets e)
    ((d.actual_survival_iff k U hAP s _ (d.target_mem e)).2 hg.1)
  rintro ⟨f, hf, hne, hs, hx⟩
  exact d.good_eligibility k U N e s hg
    ⟨f, (d.mem_eligibilityCompetitors e f).2 ⟨hf, hne, hx⟩,
      (d.actual_survival_iff k U hAP s f hf).1 hs⟩

def actualAssignment (d : OrbitData P E O V) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (compatible useful : Triple P → V → Prop) (keep : V → Prop)
    (s : Sample P k) (v : V) : Option (Triple P) :=
  JointExtraction.retainAssignment
    (JointCoarseAssignment.assignUseful (d.actualEligible k U s) compatible useful) keep v

theorem model_retained_assigned (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (N : ℝ) (e : E) (o : O) (ho : o ∈ d.orbits e) (s : Sample P k)
    (hg : d.Good k U N e s)
    (compatible useful : Triple P → V → Prop) (keep : V → Prop)
    (v : V) (hv : v ∈ JointLossCounts.retained (d.passing e o) (d.variableBad k U e o) s)
    (hc : compatible (d.coarse e) v) (hu : useful (d.coarse e) v) (hk : keep v)
    (hcover : ∀ f ∈ d.actualTargets, f ≠ d.coarse e → compatible f v →
      f ∈ d.competitors e o v) :
    d.actualAssignment k U compatible useful keep s v = some (d.coarse e) := by
  obtain ⟨hpass, hnotbad⟩ := Finset.mem_filter.1 hv
  have hassign := JointAssignmentLoss.assignUseful_of_no_targetCollision
    d.ambient d.actualTargets (xFlag k U s) (yFlag k U s) (d.zFlag k U s)
    compatible useful (d.coarse e) v (d.good_mem_actualEligible k U hAP N e s hg) hc hu
    (by
      rintro ⟨f, hf, hne, hsurv, hcomp⟩
      have hfc := hcover f hf hne hcomp
      have hfa := d.competitor_mem e o ho v hpass f hfc
      exact hnotbad ⟨f, hfc, (d.actual_survival_iff k U hAP s f hfa).1 hsurv⟩)
  simpa only [actualAssignment, actualEligible, JointExtraction.retainAssignment,
    ite_eq_left hk] using hassign

theorem actual_failure_subset_model_missing (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (N : ℝ) (e : E) (o : O) (ho : o ∈ d.orbits e) (s : Sample P k)
    (hg : d.Good k U N e s)
    (compatible useful : Triple P → V → Prop) (keep : V → Prop)
    (hc : ∀ v ∈ d.passing e o, compatible (d.coarse e) v)
    (hu : ∀ v ∈ d.passing e o, useful (d.coarse e) v)
    (hk : ∀ v ∈ d.passing e o, keep v)
    (hcover : ∀ v ∈ d.passing e o, ∀ f ∈ d.actualTargets,
      f ≠ d.coarse e → compatible f v → f ∈ d.competitors e o v) :
    (d.full e o).filter (fun v => d.actualAssignment k U compatible useful keep s v ≠
      some (d.coarse e)) ⊆
    d.full e o \ JointLossCounts.retained (d.passing e o) (d.variableBad k U e o) s := by
  intro v hv
  obtain ⟨hvfull, hvfail⟩ := Finset.mem_filter.1 hv
  apply Finset.mem_sdiff.2
  refine ⟨hvfull, ?_⟩
  intro hvmodel
  have hpass := (Finset.mem_filter.1 hvmodel).1
  exact hvfail (d.model_retained_assigned k U hAP N e o ho s hg compatible useful keep v
    hvmodel (hc v hpass) (hu v hpass) (hk v hpass) (hcover v hpass))

theorem good_actual_missingFraction_le (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (C₀ N : ℝ) (e : E) (o : O) (ho : o ∈ d.orbits e) (s : Sample P k)
    (hg : d.Good k U N e s)
    (compatible useful : Triple P → V → Prop) (keep : V → Prop)
    (hc : ∀ v ∈ d.passing e o, compatible (d.coarse e) v)
    (hu : ∀ v ∈ d.passing e o, useful (d.coarse e) v)
    (hk : ∀ v ∈ d.passing e o, keep v)
    (hcover : ∀ v ∈ d.passing e o, ∀ f ∈ d.actualTargets,
      f ≠ d.coarse e → compatible f v → f ∈ d.competitors e o v)
    (hdet : ∀ o ∈ d.orbits e,
      JointLossCounts.deterministicLossFraction (d.full e o) (d.passing e o) ≤ C₀ / N) :
    (((d.full e o).filter (fun v => d.actualAssignment k U compatible useful keep s v ≠
      some (d.coarse e))).card : ℝ) / ((d.full e o).card : ℝ) ≤ (C₀ + 1) / N := by
  have hcard := Finset.card_le_card
    (d.actual_failure_subset_model_missing k U hAP N e o ho s hg compatible useful keep hc hu hk hcover)
  have hR : (((d.full e o).filter (fun v => d.actualAssignment k U compatible useful keep s v ≠
      some (d.coarse e))).card : ℝ) ≤
      ((d.full e o \ JointLossCounts.retained (d.passing e o) (d.variableBad k U e o) s).card : ℝ) := by
    exact_mod_cast hcard
  exact (div_le_div_of_nonneg_right hR (Nat.cast_nonneg _)).trans
    (d.good_missingFraction_le k U C₀ N e s hg hdet o ho)

end MatrixMultiplication.JointMaskedSelection.OrbitData

end
end

end MatrixAllFields

end OAI
