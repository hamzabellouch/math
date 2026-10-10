import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.Extraction

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

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

end

end OAI
