import Mathlib
import OAI.Combinatorics.StripMass.TurnShelling

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace BoundaryInsert
variable {n m : ℕ}

@[simp] lemma old_val (k : ℕ) (hk : k≤n) (i : Fin n) :
    (old (m:=m) k hk i).val=(if i.val<k then i.val else i.val+m) := rfl
@[simp] lemma fresh_val (k : ℕ) (hk : k≤n) (i : Fin m) :
    (fresh k hk i).val=k+i.val := rfl

lemma boundary_before {V W : Type*} (k : ℕ) (hk : k≤n) (a : Fin n → V)
    (b : Fin m → W) (i : Fin (n+m)) (hi : i.val<k) :
    boundary k hk a b i=.inl (a ⟨i.val,by omega⟩) := by
  have he : old (m:=m) k hk ⟨i.val,by omega⟩=i := by
    apply Fin.ext
    change (if i.val<k then i.val else i.val+m)=i.val
    simp only [ite_eq_left hi]
  exact (congrArg (boundary k hk a b) he).symm.trans (boundary_old k hk a b _)

lemma boundary_between {V W : Type*} (k : ℕ) (hk : k≤n) (a : Fin n → V)
    (b : Fin m → W) (i : Fin (n+m)) (hl : k≤ i.val) (hr : i.val<k+m) :
    boundary k hk a b i=.inr (b ⟨i.val-k,by omega⟩) := by
  have he : fresh (n:=n) k hk ⟨i.val-k,by omega⟩=i := by
    apply Fin.ext
    change k+(i.val-k)=i.val
    omega
  exact (congrArg (boundary k hk a b) he).symm.trans (boundary_fresh k hk a b _)

lemma boundary_after {V W : Type*} (k : ℕ) (hk : k≤n) (a : Fin n → V)
    (b : Fin m → W) (i : Fin (n+m)) (hi : k+m≤ i.val) :
    boundary k hk a b i=.inl (a ⟨i.val-m,by omega⟩) := by
  have he : old (m:=m) k hk ⟨i.val-m,by omega⟩=i := by
    apply Fin.ext
    change (if i.val-m<k then i.val-m else i.val-m+m)=i.val
    rw [ite_eq_right (by omega)]
    omega
  exact (congrArg (boundary k hk a b) he).symm.trans (boundary_old k hk a b _)

lemma gauge_before (k : ℕ) (hk : k≤n) (a : Fin n → ℤ)
    (b : Fin m → ℤ) (i : Fin (n+m)) (hi : i.val<k) :
    gauge k hk a b i=a ⟨i.val,by omega⟩ := by
  have he : old (m:=m) k hk ⟨i.val,by omega⟩=i := by
    apply Fin.ext
    change (if i.val<k then i.val else i.val+m)=i.val
    simp only [ite_eq_left hi]
  exact (congrArg (gauge k hk a b) he).symm.trans (gauge_old k hk a b _)

lemma gauge_between (k : ℕ) (hk : k≤n) (a : Fin n → ℤ)
    (b : Fin m → ℤ) (i : Fin (n+m)) (hl : k≤ i.val) (hr : i.val<k+m) :
    gauge k hk a b i=b ⟨i.val-k,by omega⟩ := by
  have he : fresh (n:=n) k hk ⟨i.val-k,by omega⟩=i := by
    apply Fin.ext
    change k+(i.val-k)=i.val
    omega
  exact (congrArg (gauge k hk a b) he).symm.trans (gauge_fresh k hk a b _)

lemma gauge_after (k : ℕ) (hk : k≤n) (a : Fin n → ℤ)
    (b : Fin m → ℤ) (i : Fin (n+m)) (hi : k+m≤ i.val) :
    gauge k hk a b i=a ⟨i.val-m,by omega⟩ := by
  have he : old (m:=m) k hk ⟨i.val-m,by omega⟩=i := by
    apply Fin.ext
    change (if i.val-m<k then i.val-m else i.val-m+m)=i.val
    rw [ite_eq_right (by omega)]
    omega
  exact (congrArg (gauge k hk a b) he).symm.trans (gauge_old k hk a b _)

lemma used_left {V W : Type*} (r : V → V → Prop) (s : W → W → Prop) (v : V) :
    Graph.Used (unionGraph r s) (.inl v) ↔ Graph.Used r v := by
  constructor
  · rintro ⟨w,hw⟩
    cases w with
    | inl w => exact ⟨w,hw⟩
    | inr w => exact hw.elim
  · rintro ⟨w,hw⟩
    exact ⟨.inl w,hw⟩

lemma used_right {V W : Type*} (r : V → V → Prop) (s : W → W → Prop) (v : W) :
    Graph.Used (unionGraph r s) (.inr v) ↔ Graph.Used s v := by
  constructor
  · rintro ⟨w,hw⟩
    cases w with
    | inl w => exact hw.elim
    | inr w => exact ⟨w,hw⟩
  · rintro ⟨w,hw⟩
    exact ⟨.inr w,hw⟩
end BoundaryInsert

namespace BoundarySew
lemma used_iff {V : Type*} (r : V → V → Prop) (a b : V) (active : Prop)
    (ha : active → Graph.Used r a) (hb : active → Graph.Used r b) (v : V) :
    Graph.Used (graph r a b active) v ↔ Graph.Used r v := by
  constructor
  · rintro ⟨w,hw|⟨ht,hw⟩⟩
    · exact ⟨w,hw⟩
    · rcases hw with ⟨rfl,_⟩|⟨rfl,_⟩
      · exact ha ht
      · exact hb ht
  · rintro ⟨w,hw⟩
    exact ⟨w,Or.inl hw⟩
end BoundarySew

namespace TurnDisk

lemma sew_used {n : ℕ} (D : TurnDisk (n+2)) (k : ℕ) (hk : k≤n)
    (hc : Graph.Used D.wiring (D.boundary (BoundaryErase.left k hk)) ↔
      Graph.Used D.wiring (D.boundary (BoundaryErase.right k hk))) (v : D.Vertex) :
    Graph.Used (D.sew k hk).wiring v ↔ Graph.Used D.wiring v :=
  BoundarySew.used_iff _ _ _ _ (fun h=>h) hc.mp v

 

def vertexGauge : {n : ℕ} → (D : TurnDisk n) → D.Vertex → ℤ
  | _,.atom _ g => g
  | _,.insert D _ _ _ g => Sum.elim D.vertexGauge g
  | _,.attach D E _ _ => Sum.elim D.vertexGauge E.vertexGauge
  | _,.sew D _ _ => D.vertexGauge

@[simp] lemma vertexGauge_boundary {boundarySize : ℕ} (D : TurnDisk boundarySize)
    (i : Fin boundarySize) :
    D.vertexGauge (D.boundary i)=D.gauge i := by
  induction D with
  | atom p g => rfl
  | @insert n m D k hk p g ih =>
    obtain ⟨j,rfl⟩|⟨j,rfl⟩:=BoundaryInsert.cover (m:=m) k hk i
    · simp only [boundary,gauge,vertexGauge,BoundaryInsert.boundary_old,
        BoundaryInsert.gauge_old,Sum.elim_inl,ih]
    · simp only [boundary,gauge,vertexGauge,BoundaryInsert.boundary_fresh,
        BoundaryInsert.gauge_fresh,Sum.elim_inr]
      rfl
  | @attach n m D E k hk ih ihE =>
    obtain ⟨j,rfl⟩|⟨j,rfl⟩:=BoundaryInsert.cover (m:=m) k hk i
    · simp only [boundary,gauge,vertexGauge,BoundaryInsert.boundary_old,
        BoundaryInsert.gauge_old,Sum.elim_inl,ih]
    · simp only [boundary,gauge,vertexGauge,BoundaryInsert.boundary_fresh,
        BoundaryInsert.gauge_fresh,Sum.elim_inr,ihE]
  | sew D k hk ih => exact ih _

 

def gate4 {n : ℕ} (D : TurnDisk n) (k : ℕ) (hk : k+4≤n)
    (E : TurnDisk 8) : TurnDisk n :=
  (((D.attach E (k+4) hk).sew (k+3) (by omega)).sew (k+2) (by omega)).sew
    (k+1) (by omega) |>.sew k (by omega)

namespace Gate4
def skip (k i : ℕ) : ℕ := if i<k then i else i+2

def input (i : Fin 4) : Fin 8 := ⟨3-i.val,by omega⟩
def output (i : Fin 4) : Fin 8 := ⟨4+i.val,by omega⟩

lemma finite_four_or (A : Prop) (f : Fin 4 → Prop) :
    ((((A ∨ f 3) ∨ f 2) ∨ f 1) ∨ f 0) ↔ A ∨ ∃ i,f i := by
  constructor
  · rintro ((((h|h)|h)|h)|h)
    · exact Or.inl h
    · exact Or.inr ⟨3,h⟩
    · exact Or.inr ⟨2,h⟩
    · exact Or.inr ⟨1,h⟩
    · exact Or.inr ⟨0,h⟩
  · rintro (h|⟨i,h⟩)
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · fin_cases i
      · exact Or.inr h
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inl (Or.inl (Or.inr h)))

variable {n : ℕ} (D : TurnDisk n) (k : ℕ) (hk : k+4≤n) (E : TurnDisk 8)

abbrev stage0 := D.attach E (k+4) hk
abbrev stage1 := (stage0 D k hk E).sew (k+3) (by omega)
abbrev stage2 := (stage1 D k hk E).sew (k+2) (by omega)
abbrev stage3 := (stage2 D k hk E).sew (k+1) (by omega)

def slot (i : Fin 4) : Fin n := ⟨k+i.val,by omega⟩

lemma stage1_left : (stage0 D k hk E).boundary (BoundaryErase.left (k+3) (by omega))=
    .inl (D.boundary (slot k hk 3)) := by
  apply (BoundaryInsert.boundary_before _ _ _ _ _ (by change k+3+0<k+4; omega)).trans
  rfl

lemma stage1_right : (stage0 D k hk E).boundary (BoundaryErase.right (k+3) (by omega))=
    .inr (E.boundary (input 3)) := by
  rw [boundary,BoundaryInsert.boundary_between _ _ _ _ _ (by change k+4≤k+3+1; omega)
    (by change k+3+1<k+4+8; omega)]
  apply congrArg (Sum.inr ∘ E.boundary)
  apply Fin.ext
  change (k+3+1)-(k+4)=3-3
  omega

lemma stage2_left : (stage1 D k hk E).boundary (BoundaryErase.left (k+2) (by omega))=
    .inl (D.boundary (slot k hk 2)) := by
  have hi : BoundaryErase.keep (k+3) (by omega) (BoundaryErase.left (k+2) (by omega))=
      (⟨k+2,by omega⟩ : Fin (n+8)) := by
    apply Fin.ext
    change (if k+2+0<k+3 then k+2+0 else k+2+0+2)=k+2
    rw [ite_eq_left (by omega)]
  change (stage0 D k hk E).boundary (BoundaryErase.keep (k+3) _ _)=_
  rw [hi]
  apply (BoundaryInsert.boundary_before _ _ _ _ _ (by change k+2<k+4; omega)).trans
  rfl

lemma stage2_right : (stage1 D k hk E).boundary (BoundaryErase.right (k+2) (by omega))=
    .inr (E.boundary (input 2)) := by
  have hi : BoundaryErase.keep (k+3) (by omega) (BoundaryErase.right (k+2) (by omega))=
      (⟨k+5,by omega⟩ : Fin (n+8)) := by
    apply Fin.ext
    change (if k+2+1<k+3 then k+2+1 else k+2+1+2)=k+5
    rw [ite_eq_right (by omega)]
  change (stage0 D k hk E).boundary (BoundaryErase.keep (k+3) _ _)=_
  rw [hi,boundary,BoundaryInsert.boundary_between _ _ _ _ _ (by change k+4≤k+5; omega)
    (by change k+5<k+4+8; omega)]
  apply congrArg (Sum.inr ∘ E.boundary)
  apply Fin.ext
  change (k+5)-(k+4)=3-2
  omega

lemma stage3_left : (stage2 D k hk E).boundary (BoundaryErase.left (k+1) (by omega))=
    .inl (D.boundary (slot k hk 1)) := by
  have hi : BoundaryErase.keep (k+3) (by omega)
      (BoundaryErase.keep (k+2) (by omega) (BoundaryErase.left (k+1) (by omega)))=
      (⟨k+1,by omega⟩ : Fin (n+8)) := by
    apply Fin.ext
    change skip (k+3) (skip (k+2) (k+1))=k+1
    simp (disch := omega) only [skip,ite_eq_left]
  change (stage0 D k hk E).boundary (BoundaryErase.keep (k+3) _ (BoundaryErase.keep (k+2) _ _))=_
  rw [hi]
  apply (BoundaryInsert.boundary_before _ _ _ _ _ (by change k+1<k+4; omega)).trans
  rfl

lemma stage3_right : (stage2 D k hk E).boundary (BoundaryErase.right (k+1) (by omega))=
    .inr (E.boundary (input 1)) := by
  have hi : BoundaryErase.keep (k+3) (by omega)
      (BoundaryErase.keep (k+2) (by omega) (BoundaryErase.right (k+1) (by omega)))=
      (⟨k+6,by omega⟩ : Fin (n+8)) := by
    apply Fin.ext
    change skip (k+3) (skip (k+2) (k+2))=k+6
    simp (disch := omega) only [skip,ite_eq_left,ite_eq_right]
  change (stage0 D k hk E).boundary (BoundaryErase.keep (k+3) _ (BoundaryErase.keep (k+2) _ _))=_
  rw [hi,boundary,BoundaryInsert.boundary_between _ _ _ _ _ (by change k+4≤k+6; omega)
    (by change k+6<k+4+8; omega)]
  apply congrArg (Sum.inr ∘ E.boundary)
  apply Fin.ext
  change (k+6)-(k+4)=3-1
  omega

lemma stage4_left : (stage3 D k hk E).boundary (BoundaryErase.left k (by omega))=
    .inl (D.boundary (slot k hk 0)) := by
  have hi : BoundaryErase.keep (k+3) (by omega) (BoundaryErase.keep (k+2) (by omega)
      (BoundaryErase.keep (k+1) (by omega) (BoundaryErase.left k (by omega))))=
      (⟨k,by omega⟩ : Fin (n+8)) := by
    apply Fin.ext
    change skip (k+3) (skip (k+2) (skip (k+1) k))=k
    simp (disch := omega) only [skip,ite_eq_left]
  change (stage0 D k hk E).boundary
    (BoundaryErase.keep (k+3) _ (BoundaryErase.keep (k+2) _ (BoundaryErase.keep (k+1) _ _)))=_
  rw [hi]
  apply (BoundaryInsert.boundary_before _ _ _ _ _ (by change k<k+4; omega)).trans
  rfl

lemma stage4_right : (stage3 D k hk E).boundary (BoundaryErase.right k (by omega))=
    .inr (E.boundary (input 0)) := by
  have hi : BoundaryErase.keep (k+3) (by omega) (BoundaryErase.keep (k+2) (by omega)
      (BoundaryErase.keep (k+1) (by omega) (BoundaryErase.right k (by omega))))=
      (⟨k+7,by omega⟩ : Fin (n+8)) := by
    apply Fin.ext
    change skip (k+3) (skip (k+2) (skip (k+1) (k+1)))=k+7
    simp (disch := omega) only [skip,ite_eq_left,ite_eq_right]
  change (stage0 D k hk E).boundary
    (BoundaryErase.keep (k+3) _ (BoundaryErase.keep (k+2) _ (BoundaryErase.keep (k+1) _ _)))=_
  rw [hi,boundary,BoundaryInsert.boundary_between _ _ _ _ _ (by change k+4≤k+7; omega)
    (by change k+7<k+4+8; omega)]
  apply congrArg (Sum.inr ∘ E.boundary)
  apply Fin.ext
  change (k+7)-(k+4)=3-0
  omega

lemma boundary_slot (i : Fin 4) :
    (D.gate4 k hk E).boundary (slot k hk i)=.inr (E.boundary (output i)) := by
  have hi : BoundaryErase.keep (k+3) (by omega) (BoundaryErase.keep (k+2) (by omega)
      (BoundaryErase.keep (k+1) (by omega) (BoundaryErase.keep k (by omega) (slot k hk i))))=
      (⟨k+i.val+8,by omega⟩ : Fin (n+8)) := by
    apply Fin.ext
    change skip (k+3) (skip (k+2) (skip (k+1) (skip k (k+i.val))))=k+i.val+8
    simp (disch := omega) only [skip,ite_eq_right]
  change (stage0 D k hk E).boundary
    (BoundaryErase.keep (k+3) _ (BoundaryErase.keep (k+2) _
      (BoundaryErase.keep (k+1) _ (BoundaryErase.keep k _ _))))=_
  rw [hi,boundary,BoundaryInsert.boundary_between _ _ _ _ _ (by change k+4≤k+i.val+8; omega)
    (by change k+i.val+8<k+4+8; omega)]
  apply congrArg (Sum.inr ∘ E.boundary)
  apply Fin.ext
  change (k+i.val+8)-(k+4)=4+i.val
  omega

lemma boundary_outside (i : Fin n) (hi : i.val<k ∨ k+4≤ i.val) :
    (D.gate4 k hk E).boundary i=.inl (D.boundary i) := by
  rcases hi with hi|hi
  · have he : BoundaryErase.keep (k+3) (by omega) (BoundaryErase.keep (k+2) (by omega)
        (BoundaryErase.keep (k+1) (by omega) (BoundaryErase.keep k (by omega) i)))=
        (⟨i.val,by omega⟩ : Fin (n+8)) := by
      apply Fin.ext
      change skip (k+3) (skip (k+2) (skip (k+1) (skip k i.val)))=i.val
      simp (disch := omega) only [skip,ite_eq_left]
    change (stage0 D k hk E).boundary
      (BoundaryErase.keep (k+3) _ (BoundaryErase.keep (k+2) _
        (BoundaryErase.keep (k+1) _ (BoundaryErase.keep k _ _))))=_
    rw [he]
    exact BoundaryInsert.boundary_before _ _ _ _ _ (by change i.val<k+4; omega)
  · have he : BoundaryErase.keep (k+3) (by omega) (BoundaryErase.keep (k+2) (by omega)
        (BoundaryErase.keep (k+1) (by omega) (BoundaryErase.keep k (by omega) i)))=
        (⟨i.val+8,by omega⟩ : Fin (n+8)) := by
      apply Fin.ext
      change skip (k+3) (skip (k+2) (skip (k+1) (skip k i.val)))=i.val+8
      simp (disch := omega) only [skip,ite_eq_right]
    change (stage0 D k hk E).boundary
      (BoundaryErase.keep (k+3) _ (BoundaryErase.keep (k+2) _
        (BoundaryErase.keep (k+1) _ (BoundaryErase.keep k _ _))))=_
    rw [he,boundary,BoundaryInsert.boundary_after _ _ _ _ _ (by change k+4+8≤ i.val+8; omega)]
    rfl

lemma gauge_slot (i : Fin 4) : (D.gate4 k hk E).gauge (slot k hk i)=E.gauge (output i) := by
  rw [←vertexGauge_boundary,boundary_slot]
  exact vertexGauge_boundary E _

lemma gauge_outside (i : Fin n) (hi : i.val<k ∨ k+4≤ i.val) :
    (D.gate4 k hk E).gauge i=D.gauge i := by
  rw [←vertexGauge_boundary,boundary_outside D k hk E i hi]
  exact vertexGauge_boundary D i

variable (hm : ∀ i : Fin 4, Graph.Used D.wiring (D.boundary (slot k hk i)) ↔ Graph.Used E.wiring (E.boundary (input i)))

include hm

lemma match1 : Graph.Used (stage0 D k hk E).wiring
      ((stage0 D k hk E).boundary (BoundaryErase.left (k+3) (by omega))) ↔
    Graph.Used (stage0 D k hk E).wiring
      ((stage0 D k hk E).boundary (BoundaryErase.right (k+3) (by omega))) := by
  rw [stage1_left,stage1_right]
  change Graph.Used (BoundaryInsert.unionGraph D.wiring E.wiring) (.inl _) ↔
    Graph.Used (BoundaryInsert.unionGraph D.wiring E.wiring) (.inr _)
  rw [BoundaryInsert.used_left,BoundaryInsert.used_right]
  exact hm 3

lemma stage1_used (v : D.Vertex ⊕ E.Vertex) :
    Graph.Used (stage1 D k hk E).wiring v ↔ Graph.Used (stage0 D k hk E).wiring v :=
  sew_used _ _ _ (match1 D k hk E hm) v

lemma match2 : Graph.Used (stage1 D k hk E).wiring
      ((stage1 D k hk E).boundary (BoundaryErase.left (k+2) (by omega))) ↔
    Graph.Used (stage1 D k hk E).wiring
      ((stage1 D k hk E).boundary (BoundaryErase.right (k+2) (by omega))) := by
  rw [stage2_left,stage2_right,stage1_used D k hk E hm,stage1_used D k hk E hm]
  change Graph.Used (BoundaryInsert.unionGraph D.wiring E.wiring) (.inl _) ↔
    Graph.Used (BoundaryInsert.unionGraph D.wiring E.wiring) (.inr _)
  rw [BoundaryInsert.used_left,BoundaryInsert.used_right]
  exact hm 2

lemma stage2_used (v : D.Vertex ⊕ E.Vertex) :
    Graph.Used (stage2 D k hk E).wiring v ↔ Graph.Used (stage0 D k hk E).wiring v :=
  (sew_used _ _ _ (match2 D k hk E hm) v).trans (stage1_used D k hk E hm v)

lemma match3 : Graph.Used (stage2 D k hk E).wiring
      ((stage2 D k hk E).boundary (BoundaryErase.left (k+1) (by omega))) ↔
    Graph.Used (stage2 D k hk E).wiring
      ((stage2 D k hk E).boundary (BoundaryErase.right (k+1) (by omega))) := by
  rw [stage3_left,stage3_right,stage2_used D k hk E hm,stage2_used D k hk E hm]
  change Graph.Used (BoundaryInsert.unionGraph D.wiring E.wiring) (.inl _) ↔
    Graph.Used (BoundaryInsert.unionGraph D.wiring E.wiring) (.inr _)
  rw [BoundaryInsert.used_left,BoundaryInsert.used_right]
  exact hm 1

lemma stage3_used (v : D.Vertex ⊕ E.Vertex) :
    Graph.Used (stage3 D k hk E).wiring v ↔ Graph.Used (stage0 D k hk E).wiring v :=
  (sew_used _ _ _ (match3 D k hk E hm) v).trans (stage2_used D k hk E hm v)

lemma match4 : Graph.Used (stage3 D k hk E).wiring
      ((stage3 D k hk E).boundary (BoundaryErase.left k (by omega))) ↔
    Graph.Used (stage3 D k hk E).wiring
      ((stage3 D k hk E).boundary (BoundaryErase.right k (by omega))) := by
  rw [stage4_left,stage4_right,stage3_used D k hk E hm,stage3_used D k hk E hm]
  change Graph.Used (BoundaryInsert.unionGraph D.wiring E.wiring) (.inl _) ↔
    Graph.Used (BoundaryInsert.unionGraph D.wiring E.wiring) (.inr _)
  rw [BoundaryInsert.used_left,BoundaryInsert.used_right]
  exact hm 0

lemma used (v : D.Vertex ⊕ E.Vertex) :
    Graph.Used (D.gate4 k hk E).wiring v ↔ Graph.Used (stage0 D k hk E).wiring v :=
  (sew_used _ _ _ (match4 D k hk E hm) v).trans (stage3_used D k hk E hm v)

lemma compatible (hc : D.Compatible) (hE : E.Compatible)
    (hg : ∀ i : Fin 4,E.gauge (input i)=D.gauge (slot k hk i)-3) :
    (D.gate4 k hk E).Compatible := by
  have hg1 : (stage0 D k hk E).gauge (BoundaryErase.right (k+3) (by omega))=
      (stage0 D k hk E).gauge (BoundaryErase.left (k+3) (by omega))-3 := by
    rw [←vertexGauge_boundary,←vertexGauge_boundary,stage1_right,stage1_left]
    change E.vertexGauge (E.boundary (input 3))=D.vertexGauge (D.boundary (slot k hk 3))-3
    rw [vertexGauge_boundary,vertexGauge_boundary]
    exact hg 3
  have hg2 : (stage1 D k hk E).gauge (BoundaryErase.right (k+2) (by omega))=
      (stage1 D k hk E).gauge (BoundaryErase.left (k+2) (by omega))-3 := by
    rw [←vertexGauge_boundary,←vertexGauge_boundary,stage2_right,stage2_left]
    change E.vertexGauge (E.boundary (input 2))=D.vertexGauge (D.boundary (slot k hk 2))-3
    rw [vertexGauge_boundary,vertexGauge_boundary]
    exact hg 2
  have hg3 : (stage2 D k hk E).gauge (BoundaryErase.right (k+1) (by omega))=
      (stage2 D k hk E).gauge (BoundaryErase.left (k+1) (by omega))-3 := by
    rw [←vertexGauge_boundary,←vertexGauge_boundary,stage3_right,stage3_left]
    change E.vertexGauge (E.boundary (input 1))=D.vertexGauge (D.boundary (slot k hk 1))-3
    rw [vertexGauge_boundary,vertexGauge_boundary]
    exact hg 1
  have hg4 : (stage3 D k hk E).gauge (BoundaryErase.right k (by omega))=
      (stage3 D k hk E).gauge (BoundaryErase.left k (by omega))-3 := by
    rw [←vertexGauge_boundary,←vertexGauge_boundary,stage4_right,stage4_left]
    change E.vertexGauge (E.boundary (input 0))=D.vertexGauge (D.boundary (slot k hk 0))-3
    rw [vertexGauge_boundary,vertexGauge_boundary]
    exact hg 0
  exact ⟨⟨⟨⟨⟨hc,hE⟩,match1 D k hk E hm,hg1⟩,match2 D k hk E hm,hg2⟩,
    match3 D k hk E hm,hg3⟩,match4 D k hk E hm,hg4⟩

 
def wire (v w : D.Vertex ⊕ E.Vertex) : Prop := ∃ i : Fin 4,
  Graph.Used E.wiring (E.boundary (input i)) ∧ ((v=.inl (D.boundary (slot k hk i)) ∧ w=.inr (E.boundary (input i))) ∨
    (v=.inr (E.boundary (input i)) ∧ w=.inl (D.boundary (slot k hk i))))

lemma wiring (v w : D.Vertex ⊕ E.Vertex) :
    (D.gate4 k hk E).wiring v w ↔
      BoundaryInsert.unionGraph D.wiring E.wiring v w ∨ wire D k hk E v w := by
  have h1 : Graph.Used (stage0 D k hk E).wiring (.inl (D.boundary (slot k hk 3))) ↔
      Graph.Used E.wiring (E.boundary (input 3)) := (BoundaryInsert.used_left _ _ _).trans (hm 3)
  have h2 : Graph.Used (stage1 D k hk E).wiring (.inl (D.boundary (slot k hk 2))) ↔
      Graph.Used E.wiring (E.boundary (input 2)) := (stage1_used D k hk E hm _).trans
        ((BoundaryInsert.used_left _ _ _).trans (hm 2))
  have h3 : Graph.Used (stage2 D k hk E).wiring (.inl (D.boundary (slot k hk 1))) ↔
      Graph.Used E.wiring (E.boundary (input 1)) := (stage2_used D k hk E hm _).trans
        ((BoundaryInsert.used_left _ _ _).trans (hm 1))
  have h4 : Graph.Used (stage3 D k hk E).wiring (.inl (D.boundary (slot k hk 0))) ↔
      Graph.Used E.wiring (E.boundary (input 0)) := (stage3_used D k hk E hm _).trans
        ((BoundaryInsert.used_left _ _ _).trans (hm 0))
  change BoundarySew.graph (stage3 D k hk E).wiring _ _ _ v w ↔ _
  simp only [BoundarySew.graph]
  rw [stage4_left,stage4_right,h4]
  change (BoundarySew.graph (stage2 D k hk E).wiring _ _ _ v w ∨ _) ↔ _
  simp only [BoundarySew.graph]
  rw [stage3_left,stage3_right,h3]
  change ((BoundarySew.graph (stage1 D k hk E).wiring _ _ _ v w ∨ _) ∨ _) ↔ _
  simp only [BoundarySew.graph]
  rw [stage2_left,stage2_right,h2]
  change (((BoundarySew.graph (stage0 D k hk E).wiring _ _ _ v w ∨ _) ∨ _) ∨ _) ↔ _
  simp only [BoundarySew.graph]
  rw [stage1_left,stage1_right,h1]
  exact finite_four_or (BoundaryInsert.unionGraph D.wiring E.wiring v w) (fun i=>
    Graph.Used E.wiring (E.boundary (input i)) ∧ ((v=.inl (D.boundary (slot k hk i)) ∧ w=.inr (E.boundary (input i))) ∨
      (v=.inr (E.boundary (input i)) ∧ w=.inl (D.boundary (slot k hk i)))))

end Gate4
end TurnDisk
end
end CriticalStrip.Diagram

end OAI
