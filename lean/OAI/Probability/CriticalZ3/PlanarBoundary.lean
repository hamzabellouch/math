import OAI.Probability.CriticalZ3.FiniteTrails

namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

/-! Oriented planar edge boundary with exact nearest-neighbor conventions. -/
open Classical
namespace PlanarBoundary
abbrev Point := ℤ × ℤ
abbrev Direction := Fin 4

def tailOffset : Direction → Point := ![(0,0),(1,0),(1,1),(0,1)]
def headOffset : Direction → Point := ![(1,0),(1,1),(0,1),(0,0)]
def outward : Direction → Point := ![(0,-1),(1,0),(0,1),(-1,0)]

abbrev Boundary (X : Finset Point) := {e : Point × Direction // e.1 ∈ X ∧ e.1+outward e.2 ∉ X}

noncomputable instance (X : Finset Point) : Fintype (Boundary X) :=
  Fintype.ofInjective (fun e : Boundary X => (⟨e.val.1,e.property.1⟩,e.val.2) : Boundary X → X × Direction)
    (by intro e e' h; apply Subtype.ext; exact Prod.ext (congrArg (fun z => z.1.val) h) (congrArg (fun z : X × Direction => z.2) h))

def tail {X : Finset Point} (e : Boundary X) : Point := e.val.1+tailOffset e.val.2
def head {X : Finset Point} (e : Boundary X) : Point := e.val.1+headOffset e.val.2

noncomputable def atVertex (X : Finset Point) (v : Point) (offset : Direction → Point) :
    {e : Boundary X // e.val.1+offset e.val.2 = v} ≃
      {d : Direction // v-offset d ∈ X ∧ v-offset d+outward d ∉ X} where
  toFun e := ⟨e.val.val.2,by
    have he : e.val.val.1 = v-offset e.val.val.2 := eq_sub_iff_add_eq.mpr e.property
    rw [←he]
    exact e.val.property⟩
  invFun d := ⟨⟨(v-offset d.val,d.val),d.property⟩,sub_add_cancel _ _⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (eq_sub_iff_add_eq.mpr e.property).symm
    · rfl
  right_inv d := by rfl

/-- At each dual vertex incoming and outgoing boundary degrees agree. -/
theorem balanced (X : Finset Point) (v : Point) :
    Fintype.card {e : Boundary X // head e = v} =
      Fintype.card {e : Boundary X // tail e = v} := by
  apply (Fintype.card_congr (atVertex X v headOffset)).trans
  apply Eq.trans _ (Fintype.card_congr (atVertex X v tailOffset)).symm
  simp only [Fintype.card_subtype,Finset.card_filter]
  simp only [Fin.sum_univ_succ,headOffset,tailOffset,outward,Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  have ha : v-(1,0)+(0,-1) = v-(1,1) := by ext <;> simp [sub_eq_add_neg,add_assoc]
  have hb : v-(1,1)+(1,0) = v-(0,1) := by ext <;> simp
  have hc : v-(0,1)+(0,1) = v := sub_add_cancel _ _
  have hd : v+(-1,0) = v-(1,0) := by ext <;> simp [sub_eq_add_neg]
  have he : v+(0,-1) = v-(0,1) := by ext <;> simp [sub_eq_add_neg]
  have hf : v-(1,0)+(1,0) = v := sub_add_cancel _ _
  have hg : v-(1,1)+(0,1) = v-(1,0) := by ext <;> simp
  have hh : v-(0,1)+(-1,0) = v-(1,1) := by ext <;> simp [sub_eq_add_neg,add_assoc]
  simp only [show ((0,0) : Point) = 0 from rfl,sub_zero,ha,hb,hc,hd,he,hf,hg,hh]
  by_cases h0 : v ∈ X <;> by_cases h1 : v-(1,0) ∈ X <;>
    by_cases h2 : v-(1,1) ∈ X <;> by_cases h3 : v-(0,1) ∈ X <;> simp [h0,h1,h2,h3]

theorem head_ne_tail {X : Finset Point} (e : Boundary X) : head e ≠ tail e := by
  intro h
  have he : headOffset e.val.2 = tailOffset e.val.2 := add_left_cancel h
  generalize hd : e.val.2 = d at he
  fin_cases d <;> simp [headOffset,tailOffset] at he

def opposite (d : Direction) : Direction := d+2

theorem opposite_opposite (d : Direction) : opposite (opposite d) = d := by
  fin_cases d <;> decide

theorem outward_opposite (d : Direction) : outward (opposite d) = -outward d := by
  fin_cases d <;> decide

theorem reverse_tail (d : Direction) : outward d+tailOffset (opposite d) = headOffset d := by
  fin_cases d <;> decide

theorem reverse_head (d : Direction) : outward d+headOffset (opposite d) = tailOffset d := by
  fin_cases d <;> decide

/-- Signed intersections with the positive horizontal ray; dual vertex (a,b)
represents the point (a-1/2,b-1/2). -/
def rayFlux (a b : Point) : ℤ :=
  (if a.2 = 0 ∧ b.2 = 1 ∧ 0 < a.1 then 1 else 0) -
  (if b.2 = 0 ∧ a.2 = 1 ∧ 0 < b.1 then 1 else 0)

theorem rayFlux_reverse (a b : Point) : rayFlux b a = -rayFlux a b := by
  unfold rayFlux
  ring

def sideFlux (cell : Point) (d : Direction) : ℤ :=
  rayFlux (cell+tailOffset d) (cell+headOffset d)

theorem sideFlux_reverse (cell : Point) (d : Direction) :
    sideFlux (cell+outward d) (opposite d) = -sideFlux cell d := by
  unfold sideFlux
  simp only [add_assoc,reverse_tail,reverse_head]
  exact rayFlux_reverse _ _

/-- The oriented boundary of one unit cell has ray intersection number one
exactly when it contains the ray's origin. No Jordan curve theorem is assumed. -/
theorem cell_flux (cell : Point) :
    (∑ d : Direction, sideFlux cell d) = if cell = (0,0) then 1 else 0 := by
  rcases cell with ⟨x,y⟩
  simp only [Fin.sum_univ_succ]
  simp [sideFlux,rayFlux,tailOffset,headOffset,Prod.ext_iff]
  split_ifs <;> omega

abbrev FullSide (X : Finset Point) := X × Direction

def isInternal {X : Finset Point} (e : FullSide X) : Prop := e.1.val+outward e.2 ∈ X

noncomputable def internalReverse (X : Finset Point) :
    {e : FullSide X // isInternal e} ≃ {e : FullSide X // isInternal e} := by
  let f : {e : FullSide X // isInternal e} → {e : FullSide X // isInternal e} :=
    fun e => ⟨(⟨e.val.1.val+outward e.val.2,e.property⟩,opposite e.val.2),by
      change e.val.1.val+outward e.val.2+outward (opposite e.val.2) ∈ X
      rw [outward_opposite,add_neg_cancel_right]
      exact e.val.1.property⟩
  have hf : Function.Involutive f := by
    intro e
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact by simp [f,outward_opposite]
    · exact opposite_opposite _
  exact ⟨f,f,hf,hf⟩

theorem internal_flux_zero (X : Finset Point) :
    (∑ e : {e : FullSide X // isInternal e}, sideFlux e.val.1.val e.val.2) = 0 := by
  let F : {e : FullSide X // isInternal e} → ℤ := fun e => sideFlux e.val.1.val e.val.2
  have hs := (internalReverse X).sum_comp F
  have he : (∑ e, F (internalReverse X e)) = -(∑ e, F e) := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro e _
    exact sideFlux_reverse _ _
  rw [he] at hs
  dsimp [F] at hs
  omega

noncomputable def boundaryEquiv (X : Finset Point) :
    Boundary X ≃ {e : FullSide X // ¬isInternal e} where
  toFun e := ⟨(⟨e.val.1,e.property.1⟩,e.val.2),e.property.2⟩
  invFun e := ⟨(e.val.1.val,e.val.2),e.val.1.property,e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The whole finite boundary has nonzero positive-ray intersection number. -/
theorem boundary_flux (X : Finset Point) :
    (∑ e : Boundary X, rayFlux (tail e) (head e)) = if (0,0) ∈ X then 1 else 0 := by
  have hfull : (∑ e : FullSide X, sideFlux e.1.val e.2) = if (0,0) ∈ X then 1 else 0 := by
    rw [Fintype.sum_prod_type]
    simp_rw [cell_flux]
    rw [←Finset.sum_subtype X (by simp) (fun cell => if cell = (0,0) then (1 : ℤ) else 0)]
    simp
  have hpart : (∑ e : {e : FullSide X // isInternal e}, sideFlux e.val.1.val e.val.2) +
      (∑ e : {e : FullSide X // ¬isInternal e}, sideFlux e.val.1.val e.val.2) =
      ∑ e : FullSide X, sideFlux e.1.val e.2 := by
    have h₁ := Finset.sum_subtype (F := inferInstance) (Finset.univ.filter (isInternal (X := X)))
      (by simp : ∀ e : FullSide X, e ∈ Finset.univ.filter isInternal ↔ isInternal e)
      (fun e : FullSide X => sideFlux e.1.val e.2)
    have h₂ := Finset.sum_subtype (F := inferInstance) (Finset.univ.filter (fun e : FullSide X => ¬isInternal e))
      (by simp : ∀ e : FullSide X, e ∈ Finset.univ.filter (fun e => ¬isInternal e) ↔ ¬isInternal e)
      (fun e : FullSide X => sideFlux e.1.val e.2)
    rw [←h₁,←h₂]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  rw [internal_flux_zero,zero_add] at hpart
  rw [←hfull,←hpart]
  exact (boundaryEquiv X).sum_comp (fun e => sideFlux e.val.1.val e.val.2)

end PlanarBoundary

namespace PlanarBoundary
open Classical

def Neighbor (a b : Point) : Prop := ∃ d : Direction, b = a+outward d

theorem side_neighbor (cell : Point) (d : Direction) :
    Neighbor (cell+tailOffset d) (cell+headOffset d) := by
  refine ⟨d+1,?_⟩
  fin_cases d <;> ext <;> simp [headOffset,tailOffset,outward]

theorem head_neighbor {X : Finset Point} (e : Boundary X) : Neighbor (tail e) (head e) :=
  side_neighbor _ _

theorem neighbor_coord {a b : Point} (h : Neighbor a b) : |b.1-a.1| ≤ 1 := by
  obtain ⟨d,rfl⟩ := h
  fin_cases d <;> simp [outward]

def lineFlux (a b : Point) : ℤ := (if 1 ≤ b.2 then 1 else 0)-(if 1 ≤ a.2 then 1 else 0)

theorem rayFlux_eq_lineFlux {a b : Point} (h : Neighbor a b) :
    rayFlux a b = if 0 < a.1 then lineFlux a b else 0 := by
  obtain ⟨d,rfl⟩ := h
  rcases a with ⟨x,y⟩
  fin_cases d <;> simp [outward,rayFlux,lineFlux] <;> split_ifs <;> omega

theorem next_eq_rotate {n : ℕ} (hn : 0 < n) (i : Fin n) :
    FiniteTrails.next hn i = finRotate n i := by
  ext
  simp [FiniteTrails.next,finRotate_apply,Fin.add_def,Nat.add_mod_mod]

theorem lineFlux_sum_zero {n : ℕ} (hn : 0 < n) (v : Fin n → Point) :
    (∑ i, lineFlux (v i) (v (FiniteTrails.next hn i))) = 0 := by
  simp only [lineFlux,Finset.sum_sub_distrib,next_eq_rotate]
  exact sub_eq_zero.mpr (Equiv.sum_comp (finRotate n) (fun i => if 1 ≤ (v i).2 then (1 : ℤ) else 0))

/-- Nonzero positive-ray flux forces a crossing on each side of the vertical axis. -/
theorem two_sides {n : ℕ} (hn : 0 < n) (v : Fin n → Point)
    (hedge : ∀ i, Neighbor (v i) (v (FiniteTrails.next hn i)))
    (hw : (∑ i, rayFlux (v i) (v (FiniteTrails.next hn i))) ≠ 0) :
    (∃ i, 0 < (v i).1 ∧ rayFlux (v i) (v (FiniteTrails.next hn i)) ≠ 0) ∧
      ∃ j, (v j).1 ≤ 0 := by
  constructor
  · obtain ⟨i,_,hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
    refine ⟨i,?_,hi⟩
    by_contra! hh
    exact hi (by rw [rayFlux_eq_lineFlux (hedge i),ite_eq_right (not_lt.mpr hh)])
  · by_contra! hh
    have he : (∑ i, rayFlux (v i) (v (FiniteTrails.next hn i))) = 0 := by
      simp_rw [rayFlux_eq_lineFlux (hedge _),ite_eq_left (hh _)]
      exact lineFlux_sum_zero hn v
    exact hw he

/-- A coarse diameter bound adequate for the same Peierls argument. -/
theorem coordinate_diameter {n : ℕ} (hn : 0 < n) (v : Fin n → Point)
    (hedge : ∀ i, Neighbor (v i) (v (FiniteTrails.next hn i))) (i j : Fin n) :
    (v i).1-(v j).1 < 2*(n : ℤ) := by
  let a : ℕ → ℤ := fun k => (v ⟨k%n,Nat.mod_lt _ hn⟩).1
  have hs (k : ℕ) : |a (k+1)-a k| ≤ 1 := by
    have he : FiniteTrails.next hn ⟨k%n,Nat.mod_lt _ hn⟩ =
        (⟨(k+1)%n,Nat.mod_lt _ hn⟩ : Fin n) := by
      ext
      exact Nat.mod_add_mod k n 1
    simpa only [he] using neighbor_coord (hedge ⟨k%n,Nat.mod_lt _ hn⟩)
  have hb (k : ℕ) : |a k-a 0| ≤ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        |a (k+1)-a 0| ≤ |a (k+1)-a k|+|a k-a 0| := abs_sub_le _ _ _
        _ ≤ 1+(k : ℤ) := add_le_add (hs k) ih
        _ = (k+1 : ℕ) := by omega
  have hi := (abs_le.mp (hb i.val)).2
  have hj := (abs_le.mp (hb j.val)).1
  dsimp [a] at hi hj
  simp only [Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt,Fin.eta] at hi hj
  have hin : (i.val : ℤ) < n := by exact_mod_cast i.isLt
  have hjn : (j.val : ℤ) < n := by exact_mod_cast j.isLt
  omega

/-- Every finite region containing zero contains an edge-simple closed boundary
trail with a positive-ray anchor of coordinate less than 2n. This deliberately
uses a harmless overcount rather than an unformalized Jordan theorem. -/
theorem exists_anchored_trail (X : Finset Point) (hX : (0,0) ∈ X) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∃ e : Fin n → Boundary X,
      Function.Injective e ∧
      (∀ i, tail (e (FiniteTrails.next hn i)) = head (e i)) ∧
      ∃ i, 0 < (tail (e i)).1 ∧ (tail (e i)).1 < 2*(n : ℤ) ∧
        rayFlux (tail (e i)) (head (e i)) ≠ 0 := by
  have hw : (∑ e : Boundary X, rayFlux (tail e) (head e)) ≠ 0 := by
    rw [boundary_flux,ite_eq_left hX]
    norm_num
  obtain ⟨n,hn,e,he,hnext,hsum⟩ :=
    FiniteTrails.exists_closed_trail tail head (fun v => by
      simpa only [←Nat.card_eq_fintype_card] using balanced X v) (fun e => rayFlux (tail e) (head e)) hw
  let v : Fin n → Point := fun i => tail (e i)
  have hed : ∀ i, Neighbor (v i) (v (FiniteTrails.next hn i)) := by
    intro i
    dsimp [v]
    rw [hnext]
    exact head_neighbor _
  have hs : (∑ i, rayFlux (v i) (v (FiniteTrails.next hn i))) ≠ 0 := by
    simpa only [v,hnext] using hsum
  obtain ⟨⟨i,hi,hir⟩,j,hj⟩ := two_sides hn v hed hs
  have hd := coordinate_diameter hn v hed i j
  change (tail (e i)).1-(tail (e j)).1 < 2*(n : ℤ) at hd
  change (tail (e j)).1 ≤ 0 at hj
  refine ⟨n,hn,e,he,hnext,i,hi,by omega,?_⟩
  simpa only [v,hnext] using hir

end PlanarBoundary

namespace PlanarBoundary
open Classical

abbrev Code (n : ℕ) := Fin (2*n) × Bool × (Fin n → Direction)

def anchor {n : ℕ} (c : Code n) : Point := (c.1.val,if c.2.1 then 0 else 1)

def wordAt {n : ℕ} (w : Fin n → Direction) (k : ℕ) : Direction :=
  if hk : k < n then w ⟨k,hk⟩ else 0

def displacement (d : Direction) : Point := headOffset d-tailOffset d

def tracePosition {n : ℕ} (c : Code n) (k : ℕ) : Point :=
  anchor c+∑ j ∈ Finset.range k, displacement (wordAt c.2.2 j)

def traceSide {n : ℕ} (c : Code n) (i : Fin n) : Point × Direction :=
  (tracePosition c i.val-tailOffset (c.2.2 i),c.2.2 i)

theorem trace_succ {n : ℕ} (c : Code n) (k : ℕ) :
    tracePosition c (k+1) = tracePosition c k+displacement (wordAt c.2.2 k) := by
  simp only [tracePosition,Finset.sum_range_succ,add_assoc]

theorem trace_reconstruct {n : ℕ} (hn : 0 < n) {X : Finset Point}
    (e : Fin n → Boundary X) (he : ∀ i, tail (e (FiniteTrails.next hn i)) = head (e i))
    (c : Code n) (hanchor : anchor c = tail (e ⟨0,hn⟩))
    (hword : ∀ i, c.2.2 i = (e i).val.2) :
    ∀ i, traceSide c i = (e i).val := by
  have ht (k : ℕ) (hk : k < n) : tracePosition c k = tail (e ⟨k,hk⟩) := by
    induction k with
    | zero => simpa only [tracePosition,Finset.range_zero,Finset.sum_empty,add_zero] using hanchor
    | succ k ih =>
      have hkn : k < n := Nat.lt_trans (Nat.lt_succ_self _) hk
      rw [trace_succ,ih hkn]
      simp only [wordAt,dite_eq_left hkn,hword,displacement]
      have hx := he ⟨k,hkn⟩
      have hnxt : FiniteTrails.next hn ⟨k,hkn⟩ = (⟨k+1,hk⟩ : Fin n) := by
        ext
        exact Nat.mod_eq_of_lt hk
      rw [hnxt] at hx
      rw [hx]
      simp only [tail,head]
      abel
  intro i
  rw [traceSide,ht,hword]
  apply Prod.ext
  · exact add_sub_cancel_right _ _
  · rfl

def shiftIndex {n : ℕ} (hn : 0 < n) (a i : Fin n) : Fin n :=
  ⟨(i.val+a.val)%n,Nat.mod_lt _ hn⟩

theorem shiftIndex_injective {n : ℕ} (hn : 0 < n) (a : Fin n) :
    Function.Injective (shiftIndex hn a) := by
  intro i j he
  have h : (i+a : Fin n) = j+a := by
    apply Fin.ext
    exact congrArg Fin.val he
  exact add_right_cancel h

theorem shiftIndex_next {n : ℕ} (hn : 0 < n) (a i : Fin n) :
    shiftIndex hn a (FiniteTrails.next hn i) = FiniteTrails.next hn (shiftIndex hn a i) := by
  ext
  simp only [shiftIndex,FiniteTrails.next,Nat.mod_add_mod]
  congr 1
  omega

theorem rayFlux_ne_zero_height {a b : Point} (h : rayFlux a b ≠ 0) : a.2 = 0 ∨ a.2 = 1 := by
  unfold rayFlux at h
  split_ifs at h <;> aesop

/-- The finite deterministic code family has at most 4n4^n members. -/
theorem card_code (n : ℕ) : Fintype.card (Code n) = 4*n*4^n := by
  simp only [Code,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Fintype.card_fun,Direction]
  ring

/-- Every actual boundary supplies one of these finitely encoded trails. -/
theorem exists_boundary_code (X : Finset Point) (hX : (0,0) ∈ X) :
    ∃ n : ℕ, ∃ _hn : 0 < n, ∃ c : Code n, ∃ e : Fin n → Boundary X,
      Function.Injective e ∧ ∀ i, traceSide c i = (e i).val := by
  obtain ⟨n,hn,e,he,hnext,a,ha0,haN,ha⟩ := exists_anchored_trail X hX
  let e' : Fin n → Boundary X := fun i => e (shiftIndex hn a i)
  have he' : Function.Injective e' := he.comp (shiftIndex_injective hn a)
  have hs' (i : Fin n) : tail (e' (FiniteTrails.next hn i)) = head (e' i) := by
    dsimp [e']
    rw [shiftIndex_next,hnext]
  have hz : e' ⟨0,hn⟩ = e a := by
    dsimp [e']
    congr 1
    apply Fin.ext
    simpa only [shiftIndex,Nat.zero_add] using Nat.mod_eq_of_lt a.isLt
  let x := (tail (e a)).1
  have hx0 : 0 ≤ x := le_of_lt ha0
  have hxn : x.toNat < 2*n := by omega
  obtain hy | hy := rayFlux_ne_zero_height ha
  · let c : Code n := (⟨x.toNat,hxn⟩,true,fun i => (e' i).val.2)
    refine ⟨n,hn,c,e',he',trace_reconstruct hn e' hs' c ?_ (fun _ => rfl)⟩
    rw [hz]
    apply Prod.ext
    · exact Int.toNat_of_nonneg hx0
    · exact hy.symm
  · let c : Code n := (⟨x.toNat,hxn⟩,false,fun i => (e' i).val.2)
    refine ⟨n,hn,c,e',he',trace_reconstruct hn e' hs' c ?_ (fun _ => rfl)⟩
    rw [hz]
    apply Prod.ext
    · exact Int.toNat_of_nonneg hx0
    · exact hy.symm

end PlanarBoundary

end OAI
