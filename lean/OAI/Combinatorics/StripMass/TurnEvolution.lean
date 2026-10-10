import Mathlib
import OAI.Combinatorics.StripMass.TurnRhombus

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace TurnNetwork
open TurnDisk

 
def lift {n s t : ℕ} (h : s ≤ t) : Node n s → Node n t
  | .inl i => .inl i
  | .inr (i,v) => .inr (i.castLE h,v)

lemma lift_refl {n t : ℕ} (v : Node n t) : lift (le_refl t) v=v := by
  rcases v with i|⟨i,v⟩ <;> rfl
lemma lift_trans {n r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t) (v : Node n r) :
    lift hst (lift hrs v)=lift (hrs.trans hst) v := by
  rcases v with i|⟨i,v⟩ <;> rfl
lemma lift_old {n s t : ℕ} (h : s ≤ t) (v : Node n s) :
    old (lift h v)=lift (h.trans (Nat.le_succ t)) v := by
  rcases v with i|⟨i,v⟩ <;> rfl
lemma old_eq_lift {n t : ℕ} (v : Node n t) : old v=lift (Nat.le_succ t) v := by
  rcases v with i|⟨i,v⟩ <;> rfl
lemma lift_injective {n s t : ℕ} (h : s ≤ t) : Function.Injective (lift (n:=n) h) := by
  rintro (i|⟨i,v⟩) (j|⟨j,w⟩) he <;> simp only [lift,Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq] at he
  · exact congrArg Sum.inl he
  · cases he
  · cases he
  · obtain ⟨he,rfl⟩:=he
    have hj : i=j := Fin.ext (congrArg (fun i : Fin t=>i.val) he)
    subst j
    rfl

variable {n : ℕ} (p₀ : Pairing n) (g₀ : Fin n → ℤ)
  (p q : ℕ → Pairing 6) (k : ℕ → ℕ) (hk : ∀ t,k t+4 ≤ n)

lemma lift_edge {s t : ℕ} (hst : s ≤ t) {v w : Node n s}
    (h : graph p₀ g₀ p q k hk s v w) :
    graph p₀ g₀ p q k hk t (lift hst v) (lift hst w) := by
  induction t,hst using Nat.le_induction with
  | base => simpa only [lift_refl] using h
  | succ t hst ih => simpa only [lift_old] using old_edge p₀ g₀ p q k hk t ih

lemma lift_turn {s t : ℕ} (hst : s ≤ t) {v w : Node n s}
    (h : graph p₀ g₀ p q k hk s v w) :
    edgeTurn p₀ g₀ p q k hk t (lift hst v) (lift hst w)=
      edgeTurn p₀ g₀ p q k hk s v w := by
  induction t,hst using Nat.le_induction with
  | base => simp only [lift_refl]
  | succ t hst ih =>
    simpa only [lift_old] using (old_turn p₀ g₀ p q k hk t (lift_edge p₀ g₀ p q k hk hst h)).trans ih

lemma boundary_untouched {s t : ℕ} (hst : s ≤ t) (i : Fin n)
    (hi : ∀ u,s ≤ u → u<t → i.val<k u ∨ k u+4  ≤  i.val) :
    boundary p₀ g₀ p q k hk t i=lift hst (boundary p₀ g₀ p q k hk s i) := by
  induction t,hst using Nat.le_induction with
  | base => exact (lift_refl _).symm
  | succ t hst ih =>
    rw [boundary_outside p₀ g₀ p q k hk t i (hi t hst (by omega)),
      ih (fun u hu hut=>hi u hu (by omega)),lift_old]

lemma boundary_last {s t : ℕ} (hst : s<t) (i : Fin 4)
    (hi : ∀ u,s+1 ≤ u → u<t → (Gate4.slot (k s) (hk s) i).val<k u ∨
      k u+4 ≤ (Gate4.slot (k s) (hk s) i).val) :
    boundary p₀ g₀ p q k hk t (Gate4.slot (k s) (hk s) i)=
      .inr (⟨s,hst⟩,.inr ⟨2+i.val,by omega⟩) := by
  rw [boundary_untouched p₀ g₀ p q k hk (by omega : s+1 ≤ t) _ hi,
    boundary_slot]
  rfl

lemma gauge_untouched {s t : ℕ} (hst : s ≤ t) (i : Fin n)
    (hi : ∀ u,s ≤ u → u<t → i.val<k u ∨ k u+4  ≤  i.val) :
    (disk p₀ g₀ p q k hk t).gauge i=(disk p₀ g₀ p q k hk s).gauge i := by
  induction t,hst using Nat.le_induction with
  | base => rfl
  | succ t hst ih =>
    change ((disk p₀ g₀ p q k hk t).gate4 _ _ _).gauge i=_
    rw [Gate4.gauge_outside _ _ _ _ i (hi t hst (by omega))]
    exact ih (fun u hu hut=>hi u hu (by omega))

lemma gauge_slot (t : ℕ) (i : Fin 4) :
    (disk p₀ g₀ p q k hk (t+1)).gauge (Gate4.slot (k t) (hk t) i)=
      if i.val<2 then -2 else 0 := by
  change ((disk p₀ g₀ p q k hk t).gate4 _ _ _).gauge _=_
  rw [Gate4.gauge_slot,Rhombus.gauge_output]

 
def namedGauge (t : ℕ) : Node n t → ℤ
  | .inl i=>g₀ i
  | .inr (_, .inl i)=>Rhombus.upGauge i
  | .inr (_, .inr i)=>Rhombus.downGauge i

lemma namedGauge_old (t : ℕ) (v : Node n t) : namedGauge g₀ (t+1) (old v)=namedGauge g₀ t v := by
  rcases v with i|⟨i,(v|v)⟩ <;> rfl
lemma namedGauge_lift {s t : ℕ} (hst : s ≤ t) (v : Node n s) :
    namedGauge g₀ t (lift hst v)=namedGauge g₀ s v := by
  rcases v with i|⟨i,(v|v)⟩ <;> rfl
lemma namedGauge_vertex (t : ℕ) (v : Node n t) :
    (disk p₀ g₀ p q k hk t).vertexGauge ((names p₀ g₀ p q k hk t).symm v)=namedGauge g₀ t v := by
  induction t with
  | zero => rcases v with i|⟨i,v⟩; rfl; exact Fin.elim0 i
  | succ t ih =>
    obtain ⟨v,rfl⟩|⟨v,rfl⟩:=cover v
    · rw [inv_old,namedGauge_old]
      exact ih v
    · rw [inv_fresh]
      cases v <;> rfl
lemma namedGauge_boundary (t : ℕ) (i : Fin n) :
    namedGauge g₀ t (boundary p₀ g₀ p q k hk t i)=(disk p₀ g₀ p q k hk t).gauge i := by
  rw [←namedGauge_vertex p₀ g₀ p q k hk]
  simp only [boundary,Equiv.symm_apply_apply,vertexGauge_boundary]

 
def Matches (t : ℕ) : Prop :=
  (∀ u,u<t → ∀ i : Fin 2,(p u).Occupied ⟨4+i.val,by omega⟩ ↔
    (q u).Occupied ⟨1-i.val,by omega⟩) ∧
  (∀ u,u<t → ∀ i : Fin 4,Occupied p₀ p q u (boundary p₀ g₀ p q k hk u
    (Gate4.slot (k u) (hk u) i)) ↔ (p u).Occupied ⟨3-i.val,by omega⟩)

lemma Matches.mono {s t : ℕ} (h : Matches p₀ g₀ p q k hk t) (hst : s ≤ t) :
    Matches p₀ g₀ p q k hk s :=
  ⟨fun u hu=>h.1 u (hu.trans_le hst),fun u hu=>h.2 u (hu.trans_le hst)⟩

lemma occupied_iff_used (t : ℕ) (hm : Matches p₀ g₀ p q k hk t) (v : Node n t) :
    Graph.Used (graph p₀ g₀ p q k hk t) v ↔ Occupied p₀ p q t v := by
  induction t with
  | zero =>
    rcases v with i|⟨i,v⟩
    · rw [used_equiv]
      rfl
    · exact Fin.elim0 i
  | succ t ih =>
    have hm' : ∀ i : Fin 4,Graph.Used (disk p₀ g₀ p q k hk t).wiring
        ((disk p₀ g₀ p q k hk t).boundary (Gate4.slot (k t) (hk t) i)) ↔
          Graph.Used (Rhombus.disk (p t) (q t)).wiring
            ((Rhombus.disk (p t) (q t)).boundary (Gate4.input i)) := by
      intro i
      have hu := (used_equiv p₀ g₀ p q k hk t
        (boundary p₀ g₀ p q k hk t (Gate4.slot (k t) (hk t) i)))
      simp only [boundary,Equiv.symm_apply_apply] at hu
      erw [←hu,ih (Matches.mono _ _ _ _ _ _ hm (by omega)),hm.2 t (by omega),Rhombus.input_boundary,
        Rhombus.used _ _ (hm.1 t (by omega))]
      exact (BoundaryInsert.used_left (p t).Adj (q t).Adj _).symm
    obtain ⟨w,rfl⟩|⟨w,rfl⟩:=cover v
    · rw [occupied_old,used_equiv,inv_old]
      change Graph.Used ((disk p₀ g₀ p q k hk t).gate4 _ _ _).wiring _ ↔ _
      erw [Gate4.used _ _ _ _ hm',BoundaryInsert.used_left,←used_equiv]
      exact ih (Matches.mono _ _ _ _ _ _ hm (by omega)) w
    · rw [occupied_fresh,used_equiv,inv_fresh]
      change Graph.Used ((disk p₀ g₀ p q k hk t).gate4 _ _ _).wiring _ ↔ _
      erw [Gate4.used _ _ _ _ hm',BoundaryInsert.used_right,Rhombus.used _ _ (hm.1 t (by omega))]
      cases w with
      | inl i => exact BoundaryInsert.used_left _ _ _
      | inr i => exact BoundaryInsert.used_right _ _ _

lemma gate_matches (t : ℕ) (hm : Matches p₀ g₀ p q k hk (t+1)) :
    ∀ i : Fin 4,Graph.Used (disk p₀ g₀ p q k hk t).wiring
        ((disk p₀ g₀ p q k hk t).boundary (Gate4.slot (k t) (hk t) i)) ↔
          Graph.Used (Rhombus.disk (p t) (q t)).wiring
            ((Rhombus.disk (p t) (q t)).boundary (Gate4.input i)) := by
  intro i
  have hu := (used_equiv p₀ g₀ p q k hk t
    (boundary p₀ g₀ p q k hk t (Gate4.slot (k t) (hk t) i)))
  simp only [boundary,Equiv.symm_apply_apply] at hu
  erw [←hu,occupied_iff_used _ _ _ _ _ _ _ (Matches.mono _ _ _ _ _ _ hm (by omega)),hm.2 t (by omega),
    Rhombus.input_boundary,Rhombus.used _ _ (hm.1 t (by omega))]
  exact (BoundaryInsert.used_left (p t).Adj (q t).Adj _).symm

lemma compatible (t : ℕ) (hm : Matches p₀ g₀ p q k hk t)
    (hg : ∀ u,u<t → ∀ i : Fin 4,
      (disk p₀ g₀ p q k hk u).gauge (Gate4.slot (k u) (hk u) i)=
        if i.val<2 then 0 else -2) :
    (disk p₀ g₀ p q k hk t).Compatible := by
  induction t with
  | zero => trivial
  | succ t ih =>
    apply Gate4.compatible _ _ _ _ (gate_matches p₀ g₀ p q k hk t hm)
      (ih (Matches.mono _ _ _ _ _ _ hm (by omega)) (fun u hu=>hg u (by omega)))
      (Rhombus.compatible _ _ (hm.1 t (by omega)))
    intro i
    rw [Rhombus.gauge_input,hg t (by omega)]
    split_ifs <;> rfl

lemma wire_edge (t : ℕ) (hm : Matches p₀ g₀ p q k hk (t+1)) (i : Fin 4)
    (hi : (p t).Occupied ⟨3-i.val,by omega⟩) :
    graph p₀ g₀ p q k hk (t+1)
      (old (boundary p₀ g₀ p q k hk t (Gate4.slot (k t) (hk t) i)))
      (fresh (.inl ⟨3-i.val,by omega⟩)) := by
  unfold graph
  rw [inv_old,inv_fresh]
  simp only [boundary,Equiv.symm_apply_apply]
  apply (Gate4.wiring _ _ _ _ (gate_matches p₀ g₀ p q k hk t hm) _ _).mpr
  right
  refine ⟨i,?_,Or.inl ⟨rfl,?_⟩⟩
  · erw [Rhombus.input_boundary,Rhombus.used _ _ (hm.1 t (by omega)),BoundaryInsert.used_left]
    exact hi
  · rw [Rhombus.input_boundary]
    rfl

end TurnNetwork

 

 

namespace TurnRectangle
open TurnDisk TurnNetwork
section BoundaryEvolution

def width (M N : ℕ) : ℕ := 2*(M+N)
def ports (M N : ℕ) : ℕ := 2*width M N
 

def position (M N t : ℕ) : ℕ := width M N+2*(M-1-t/N+t%N)

lemma position_bound {M N : ℕ} (hM : 1 ≤ M) (hN : 1 ≤ N) (t : ℕ) :
    position M N t+4 ≤ ports M N := by
  have hs : M-1-t/N ≤ M-1 := Nat.sub_le _ _
  have h:=Nat.mod_lt t (by omega : 0<N)
  dsimp [position,ports,width]
  omega
lemma position_time {M N c r : ℕ} (hN : 1 ≤ N) (hr : r<N) :
    position M N (c*N+r)=width M N+2*(M-1-c+r) := by
  have hd : (c*N+r)/N=c := by
    rw [Nat.mul_comm c N,Nat.mul_add_div (by omega),Nat.div_eq_of_lt hr,Nat.add_zero]
  have hm : (c*N+r)%N=r := by
    rw [Nat.mul_comm c N,Nat.mul_add_mod,Nat.mod_eq_of_lt hr]
  simp only [position,hd,hm]
lemma time_lt {M N c r : ℕ} (hr : r<N) (hc : c<M) : c*N+r<M*N := by
  calc
    c*N+r < c*N+N := Nat.add_lt_add_left hr _
    _ = (c+1)*N := by ring
    _ ≤ M*N := Nat.mul_le_mul_right N (by omega)

variable {M N : ℕ} (hM : 1 ≤ M) (hN : 1 ≤ N)
  (p₀ : Pairing (ports M N)) (g₀ : Fin (ports M N) → ℤ) (p q : ℕ → Pairing 6)

abbrev box (t : ℕ) := disk p₀ g₀ p q (position M N) (position_bound hM hN) t
abbrev bdry (t : ℕ) := boundary p₀ g₀ p q (position M N) (position_bound hM hN) t

def southSlot {c r : ℕ} (_hc : c<M) (_hr : r<N) (l : Fin 2) : Fin (ports M N) :=
  Gate4.slot (position M N (c*N+r)) (position_bound hM hN _) ⟨l.val,by omega⟩
def westSlot {c r : ℕ} (_hc : c<M) (_hr : r<N) (l : Fin 2) : Fin (ports M N) :=
  Gate4.slot (position M N (c*N+r)) (position_bound hM hN _) ⟨2+l.val,by omega⟩

lemma southSlot_val {c r : ℕ} (hc : c<M) (hr : r<N) (l : Fin 2) :
    (southSlot hM hN hc hr l).val=width M N+2*(M-1-c+r)+l.val := by
  change position M N (c*N+r)+l.val=_
  rw [position_time hN hr]
lemma westSlot_val {c r : ℕ} (hc : c<M) (hr : r<N) (l : Fin 2) :
    (westSlot hM hN hc hr l).val=width M N+2*(M-1-c+r)+2+l.val := by
  change position M N (c*N+r)+(2+l.val)=_
  rw [position_time hN hr]
  omega

omit p₀ g₀ p q
lemma south_initial_untouched {c u : ℕ} (hc : c<M) (hu : u<c*N) (l : Fin 2) :
    (southSlot hM hN hc (by omega : 0<N) l).val<position M N u := by
  have hc' : u/N<c := (Nat.div_lt_iff_lt_mul (by omega : 0<N)).mpr (by simpa only [Nat.mul_comm] using hu)
  rw [southSlot_val]
  dsimp only [position]
  omega

lemma west_initial_untouched {r u : ℕ} (hr : r<N) (hu : u<r) (l : Fin 2) :
    position M N u+4 ≤ (westSlot hM hN (by omega : 0<M) hr l).val := by
  have hd : u/N=0 := Nat.div_eq_of_lt (hu.trans hr)
  have hm : u%N=u := Nat.mod_eq_of_lt (hu.trans hr)
  rw [westSlot_val]
  dsimp only [position]
  rw [hd,hm]
  omega

lemma west_previous_untouched {c r u : ℕ} (hc : c<M) (hc0 : 0<c) (hr : r<N)
    (hu₁ : (c-1)*N+r+1 ≤ u) (hu₂ : u<c*N+r) (l : Fin 2) :
    (westSlot hM hN hc hr l).val<position M N u ∨
      position M N u+4 ≤ (westSlot hM hN hc hr l).val := by
  have hN0 : 0<N := by omega
  have hcN : (c-1)*N+N=c*N := by
    calc
      (c-1)*N+N=(c-1+1)*N := by ring
      _ = c*N := by congr 1; omega
  have hdlo : c-1 ≤ u/N := (Nat.le_div_iff_mul_le hN0).mpr (by omega)
  have hdhi : u/N ≤ c := by
    have hu : u<(c+1)*N := by rw [Nat.add_mul]; omega
    have hh:=(Nat.div_lt_iff_lt_mul hN0).mpr (by simpa only [Nat.mul_comm] using hu)
    omega
  have hdivision:=Nat.mod_add_div u N
  rw [westSlot_val]
  dsimp only [position]
  by_cases hd : u/N=c
  · rw [hd,Nat.mul_comm N c] at hdivision
    right
    rw [hd]
    omega
  · have he : u/N=c-1 := by omega
    rw [he,Nat.mul_comm N (c-1)] at hdivision
    left
    rw [he]
    omega

include p₀ g₀ p q

lemma south_initial {c : ℕ} (hc : c<M) (l : Fin 2) :
    bdry hM hN p₀ g₀ p q (c*N)
      (southSlot hM hN hc (by omega : 0<N) l)=
      .inl (southSlot hM hN hc (by omega : 0<N) l) := by
  have hh:=boundary_untouched p₀ g₀ p q (position M N) (position_bound hM hN)
    (Nat.zero_le (c*N)) (southSlot hM hN hc (by omega : 0<N) l)
    (fun u _ hu=>Or.inl (south_initial_untouched hM hN hc hu l))
  exact hh

lemma west_initial {r : ℕ} (hr : r<N) (l : Fin 2) :
    bdry hM hN p₀ g₀ p q r
      (westSlot hM hN (by omega : 0<M) hr l)=
      .inl (westSlot hM hN (by omega : 0<M) hr l) := by
  exact boundary_untouched p₀ g₀ p q (position M N) (position_bound hM hN)
    (Nat.zero_le r) (westSlot hM hN (by omega : 0<M) hr l)
    (fun u _ hu=>Or.inr (west_initial_untouched hM hN hr hu l))

lemma south_previous {c r : ℕ} (hc : c<M) (hr : r<N) (hr0 : 0<r) (l : Fin 2) :
    bdry hM hN p₀ g₀ p q (c*N+r) (southSlot hM hN hc hr l)=
      .inr (⟨c*N+(r-1),by omega⟩,.inr ⟨4+l.val,by omega⟩) := by
  have he : southSlot hM hN hc hr l=Gate4.slot (position M N (c*N+(r-1)))
      (position_bound hM hN _) ⟨2+l.val,by omega⟩ := by
    apply Fin.ext
    rw [southSlot_val]
    change _ = position M N (c*N+(r-1))+(2+l.val)
    rw [position_time hN (by omega : r-1<N)]
    omega
  rw [he]
  simpa only [←Nat.add_assoc] using boundary_last p₀ g₀ p q (position M N) (position_bound hM hN)
    (by omega : c*N+(r-1)<c*N+r) ⟨2+l.val,by omega⟩ (by intro u hu₁ hu₂; omega)

lemma west_previous {c r : ℕ} (hc : c<M) (hc0 : 0<c) (hr : r<N) (l : Fin 2) :
    bdry hM hN p₀ g₀ p q (c*N+r) (westSlot hM hN hc hr l)=
      .inr (⟨(c-1)*N+r,by
        calc
          (c-1)*N+r < ((c-1)+1)*N+r := Nat.add_lt_add_right
            (Nat.mul_lt_mul_of_pos_right (by omega) (by omega)) _
          _ = c*N+r := by congr 2; omega⟩,.inr ⟨2+l.val,by omega⟩) := by
  have htime : (c-1)*N+r+1 ≤ c*N+r := by
    have hh : (c-1)*N+N=c*N := by
      calc
        (c-1)*N+N=(c-1+1)*N := by ring
        _ = c*N := by congr 1; omega
    omega
  have he : westSlot hM hN hc hr l=Gate4.slot (position M N ((c-1)*N+r))
      (position_bound hM hN _) ⟨l.val,by omega⟩ := by
    apply Fin.ext
    rw [westSlot_val]
    change _=position M N ((c-1)*N+r)+l.val
    rw [position_time hN hr]
    omega
  rw [bdry,boundary_untouched p₀ g₀ p q (position M N) (position_bound hM hN) htime _
    (fun u hu₁ hu₂=>west_previous_untouched hM hN hc hc0 hr hu₁ hu₂ l),he,boundary_slot]
  rfl

end BoundaryEvolution

 

 


variable {M N : ℕ} (hM : 1 ≤ M) (hN : 1 ≤ N)
  (p₀ : Pairing (ports M N)) (g₀ : Fin (ports M N) → ℤ) (p q : ℕ → Pairing 6)

lemma retained_boundary (t : ℕ) (i : Fin (ports M N)) (hi : i.val<width M N) :
    bdry hM hN p₀ g₀ p q t i=.inl i := by
  apply boundary_untouched p₀ g₀ p q (position M N) (position_bound hM hN) (Nat.zero_le t) i
  intro u _ _
  left
  dsimp only [position]
  omega

def eastSlot {r : ℕ} (_hr : r<N) (l : Fin 2) : Fin (ports M N) :=
  Gate4.slot (position M N ((M-1)*N+r)) (position_bound hM hN _) ⟨l.val,by omega⟩
def northSlot {c : ℕ} (_hc : c<M) (l : Fin 2) : Fin (ports M N) :=
  Gate4.slot (position M N (c*N+(N-1))) (position_bound hM hN _) ⟨2+l.val,by omega⟩

lemma eastSlot_val {r : ℕ} (hr : r<N) (l : Fin 2) :
    (eastSlot hM hN hr l).val=width M N+2*r+l.val := by
  change position M N ((M-1)*N+r)+l.val=_
  rw [position_time hN hr]
  omega
lemma northSlot_val {c : ℕ} (hc : c<M) (l : Fin 2) :
    (northSlot hM hN hc l).val=width M N+2*(M+N-1-c)+l.val := by
  change position M N (c*N+(N-1))+(2+l.val)=_
  rw [position_time hN (by omega : N-1<N)]
  omega

omit p₀ g₀ p q
lemma east_untouched {r u : ℕ} (hr : r<N) (hu₁ : (M-1)*N+r+1 ≤ u)
    (hu₂ : u<M*N) (l : Fin 2) : (eastSlot hM hN hr l).val<position M N u := by
  have hdlo : M-1 ≤ u/N := (Nat.le_div_iff_mul_le (by omega : 0<N)).mpr (by omega)
  have hdhi : u/N<M := (Nat.div_lt_iff_lt_mul (by omega : 0<N)).mpr
    (by simpa only [Nat.mul_comm] using hu₂)
  have hd : u/N=M-1 := by omega
  have hdivision:=Nat.mod_add_div u N
  rw [hd,Nat.mul_comm N (M-1)] at hdivision
  rw [eastSlot_val]
  dsimp only [position]
  rw [hd]
  omega
lemma north_untouched {c u : ℕ} (hc : c<M) (hu₁ : c*N+(N-1)+1 ≤ u)
    (hu₂ : u<M*N) (l : Fin 2) :
    position M N u+4 ≤ (northSlot hM hN hc l).val := by
  have hnext : (c+1)*N=c*N+(N-1)+1 := by rw [Nat.add_mul,Nat.one_mul]; omega
  have hdlo : c+1 ≤ u/N := (Nat.le_div_iff_mul_le (by omega : 0<N)).mpr (hnext ▸ hu₁)
  have hdhi : u/N<M := (Nat.div_lt_iff_lt_mul (by omega : 0<N)).mpr
    (by simpa only [Nat.mul_comm] using hu₂)
  have hr := Nat.mod_lt u (by omega : 0<N)
  rw [northSlot_val]
  dsimp only [position]
  omega

include p₀ g₀ p q
lemma east_boundary {r : ℕ} (hr : r<N) (l : Fin 2) :
    bdry hM hN p₀ g₀ p q (M*N) (eastSlot hM hN hr l)=
      .inr (⟨(M-1)*N+r,time_lt hr (by omega)⟩,.inr ⟨2+l.val,by omega⟩) :=
  boundary_last p₀ g₀ p q (position M N) (position_bound hM hN)
    (time_lt hr (by omega)) ⟨l.val,by omega⟩
    (fun u hu₁ hu₂=>Or.inl (east_untouched hM hN hr hu₁ hu₂ l))

lemma north_boundary {c : ℕ} (hc : c<M) (l : Fin 2) :
    bdry hM hN p₀ g₀ p q (M*N) (northSlot hM hN hc l)=
      .inr (⟨c*N+(N-1),time_lt (by omega) hc⟩,.inr ⟨4+l.val,by omega⟩) := by
  have hh := boundary_last p₀ g₀ p q (position M N) (position_bound hM hN)
    (s := c*N+(N-1)) (t := M*N)
    (time_lt (M:=M) (N:=N) (c:=c) (r:=N-1) (by omega) hc)
    (⟨2+l.val,by omega⟩ : Fin 4)
    (fun u hu₁ hu₂=>Or.inr (north_untouched hM hN hc hu₁ hu₂ l))
  refine hh.trans ?_
  apply congrArg Sum.inr
  apply congrArg (fun j : Fin 6 => ((⟨c*N+(N-1),time_lt (by omega) hc⟩:Fin (M*N)),Sum.inr j))
  apply Fin.ext
  change 2+(2+l.val)=4+l.val
  omega

 

def starterGauge (M N : ℕ) (i : Fin (ports M N)) : ℤ :=
  if i.val<2*N then -5 else if i.val<width M N then -3
    else if i.val<width M N+2*M then 0 else -2

omit g₀ p₀ p q
lemma starterGauge_south {c : ℕ} (hc : c<M) (l : Fin 2) :
    starterGauge M N (southSlot hM hN hc (by omega : 0<N) l)=0 := by
  unfold starterGauge
  rw [southSlot_val]
  unfold width
  split_ifs <;> omega
lemma starterGauge_west {r : ℕ} (hr : r<N) (l : Fin 2) :
    starterGauge M N (westSlot hM hN (by omega : 0<M) hr l)= -2 := by
  unfold starterGauge
  rw [westSlot_val]
  unfold width
  split_ifs <;> omega

include p₀ p q
lemma south_gauge {c r : ℕ} (hc : c<M) (hr : r<N) (l : Fin 2) :
    (box hM hN p₀ (starterGauge M N) p q (c*N+r)).gauge (southSlot hM hN hc hr l)=0 := by
  change (disk p₀ (starterGauge M N) p q (position M N) (position_bound hM hN) _).gauge _=_
  rw [← namedGauge_boundary]
  change namedGauge (starterGauge M N) _ (bdry hM hN p₀ (starterGauge M N) p q _ _)=_
  by_cases hr0 : r=0
  · subst r
    simpa only [Nat.add_zero, namedGauge] using
      (congrArg (namedGauge (starterGauge M N) (c*N))
        (south_initial hM hN p₀ (starterGauge M N) p q hc l)).trans
          (starterGauge_south hM hN hc l)
  · have hh := congrArg (namedGauge (starterGauge M N) (c*N+r))
        (south_previous hM hN p₀ (starterGauge M N) p q hc hr (by omega) l)
    refine hh.trans ?_
    change Rhombus.downGauge ⟨4+l.val,_⟩=0
    fin_cases l <;> norm_num [Rhombus.downGauge]
lemma west_gauge {c r : ℕ} (hc : c<M) (hr : r<N) (l : Fin 2) :
    (box hM hN p₀ (starterGauge M N) p q (c*N+r)).gauge (westSlot hM hN hc hr l)= -2 := by
  by_cases hc0 : c=0
  · subst c
    have hh := gauge_untouched p₀ (starterGauge M N) p q
      (position M N) (position_bound hM hN) (Nat.zero_le r)
      (westSlot hM hN (by omega : 0<M) hr l)
      (fun u _ hu=>Or.inr (west_initial_untouched hM hN hr hu l))
    simp only [box, Nat.zero_mul, Nat.zero_add]
    exact hh.trans (starterGauge_west hM hN hr l)
  · change (disk p₀ (starterGauge M N) p q (position M N) (position_bound hM hN) _).gauge _=_
    rw [← namedGauge_boundary]
    change namedGauge (starterGauge M N) _ (bdry hM hN p₀ (starterGauge M N) p q _ _)=_
    have hh := congrArg (namedGauge (starterGauge M N) (c*N+r))
        (west_previous hM hN p₀ (starterGauge M N) p q hc (by omega) hr l)
    refine hh.trans ?_
    change Rhombus.downGauge ⟨2+l.val,_⟩= -2
    fin_cases l <;> norm_num [Rhombus.downGauge]
lemma input_gauge {c r : ℕ} (hc : c<M) (hr : r<N) (i : Fin 4) :
    (box hM hN p₀ (starterGauge M N) p q (c*N+r)).gauge
      (Gate4.slot (position M N (c*N+r)) (position_bound hM hN _) i)=
        if i.val<2 then 0 else -2 := by
  by_cases hi : i.val<2
  · rw [ite_eq_left hi]
    exact south_gauge hM hN p₀ p q hc hr ⟨i.val,hi⟩
  · rw [ite_eq_right hi]
    have he : i=(⟨2+(i.val-2),by omega⟩:Fin 4) := Fin.ext (by change i.val=2+(i.val-2); omega)
    rw [he]
    exact west_gauge hM hN p₀ p q hc hr ⟨i.val-2,by omega⟩

lemma input_gauge_all (t : ℕ) (ht : t<M*N) (i : Fin 4) :
    (box hM hN p₀ (starterGauge M N) p q t).gauge
      (Gate4.slot (position M N t) (position_bound hM hN _) i)=
        if i.val<2 then 0 else -2 := by
  have hc : t/N<M := (Nat.div_lt_iff_lt_mul (by omega : 0<N)).mpr
    (by simpa only [Nat.mul_comm] using ht)
  have hr : t%N<N := Nat.mod_lt t (by omega)
  have hh:=input_gauge hM hN p₀ p q hc hr i
  have he : t/N*N+t%N=t := by simpa only [Nat.mul_comm] using Nat.div_add_mod t N
  simpa only [he] using hh

end TurnRectangle
end
end CriticalStrip.Diagram

end OAI
