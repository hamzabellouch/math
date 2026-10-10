import Mathlib
import OAI.Combinatorics.StripMass.TurnEvolution

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical
namespace TurnRectangle
open TurnDisk TurnNetwork

variable {M N : ℕ} (hM : 1 ≤ M) (hN : 1 ≤ N)
  (p₀ : Pairing (ports M N)) (p q : ℕ → Pairing 6)

 
def PhysicalMatches : Prop :=
  (∀ c r, c<M → r<N → ∀ l : Fin 2,
    (p (c*N+r)).Occupied ⟨4+l.val,by omega⟩ ↔ (q (c*N+r)).Occupied ⟨1-l.val,by omega⟩) ∧
  (∀ c, (hc : c<M) → ∀ l : Fin 2,
    p₀.Occupied (southSlot hM hN hc (by omega : 0<N) l) ↔
      (p (c*N)).Occupied ⟨3-l.val,by omega⟩) ∧
  (∀ r, (hr : r<N) → ∀ l : Fin 2,
    p₀.Occupied (westSlot hM hN (by omega : 0<M) hr l) ↔
      (p r).Occupied ⟨1-l.val,by omega⟩) ∧
  (∀ c r, c<M → r<N → 0<r → ∀ l : Fin 2,
    (q (c*N+(r-1))).Occupied ⟨4+l.val,by omega⟩ ↔
      (p (c*N+r)).Occupied ⟨3-l.val,by omega⟩) ∧
  (∀ c r, c<M → 0<c → r<N → ∀ l : Fin 2,
    (q ((c-1)*N+r)).Occupied ⟨2+l.val,by omega⟩ ↔
      (p (c*N+r)).Occupied ⟨1-l.val,by omega⟩)

lemma physical_matches (hm : PhysicalMatches hM hN p₀ p q) :
    Matches p₀ (starterGauge M N) p q (position M N) (position_bound hM hN) (M*N) := by
  constructor
  · intro t ht l
    have hc : t/N<M := (Nat.div_lt_iff_lt_mul (by omega : 0<N)).mpr
      (by simpa only [Nat.mul_comm] using ht)
    have hr : t%N<N := Nat.mod_lt t (by omega)
    have he : t/N*N+t%N=t := by simpa only [Nat.mul_comm] using Nat.div_add_mod t N
    simpa only [he] using hm.1 (t/N) (t%N) hc hr l
  · suffices hh : ∀ c r, (hc : c<M) → (hr : r<N) → ∀ i : Fin 4,
        Occupied p₀ p q (c*N+r) (bdry hM hN p₀ (starterGauge M N) p q (c*N+r)
          (Gate4.slot (position M N (c*N+r)) (position_bound hM hN _) i)) ↔
          (p (c*N+r)).Occupied ⟨3-i.val,by omega⟩ by
      intro t ht i
      have hc : t/N<M := (Nat.div_lt_iff_lt_mul (by omega : 0<N)).mpr
        (by simpa only [Nat.mul_comm] using ht)
      have hr : t%N<N := Nat.mod_lt t (by omega)
      have he : t/N*N+t%N=t := by simpa only [Nat.mul_comm] using Nat.div_add_mod t N
      obtain ⟨c,r,hc₁,hr₁,rfl⟩ : ∃ c r,c<M ∧ r<N ∧ t=c*N+r :=
        ⟨t/N,t%N,hc,hr,he.symm⟩
      exact hh c r hc₁ hr₁ i
    intro c r hc hr i
    by_cases hi : i.val<2
    · let l : Fin 2 := ⟨i.val,hi⟩
      change Occupied p₀ p q (c*N+r) (bdry hM hN p₀ (starterGauge M N) p q (c*N+r)
        (southSlot hM hN hc hr l)) ↔ _
      by_cases hr0 : r=0
      · subst r
        simp only [Nat.add_zero]
        rw [south_initial]
        exact hm.2.1 c hc l
      · rw [south_previous hM hN p₀ (starterGauge M N) p q hc hr (by omega) l]
        exact hm.2.2.2.1 c r hc hr (by omega) l
    · let l : Fin 2 := ⟨i.val-2,by omega⟩
      have he : i=(⟨2+l.val,by omega⟩:Fin 4) := by apply Fin.ext; change i.val=2+(i.val-2); omega
      rw [he]
      have he' : (⟨3-(2+l.val),by omega⟩:Fin 6)=(⟨1-l.val,by omega⟩:Fin 6) := by
        apply Fin.ext; dsimp; omega
      rw [he']
      change Occupied p₀ p q (c*N+r) (bdry hM hN p₀ (starterGauge M N) p q (c*N+r)
        (westSlot hM hN hc hr l)) ↔ _
      by_cases hc0 : c=0
      · subst c
        have hh:=congrArg (Occupied p₀ p q r)
          (west_initial hM hN p₀ (starterGauge M N) p q hr l)
        have hh' := (Iff.of_eq hh).trans (hm.2.2.1 r hr l)
        have hcng {t u : ℕ} (he : t=u) (j : Fin (ports M N)) :
            Occupied p₀ p q t (bdry hM hN p₀ (starterGauge M N) p q t j) ↔
              Occupied p₀ p q u (bdry hM hN p₀ (starterGauge M N) p q u j) := by
          subst u
          rfl
        exact (hcng (by omega : 0*N+r=r) _).trans (by simpa only [Nat.zero_mul,Nat.zero_add] using hh')
      · rw [west_previous hM hN p₀ (starterGauge M N) p q hc (by omega) hr l]
        exact hm.2.2.2.2 c r hc (by omega) hr l

lemma compatible (hm : PhysicalMatches hM hN p₀ p q) :
    (box hM hN p₀ (starterGauge M N) p q (M*N)).Compatible :=
  TurnNetwork.compatible _ _ _ _ _ _ _ (physical_matches hM hN p₀ p q hm)
    (input_gauge_all hM hN p₀ p q)

end TurnRectangle

 

 

namespace TurnStarter

variable (w : ℕ)
def left (i : Fin w) : Fin (2*w) := ⟨w-1-i.val,by omega⟩
def right (i : Fin w) : Fin (2*w) := ⟨w+i.val,by omega⟩

lemma left_injective : Function.Injective (left w) := by
  intro i j h
  apply Fin.ext
  have hh:=congrArg Fin.val h
  dsimp [left] at hh
  omega
lemma right_injective : Function.Injective (right w) := by
  intro i j h
  apply Fin.ext
  have hh:=congrArg Fin.val h
  dsimp [right] at hh
  omega
lemma left_lt_right (i j : Fin w) : left w i<right w j := by
  change w-1-i.val<w+j.val
  omega
lemma cover (i : Fin (2*w)) : (∃ j,i=left w j) ∨ (∃ j,i=right w j) := by
  by_cases hi : i.val<w
  · left
    refine ⟨⟨w-1-i.val,by omega⟩,?_⟩
    apply Fin.ext
    change i.val=w-1-(w-1-i.val)
    omega
  · right
    refine ⟨⟨i.val-w,by omega⟩,?_⟩
    apply Fin.ext
    change i.val=w+(i.val-w)
    omega

def pairing (active : Fin w → Prop) : Pairing (2*w) :=
  ⟨((Finset.univ.filter active).image (fun i=>(left w i,right w i))),by
    constructor
    · intro e he
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp he
      exact left_lt_right w i i
    constructor
    · intro e he f hf
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp he
      obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hf
      by_cases hij : i=j
      · subst j
        exact Or.inl rfl
      · right
        exact ⟨fun h=>hij (left_injective w h),(left_lt_right w i j).ne,
          (left_lt_right w j i).ne.symm,fun h=>hij (right_injective w h)⟩
    · intro e he f hf
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp he
      obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hf
      change ¬(left w i<left w j ∧ left w j<right w i ∧ right w i<right w j)
      simp only [Fin.lt_def,left,right]
      omega⟩

lemma adj_iff (active : Fin w → Prop) (a b : Fin (2*w)) :
    (pairing w active).Adj a b ↔ ∃ j,active j ∧
      ((a=left w j ∧ b=right w j) ∨ (a=right w j ∧ b=left w j)) := by
  simp only [Pairing.Adj,pairing,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,
    true_and,Prod.mk.injEq]
  constructor
  · rintro (⟨j,hj,ha,hb⟩|⟨j,hj,hb,ha⟩)
    · exact ⟨j,hj,Or.inl ⟨ha.symm,hb.symm⟩⟩
    · exact ⟨j,hj,Or.inr ⟨ha.symm,hb.symm⟩⟩
  · rintro ⟨j,hj,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
    · exact Or.inl ⟨j,hj,rfl,rfl⟩
    · exact Or.inr ⟨j,hj,rfl,rfl⟩

lemma across (active : Fin w → Prop) {j : Fin w} (hj : active j) :
    (pairing w active).Adj (left w j) (right w j) :=
  (adj_iff w active _ _).mpr ⟨j,hj,Or.inl ⟨rfl,rfl⟩⟩

lemma occupied_left (active : Fin w → Prop) (i : Fin w) :
    (pairing w active).Occupied (left w i) ↔ active i := by
  constructor
  · rintro ⟨v,hv⟩
    obtain ⟨j,hj,h⟩:=(adj_iff w active _ _).mp hv
    rcases h with ⟨h,_⟩|⟨h,_⟩
    · exact left_injective w h ▸ hj
    · exact ((left_lt_right w i j).ne h).elim
  · intro hi
    exact ⟨right w i,across w active hi⟩
lemma occupied_right (active : Fin w → Prop) (i : Fin w) :
    (pairing w active).Occupied (right w i) ↔ active i := by
  constructor
  · rintro ⟨v,hv⟩
    obtain ⟨j,hj,h⟩:=(adj_iff w active _ _).mp hv
    rcases h with ⟨h,_⟩|⟨h,_⟩
    · exact ((left_lt_right w j i).ne.symm h).elim
    · exact right_injective w h ▸ hj
  · intro hi
    exact ⟨left w i,(across w active hi).symm⟩

end TurnStarter

 

 

namespace TurnRectangle
open TurnDisk TurnNetwork
section PhysicalMatching

variable {M N : ℕ} (hM : 1 ≤ M) (hN : 1 ≤ N)
  (p₀ : Pairing (ports M N)) (p q : ℕ → Pairing 6)

abbrev edges := graph p₀ (starterGauge M N) p q (position M N) (position_bound hM hN) (M*N)
abbrev turns := edgeTurn p₀ (starterGauge M N) p q (position M N) (position_bound hM hN) (M*N)

def cellNode (c : Fin M) (r : Fin N) (v : Local) : Node (ports M N) (M*N) :=
  .inr (⟨c.val*N+r.val,time_lt r.isLt c.isLt⟩,v)

lemma local_edge {c : Fin M} {r : Fin N} {v w : Local}
    (h : (Rhombus.disk (p (c.val*N+r.val)) (q (c.val*N+r.val))).wiring v w) :
    edges hM hN p₀ p q (cellNode c r v) (cellNode c r w) :=
  lift_edge _ _ _ _ _ _ (by have :=time_lt r.isLt c.isLt; omega : c.val*N+r.val+1 ≤ M*N)
    (fresh_edge _ _ _ _ _ _ _ h)

lemma local_turn {c : Fin M} {r : Fin N} {v w : Local}
    (h : (Rhombus.disk (p (c.val*N+r.val)) (q (c.val*N+r.val))).wiring v w) :
    turns hM hN p₀ p q (cellNode c r v) (cellNode c r w)=
      (Rhombus.disk (p (c.val*N+r.val)) (q (c.val*N+r.val))).edgeTurn v w :=
  (lift_turn _ _ _ _ _ _ (by have :=time_lt r.isLt c.isLt; omega : c.val*N+r.val+1 ≤ M*N)
    (fresh_edge _ _ _ _ _ _ _ h)).trans (fresh_turn _ _ _ _ _ _ _ h)

lemma up_edge {c : Fin M} {r : Fin N} {v w : Fin 6}
    (h : (p (c.val*N+r.val)).Adj v w) :
    edges hM hN p₀ p q (cellNode c r (.inl v)) (cellNode c r (.inl w)) :=
  local_edge hM hN p₀ p q (Rhombus.up_edge _ _ h)
lemma up_turn {c : Fin M} {r : Fin N} {v w : Fin 6}
    (h : (p (c.val*N+r.val)).Adj v w) :
    turns hM hN p₀ p q (cellNode c r (.inl v)) (cellNode c r (.inl w))=
      Pairing.arcTurn Rhombus.upGauge v w :=
  (local_turn hM hN p₀ p q (Rhombus.up_edge _ _ h)).trans (Rhombus.up_turn _ _ h)
lemma down_edge {c : Fin M} {r : Fin N} {v w : Fin 6}
    (h : (q (c.val*N+r.val)).Adj v w) :
    edges hM hN p₀ p q (cellNode c r (.inr v)) (cellNode c r (.inr w)) :=
  local_edge hM hN p₀ p q (Rhombus.down_edge _ _ h)
lemma down_turn {c : Fin M} {r : Fin N} {v w : Fin 6}
    (h : (q (c.val*N+r.val)).Adj v w) :
    turns hM hN p₀ p q (cellNode c r (.inr v)) (cellNode c r (.inr w))=
      Pairing.arcTurn Rhombus.downGauge v w :=
  (local_turn hM hN p₀ p q (Rhombus.down_edge _ _ h)).trans (Rhombus.down_turn _ _ h)

variable (hm : PhysicalMatches hM hN p₀ p q)
include hm
lemma diagonal_edge {c : Fin M} {r : Fin N} (l : Fin 2)
    (h : (p (c.val*N+r.val)).Occupied ⟨4+l.val,by omega⟩) :
    edges hM hN p₀ p q (cellNode c r (.inl ⟨4+l.val,by omega⟩))
      (cellNode c r (.inr ⟨1-l.val,by omega⟩)) :=
  local_edge hM hN p₀ p q ((Rhombus.wiring _ _ (hm.1 _ _ c.isLt r.isLt) _ _).mpr
    (Or.inr ⟨l,h,Or.inl ⟨rfl,rfl⟩⟩))
lemma diagonal_turn {c : Fin M} {r : Fin N} (l : Fin 2)
    (h : (p (c.val*N+r.val)).Occupied ⟨4+l.val,by omega⟩) :
    turns hM hN p₀ p q (cellNode c r (.inl ⟨4+l.val,by omega⟩))
      (cellNode c r (.inr ⟨1-l.val,by omega⟩))=0 :=
  (local_turn hM hN p₀ p q ((Rhombus.wiring _ _ (hm.1 _ _ c.isLt r.isLt) _ _).mpr
    (Or.inr ⟨l,h,Or.inl ⟨rfl,rfl⟩⟩))).trans (Rhombus.cross_turn _ _ _ _)

lemma enter_edge {t : ℕ} (ht : t<M*N) (i : Fin 4)
    (hi : (p t).Occupied ⟨3-i.val,by omega⟩) :
    edges hM hN p₀ p q
      (lift (Nat.le_of_lt ht) (bdry hM hN p₀ (starterGauge M N) p q t
        (Gate4.slot (position M N t) (position_bound hM hN _) i)))
      (.inr (⟨t,ht⟩,.inl ⟨3-i.val,by omega⟩)) := by
  have hh := lift_edge _ _ _ _ _ _ (by omega : t+1 ≤ M*N)
    (wire_edge _ _ _ _ _ _ t ((physical_matches hM hN p₀ p q hm).mono _ _ _ _ _ _ (by omega)) i hi)
  rw [old_eq_lift,lift_trans] at hh
  exact hh
lemma enter_turn {t : ℕ} (ht : t<M*N) (i : Fin 4)
    (hi : (p t).Occupied ⟨3-i.val,by omega⟩) :
    turns hM hN p₀ p q
      (lift (Nat.le_of_lt ht) (bdry hM hN p₀ (starterGauge M N) p q t
        (Gate4.slot (position M N t) (position_bound hM hN _) i)))
      (.inr (⟨t,ht⟩,.inl ⟨3-i.val,by omega⟩))=0 := by
  have hh := (lift_turn _ _ _ _ _ _ (by omega : t+1 ≤ M*N)
    (wire_edge _ _ _ _ _ _ t ((physical_matches hM hN p₀ p q hm).mono _ _ _ _ _ _ (by omega)) i hi)).trans
      (wire_turn _ _ _ _ _ _ t _ _)
  rw [old_eq_lift,lift_trans] at hh
  exact hh

lemma vertical_edge {c : Fin M} {r : Fin N} (hr : 0<r.val) (l : Fin 2)
    (h : (p (c.val*N+r.val)).Occupied ⟨3-l.val,by omega⟩) :
    edges hM hN p₀ p q (cellNode c ⟨r.val-1,by omega⟩ (.inr ⟨4+l.val,by omega⟩))
      (cellNode c r (.inl ⟨3-l.val,by omega⟩)) := by
  have hh:=enter_edge hM hN p₀ p q hm (time_lt r.isLt c.isLt) ⟨l.val,by omega⟩ h
  change edges hM hN p₀ p q
    (lift _ (bdry hM hN p₀ (starterGauge M N) p q _ (southSlot hM hN c.isLt r.isLt l))) _ at hh
  rw [south_previous hM hN p₀ (starterGauge M N) p q c.isLt r.isLt hr l] at hh
  exact hh
lemma vertical_turn {c : Fin M} {r : Fin N} (hr : 0<r.val) (l : Fin 2)
    (h : (p (c.val*N+r.val)).Occupied ⟨3-l.val,by omega⟩) :
    turns hM hN p₀ p q (cellNode c ⟨r.val-1,by omega⟩ (.inr ⟨4+l.val,by omega⟩))
      (cellNode c r (.inl ⟨3-l.val,by omega⟩))=0 := by
  have hh:=enter_turn hM hN p₀ p q hm (time_lt r.isLt c.isLt) ⟨l.val,by omega⟩ h
  change turns hM hN p₀ p q
    (lift _ (bdry hM hN p₀ (starterGauge M N) p q _ (southSlot hM hN c.isLt r.isLt l))) _=0 at hh
  rw [south_previous hM hN p₀ (starterGauge M N) p q c.isLt r.isLt hr l] at hh
  exact hh

lemma horizontal_edge {c : Fin M} {r : Fin N} (hc : 0<c.val) (l : Fin 2)
    (h : (p (c.val*N+r.val)).Occupied ⟨1-l.val,by omega⟩) :
    edges hM hN p₀ p q (cellNode ⟨c.val-1,by omega⟩ r (.inr ⟨2+l.val,by omega⟩))
      (cellNode c r (.inl ⟨1-l.val,by omega⟩)) := by
  have hi : (p (c.val*N+r.val)).Occupied ⟨3-(2+l.val),by omega⟩ := by
    convert h using 1; congr 1; omega
  have hh:=enter_edge hM hN p₀ p q hm (time_lt r.isLt c.isLt) ⟨2+l.val,by omega⟩ hi
  change edges hM hN p₀ p q
    (lift _ (bdry hM hN p₀ (starterGauge M N) p q _ (westSlot hM hN c.isLt r.isLt l))) _ at hh
  rw [west_previous hM hN p₀ (starterGauge M N) p q c.isLt hc r.isLt l] at hh
  convert hh using 1 <;> congr 3
  dsimp only
  omega
lemma horizontal_turn {c : Fin M} {r : Fin N} (hc : 0<c.val) (l : Fin 2)
    (h : (p (c.val*N+r.val)).Occupied ⟨1-l.val,by omega⟩) :
    turns hM hN p₀ p q (cellNode ⟨c.val-1,by omega⟩ r (.inr ⟨2+l.val,by omega⟩))
      (cellNode c r (.inl ⟨1-l.val,by omega⟩))=0 := by
  have hi : (p (c.val*N+r.val)).Occupied ⟨3-(2+l.val),by omega⟩ := by
    convert h using 1; congr 1; omega
  have hh:=enter_turn hM hN p₀ p q hm (time_lt r.isLt c.isLt) ⟨2+l.val,by omega⟩ hi
  change turns hM hN p₀ p q
    (lift _ (bdry hM hN p₀ (starterGauge M N) p q _ (westSlot hM hN c.isLt r.isLt l))) _=0 at hh
  rw [west_previous hM hN p₀ (starterGauge M N) p q c.isLt hc r.isLt l] at hh
  convert hh using 1; congr 4; dsimp only; omega

end PhysicalMatching

 

 


variable {M N : ℕ}

def southRay (c : Fin M) (l : Fin 2) : Fin (width M N) :=
  ⟨2*(M-1-c.val)+l.val,by dsimp [width]; omega⟩
def westRay (r : Fin N) (l : Fin 2) : Fin (width M N) :=
  ⟨2*(M+r.val)+l.val,by dsimp [width]; omega⟩

lemma southRay_div (c : Fin M) (l : Fin 2) : (southRay (N:=N) c l).val/2=M-1-c.val := by
  rw [southRay,Nat.mul_add_div (by omega : 0<2),Nat.div_eq_of_lt l.isLt,Nat.add_zero]
lemma southRay_mod (c : Fin M) (l : Fin 2) : (southRay (N:=N) c l).val%2=l.val := by
  rw [southRay,Nat.mul_add_mod,Nat.mod_eq_of_lt l.isLt]
lemma westRay_div (r : Fin N) (l : Fin 2) : (westRay (M:=M) r l).val/2=M+r.val := by
  rw [westRay,Nat.mul_add_div (by omega : 0<2),Nat.div_eq_of_lt l.isLt,Nat.add_zero]
lemma westRay_mod (r : Fin N) (l : Fin 2) : (westRay (M:=M) r l).val%2=l.val := by
  rw [westRay,Nat.mul_add_mod,Nat.mod_eq_of_lt l.isLt]

lemma ray_cover (i : Fin (width M N)) :
    (∃c : Fin M,∃l : Fin 2,i=southRay c l) ∨ (∃r : Fin N,∃l : Fin 2,i=westRay r l) := by
  have hd:=Nat.mod_add_div i.val 2
  have hr:=Nat.mod_lt i.val (by omega : 0<2)
  have hi : i.val<2*(M+N) := i.isLt
  by_cases h : i.val<2*M
  · left
    refine ⟨⟨M-1-i.val/2,by omega⟩,⟨i.val%2,hr⟩,?_⟩
    apply Fin.ext
    change i.val=2*(M-1-(M-1-i.val/2))+i.val%2
    omega
  · right
    refine ⟨⟨i.val/2-M,by omega⟩,⟨i.val%2,hr⟩,?_⟩
    apply Fin.ext
    change i.val=2*(M+(i.val/2-M))+i.val%2
    omega

variable (hM : 1 ≤ M) (hN : 1 ≤ N) (p q : ℕ → Pairing 6)

def starterActive (i : Fin (width M N)) : Prop :=
  if i.val<2*M then (p ((M-1-i.val/2)*N)).Occupied ⟨3-i.val%2,by omega⟩
  else (p (i.val/2-M)).Occupied ⟨1-i.val%2,by omega⟩

def startPairing : Pairing (ports M N) := TurnStarter.pairing (width M N) (starterActive (M:=M) (N:=N) p)

lemma active_south (c : Fin M) (l : Fin 2) : starterActive p (southRay (N:=N) c l) ↔
    (p (c.val*N)).Occupied ⟨3-l.val,by omega⟩ := by
  have hi : (southRay (N:=N) c l).val<2*M := by dsimp [southRay]; omega
  simp only [starterActive,ite_eq_left hi,southRay_mod,southRay_div]
  have he : M-1-(M-1-c.val)=c.val := by omega
  rw [he]
lemma active_west (r : Fin N) (l : Fin 2) : starterActive p (westRay (M:=M) r l) ↔
    (p r.val).Occupied ⟨1-l.val,by omega⟩ := by
  have hi : ¬(westRay (M:=M) r l).val<2*M := by dsimp [westRay]; omega
  simp only [starterActive,ite_eq_right hi,westRay_mod,westRay_div,Nat.add_sub_cancel_left]

lemma southSlot_right (c : Fin M) (l : Fin 2) :
    southSlot hM hN c.isLt (by omega : 0<N) l=
      TurnStarter.right (width M N) (southRay c l) := by
  apply Fin.ext
  rw [southSlot_val]
  dsimp only [TurnStarter.right,southRay]
  omega
lemma westSlot_right (r : Fin N) (l : Fin 2) :
    westSlot hM hN (by omega : 0<M) r.isLt l=
      TurnStarter.right (width M N) (westRay r l) := by
  apply Fin.ext
  rw [westSlot_val]
  change width M N+2*(M-1-0+r.val)+2+l.val=width M N+(2*(M+r.val)+l.val)
  omega

lemma start_matches_south (c : Fin M) (l : Fin 2) :
    (startPairing (M:=M) (N:=N) p).Occupied (southSlot hM hN c.isLt (by omega : 0<N) l) ↔
      (p (c.val*N)).Occupied ⟨3-l.val,by omega⟩ := by
  rw [southSlot_right]
  exact (TurnStarter.occupied_right _ _ _).trans (active_south p c l)
lemma start_matches_west (r : Fin N) (l : Fin 2) :
    (startPairing (M:=M) (N:=N) p).Occupied (westSlot hM hN (by omega : 0<M) r.isLt l) ↔
      (p r.val).Occupied ⟨1-l.val,by omega⟩ := by
  rw [westSlot_right]
  exact (TurnStarter.occupied_right _ _ _).trans (active_west p r l)

 

def InteriorMatches : Prop :=
  (∀ c r, c<M → r<N → ∀ l : Fin 2,
    (p (c*N+r)).Occupied ⟨4+l.val,by omega⟩ ↔ (q (c*N+r)).Occupied ⟨1-l.val,by omega⟩) ∧
  (∀ c r, c<M → r<N → 0<r → ∀ l : Fin 2,
    (q (c*N+(r-1))).Occupied ⟨4+l.val,by omega⟩ ↔ (p (c*N+r)).Occupied ⟨3-l.val,by omega⟩) ∧
  (∀ c r, c<M → 0<c → r<N → ∀ l : Fin 2,
    (q ((c-1)*N+r)).Occupied ⟨2+l.val,by omega⟩ ↔ (p (c*N+r)).Occupied ⟨1-l.val,by omega⟩)

lemma starter_physical (hm : InteriorMatches (M:=M) (N:=N) p q) :
    PhysicalMatches hM hN (startPairing p) p q :=
  ⟨hm.1,fun c hc=>start_matches_south hM hN p ⟨c,hc⟩,
    fun r hr=>start_matches_west hM hN p ⟨r,hr⟩,hm.2⟩

omit p q
lemma starter_arc_turn (i : Fin (width M N)) :
    Pairing.arcTurn (starterGauge M N) (TurnStarter.left (width M N) i)
      (TurnStarter.right (width M N) i)=0 := by
  have ho:=TurnStarter.left_lt_right (width M N) i i
  dsimp only [Pairing.arcTurn,Pairing.turnOrder]
  erw [ite_eq_left ho]
  unfold starterGauge TurnStarter.left TurnStarter.right width
  dsimp only
  have hi : i.val<2*(M+N) := i.isLt
  split_ifs <;> omega

include p q
lemma starter_edge {i : Fin (width M N)} (hi : starterActive p i) :
    edges hM hN (startPairing p) p q (.inl (TurnStarter.left (width M N) i))
      (.inl (TurnStarter.right (width M N) i)) :=
  lift_edge _ _ _ _ _ _ (Nat.zero_le (M*N))
    (show graph (startPairing p) (starterGauge M N) p q (position M N) (position_bound hM hN) 0
      (.inl (TurnStarter.left _ i)) (.inl (TurnStarter.right _ i)) from
        TurnStarter.across (width M N) (starterActive p) hi)
lemma starter_turn {i : Fin (width M N)} (hi : starterActive p i) :
    turns hM hN (startPairing p) p q (.inl (TurnStarter.left (width M N) i))
      (.inl (TurnStarter.right (width M N) i))=0 :=
  (lift_turn _ _ _ _ _ _ (Nat.zero_le (M*N))
    (show graph (startPairing p) (starterGauge M N) p q (position M N) (position_bound hM hN) 0
      (.inl (TurnStarter.left _ i)) (.inl (TurnStarter.right _ i)) from
        TurnStarter.across (width M N) (starterActive p) hi)).trans (starter_arc_turn i)

variable (hm : InteriorMatches (M:=M) (N:=N) p q)
include hm
lemma south_edge {c : Fin M} (l : Fin 2)
    (hi : (p (c.val*N)).Occupied ⟨3-l.val,by omega⟩) :
    edges hM hN (startPairing p) p q
      (.inl (southSlot hM hN c.isLt (by omega : 0<N) l))
      (cellNode c ⟨0,by omega⟩ (.inl ⟨3-l.val,by omega⟩)) := by
  have hh:=enter_edge hM hN (startPairing p) p q (starter_physical hM hN p q hm)
    (by simpa only [Nat.add_zero] using time_lt (M:=M) (N:=N) (c:=c.val) (r:=0) (by omega) c.isLt)
    ⟨l.val,by omega⟩ hi
  have he : Gate4.slot (position M N (c.val*N)) (position_bound hM hN _) ⟨l.val,by omega⟩=
      southSlot hM hN c.isLt (by omega : 0<N) l := rfl
  rw [he,south_initial] at hh
  exact hh
lemma south_turn {c : Fin M} (l : Fin 2)
    (hi : (p (c.val*N)).Occupied ⟨3-l.val,by omega⟩) :
    turns hM hN (startPairing p) p q
      (.inl (southSlot hM hN c.isLt (by omega : 0<N) l))
      (cellNode c ⟨0,by omega⟩ (.inl ⟨3-l.val,by omega⟩))=0 := by
  have hh:=enter_turn hM hN (startPairing p) p q (starter_physical hM hN p q hm)
    (by simpa only [Nat.add_zero] using time_lt (M:=M) (N:=N) (c:=c.val) (r:=0) (by omega) c.isLt)
    ⟨l.val,by omega⟩ hi
  have he : Gate4.slot (position M N (c.val*N)) (position_bound hM hN _) ⟨l.val,by omega⟩=
      southSlot hM hN c.isLt (by omega : 0<N) l := rfl
  rw [he,south_initial] at hh
  exact hh
lemma west_edge {r : Fin N} (l : Fin 2)
    (hi : (p r.val).Occupied ⟨1-l.val,by omega⟩) :
    edges hM hN (startPairing p) p q
      (.inl (westSlot hM hN (by omega : 0<M) r.isLt l))
      (cellNode ⟨0,by omega⟩ r (.inl ⟨1-l.val,by omega⟩)) := by
  have ht : r.val<M*N := by
    simpa only [Nat.zero_mul,Nat.zero_add] using time_lt r.isLt (by omega : 0<M)
  have hi' : (p r.val).Occupied ⟨3-(2+l.val),by omega⟩ := by convert hi using 1; congr 1; omega
  have hh:=enter_edge hM hN (startPairing p) p q (starter_physical hM hN p q hm)
    ht ⟨2+l.val,by omega⟩ hi'
  have he : Gate4.slot (position M N r.val) (position_bound hM hN _) ⟨2+l.val,by omega⟩=
      westSlot hM hN (by omega : 0<M) r.isLt l := by
        apply Fin.ext
        simp only [westSlot,Gate4.slot,Nat.zero_mul,Nat.zero_add]
  rw [he,west_initial] at hh
  have hj : (⟨3-(2+l.val),by omega⟩:Fin 6)=⟨1-l.val,by omega⟩ := Fin.ext (by dsimp; omega)
  simpa only [Fin.val_mk,hj,cellNode,westSlot,Gate4.slot,lift,Nat.zero_mul,Nat.zero_add] using hh
lemma west_turn {r : Fin N} (l : Fin 2)
    (hi : (p r.val).Occupied ⟨1-l.val,by omega⟩) :
    turns hM hN (startPairing p) p q
      (.inl (westSlot hM hN (by omega : 0<M) r.isLt l))
      (cellNode ⟨0,by omega⟩ r (.inl ⟨1-l.val,by omega⟩))=0 := by
  have ht : r.val<M*N := by
    simpa only [Nat.zero_mul,Nat.zero_add] using time_lt r.isLt (by omega : 0<M)
  have hi' : (p r.val).Occupied ⟨3-(2+l.val),by omega⟩ := by convert hi using 1; congr 1; omega
  have hh:=enter_turn hM hN (startPairing p) p q (starter_physical hM hN p q hm)
    ht ⟨2+l.val,by omega⟩ hi'
  have he : Gate4.slot (position M N r.val) (position_bound hM hN _) ⟨2+l.val,by omega⟩=
      westSlot hM hN (by omega : 0<M) r.isLt l := by
        apply Fin.ext
        simp only [westSlot,Gate4.slot,Nat.zero_mul,Nat.zero_add]
  rw [he,west_initial] at hh
  have hj : (⟨3-(2+l.val),by omega⟩:Fin 6)=⟨1-l.val,by omega⟩ := Fin.ext (by dsimp; omega)
  simpa only [Fin.val_mk,hj,cellNode,westSlot,Gate4.slot,lift,Nat.zero_mul,Nat.zero_add] using hh

end TurnRectangle

 

 


lemma TurnDisk.edgeTurn_reverse {n : ℕ} (D : TurnDisk n) (v w : D.Vertex) :
    D.edgeTurn w v = -D.edgeTurn v w := by
  induction D with
  | atom p g => exact Pairing.arcTurn_reverse g v w
  | insert D k hk p g ih =>
    rcases v with v|v <;> rcases w with w|w
    · exact ih v w
    · rfl
    · rfl
    · exact Pairing.arcTurn_reverse g v w
  | attach D E k hk ih ihE =>
    rcases v with v|v <;> rcases w with w|w
    · exact ih v w
    · rfl
    · rfl
    · exact ihE v w
  | sew D k hk ih =>
    change (if D.wiring w v then D.edgeTurn w v else 0)= -(if D.wiring v w then D.edgeTurn v w else 0)
    have hs : D.wiring w v ↔ D.wiring v w := ⟨fun h=>(TurnDisk.instSymmVertexWiring D).symm _ _ h,
      fun h=>(TurnDisk.instSymmVertexWiring D).symm _ _ h⟩
    simp only [hs]
    split_ifs
    · exact ih v w
    · rfl

lemma TurnNetwork.edgeTurn_reverse {n : ℕ} (p₀ : Pairing n) (g₀ : Fin n → ℤ)
    (p q : ℕ → Pairing 6) (k : ℕ → ℕ) (hk : ∀ t,k t+4≤n) (t : ℕ)
    (v w : TurnNetwork.Node n t) :
    TurnNetwork.edgeTurn p₀ g₀ p q k hk t w v= -TurnNetwork.edgeTurn p₀ g₀ p q k hk t v w :=
  TurnDisk.edgeTurn_reverse _ _ _

end
end CriticalStrip.Diagram

end OAI
