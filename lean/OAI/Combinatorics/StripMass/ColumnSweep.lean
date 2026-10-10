import Mathlib
import OAI.Combinatorics.StripMass.FreshGate

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
namespace PartialColumn
section ColumnGeometry
open scoped Classical
section BoundaryTracking
variable {n : ℕ}

 def baseProject : V n → Fin (n+1)
  | .inl i => i
  | .inr _ => 0

lemma base_edge {p : Pairing n} {t : Configuration n} {v w : V n} (h : wiring p t 0 v w) :
    p.padBottom.Adj (baseProject v) (baseProject w) := by
  rcases v with i | ⟨i,a⟩ <;> rcases w with j | ⟨j,b⟩
  · exact h
  all_goals simp [wiring] at h

lemma base_used {p : Pairing n} {t : Configuration n} {v : V n}
    (h : Graph.Used (wiring p t 0) v) : v=.inl (baseProject v) := by
  obtain ⟨w,hw⟩ := h
  cases v with
  | inl i => rfl
  | inr v => cases w <;> simp [wiring] at hw

 def baseEquiv (p : Pairing n) (t : Configuration n) :
    Graph.BoundaryEquiv (wiring p t 0) p.padBottom.Adj (boundary 0 (Nat.zero_le n)) id where
  toFun := baseProject
  invFun := Sum.inl
  map_edge := fun _ _ h => .single (base_edge h)
  inv_edge := fun _ _ h => .single h
  map_boundary := fun i => by simp [baseProject]
  inv_boundary := fun i => by simp
  map_used := fun _ ⟨w,hw⟩ => ⟨baseProject w,base_edge hw⟩
  inv_used := fun _ ⟨w,hw⟩ => ⟨.inl w,hw⟩
  retract := fun _ hv => by rw [base_used hv]; exact .refl
  inv_retract := fun _ _ => .refl

lemma base_realizes (p : Pairing n) (t : Configuration n) :
    GraphRealizes (wiring p t 0) (boundary 0 (Nat.zero_le n)) p.padBottom :=
  (baseEquiv p t).symm.realizes p.padBottom.graphRealizes

 def gate (t : Configuration n) (row : Fin n) : Gate (n+1) :=
  ⟨row.castSucc,row.succ,by simp,t row⟩

 def circuit (t : Configuration n) : (k : ℕ) → k≤n → Circuit (n+1)
  | 0,_ => .nil
  | k+1,hk => .snoc (circuit t k (by omega)) (gate t ⟨k,hk⟩)

lemma circuit_support (p : Pairing n) (t : Configuration n) (k : ℕ) (hk : k≤n) :
    Circuit.support p.padBottom (circuit t k hk) = support p t k hk := by
  induction k with
  | zero => funext i; simp [circuit,Circuit.support,support]
  | succ k ih =>
    funext i
    apply propext
    change (if i=(⟨k,hk⟩:Fin n).castSucc then (t ⟨k,hk⟩).Occupied 2 else
      if i=(⟨k,hk⟩:Fin n).succ then (t ⟨k,hk⟩).Occupied 3 else
      Circuit.support p.padBottom (circuit t k (by omega)) i) ↔ support p t (k+1) hk i
    rw [ih]
    exact support_step p t ⟨k,hk⟩ i

lemma circuit_sound (p : Pairing n) (t : Configuration n) (k : ℕ) (hk : k≤n)
    (q : Pairing (n+1)) (he : Circuit.eval p.padBottom (circuit t k hk)=some q) :
    GraphRealizes (wiring p t k) (boundary k hk) q := by
  induction k generalizing q with
  | zero => have hq : p.padBottom=q := Option.some.inj he; subst q; exact base_realizes p t
  | succ k ih =>
    let row : Fin n := ⟨k,hk⟩
    let c := circuit t k (by omega)
    change (Circuit.eval p.padBottom c).bind
      (fun r => r.tileStep row.castSucc row.succ (by simp [row]) (t row))=some q at he
    cases hr : Circuit.eval p.padBottom c with
    | none => simp [hr] at he
    | some r =>
      have hstep : r.tileStep row.castSucc row.succ (by simp [row]) (t row)=some q := by
        simpa only [hr,Option.bind_some] using he
      have hp := ih (by omega) r hr
      have hs : support p t k (by omega)=r.Occupied := by
        rw [←circuit_support p t k (by omega)]
        exact (Circuit.eval_sound p.padBottom c r hr).2.2
      have hne : row.castSucc≠row.succ := by intro hh; have hf := congrArg Fin.val hh; dsimp at hf; omega
      have hc := ((graph_gate_step_iff hp row.castSucc row.succ (by simp) (t row) q).mpr hstep).2
      have hc' := (CompactGate.realizes_iff hp (boundary_injective k (by omega))
        row.castSucc row.succ hne (t row) q).mp hc
      rw [←hs] at hc'
      have hn := ((ports p t row).realizes_iff (boundary_injective k (by omega))
        (support p t k (by omega)) row.castSucc row.succ (t row) q).mp hc'
      change GraphRealizes (nextWiring p t row) ((ports p t row).boundary row.castSucc row.succ) q at hn
      rw [next_eq p t row,funext (boundary_step p t row)] at hn
      exact hn

lemma circuit_exists (p : Pairing n) (t : Configuration n) (k : ℕ) (hk : k≤n)
    (hc : Circuit.Compatible p.padBottom (circuit t k hk))
    (hd : Graph.DrainsBoundary (wiring p t k) (boundary k hk)) :
    ∃ q, Circuit.eval p.padBottom (circuit t k hk)=some q := by
  induction k with
  | zero => exact ⟨p.padBottom,rfl⟩
  | succ k ih =>
    let row : Fin n := ⟨k,hk⟩
    let hkn : k≤n := by omega
    let c := circuit t k hkn
    change Circuit.Compatible p.padBottom c ∧
      (Circuit.support p.padBottom c row.castSucc ↔ (t row).Occupied 0) ∧
      (Circuit.support p.padBottom c row.succ ↔ (t row).Occupied 1) at hc
    obtain ⟨hc,hl,hr⟩ := hc
    have hdnext : Graph.DrainsBoundary (nextWiring p t row)
        ((ports p t row).boundary row.castSucc row.succ) := by
      rw [next_eq,funext (boundary_step p t row)]
      exact hd
    have hcompact := ((ports p t row).contraction (boundary_injective k hkn)
      (support p t k hkn) row.castSucc row.succ (t row)).drains_inv hdnext
    have hold := CompactGate.drains_local (wiring p t k) (boundary k hkn)
      (support p t k hkn) row.castSucc row.succ (t row) hcompact
    obtain ⟨r,he⟩ := ih hkn hc hold
    have hp := circuit_sound p t k hkn r he
    have hs : support p t k hkn=r.Occupied := by
      rw [←circuit_support]
      exact (Circuit.eval_sound p.padBottom c r he).2.2
    have hcomp : CutPatch.Compatible (r.cutShape row.castSucc row.succ) (t row) := by
      rw [r.cutShape_compatible]
      rw [circuit_support p t k hkn,hs] at hl hr
      exact ⟨hl,hr⟩
    have hne : row.castSucc≠row.succ := by
      intro hh; have hf := congrArg Fin.val hh; dsimp at hf; omega
    rw [hs] at hcompact
    have hfull := (CompactGate.contraction hp (boundary_injective k hkn)
      row.castSucc row.succ hne (t row)).drains_inv hcompact
    obtain ⟨q,hq⟩ := graph_gate_step_exists hp row.castSucc row.succ (by simp) (t row) hcomp hfull
    refine ⟨q,?_⟩
    change (Circuit.eval p.padBottom c).bind
      (fun r => r.tileStep row.castSucc row.succ (by simp) (t row))=some q
    have he' : Circuit.eval p.padBottom c=some r := he
    simpa only [he',Option.bind_some] using hq

lemma circuit_iff (p : Pairing n) (t : Configuration n) (k : ℕ) (hk : k≤n)
    (q : Pairing (n+1)) : Circuit.eval p.padBottom (circuit t k hk)=some q ↔
      Circuit.Compatible p.padBottom (circuit t k hk) ∧
      GraphRealizes (wiring p t k) (boundary k hk) q := by
  constructor
  · intro h
    exact ⟨(Circuit.eval_sound p.padBottom (circuit t k hk) q h).1,circuit_sound p t k hk q h⟩
  · rintro ⟨hc,hq⟩
    obtain ⟨r,hr⟩ := circuit_exists p t k hk hc hq.drainsBoundary
    have he := (circuit_sound p t k hk r hr).unique hq
    exact he ▸ hr

end BoundaryTracking

section InputCompatibility
variable {n : ℕ} (p : Pairing n) (t : Configuration n)

def inputCompatible (row : Fin n) : Prop :=
  (support p t row.val (Nat.le_of_lt row.isLt) row.castSucc ↔ (t row).Occupied 0) ∧
  (support p t row.val (Nat.le_of_lt row.isLt) row.succ ↔ (t row).Occupied 1)

lemma circuit_compatible_iff (k : ℕ) (hk : k≤n) :
    Circuit.Compatible p.padBottom (circuit t k hk) ↔
      ∀ row : Fin n, row.val<k → inputCompatible p t row := by
  induction k with
  | zero => simp [circuit,Circuit.Compatible]
  | succ k ih =>
    change (Circuit.Compatible p.padBottom (circuit t k (by omega)) ∧
      (Circuit.support p.padBottom (circuit t k (by omega)) (⟨k,hk⟩:Fin n).castSucc ↔ (t ⟨k,hk⟩).Occupied 0) ∧
      (Circuit.support p.padBottom (circuit t k (by omega)) (⟨k,hk⟩:Fin n).succ ↔ (t ⟨k,hk⟩).Occupied 1)) ↔ _
    rw [ih,circuit_support]
    change ((∀ row : Fin n, row.val<k → inputCompatible p t row) ∧ inputCompatible p t ⟨k,hk⟩) ↔ _
    constructor
    · rintro ⟨hc,hr⟩ row hrow
      by_cases h : row.val<k
      · exact hc row h
      · have he : row=(⟨k,hk⟩:Fin n) := Fin.ext (by dsimp; omega)
        exact he ▸ hr
    · intro hc
      exact ⟨fun row hr => hc row (by omega),hc ⟨k,hk⟩ (by simp)⟩

structure InputConditions : Prop where
  west : ∀ i, (t i).Occupied 1 ↔ p.Occupied i
  south : ∀ i, i.val=0 → ¬(t i).Occupied 0
  glued : ∀ i j, i.val+1=j.val → ((t i).Occupied 3 ↔ (t j).Occupied 0)

lemma all_input_iff : (∀ row, inputCompatible p t row) ↔ InputConditions p t := by
  constructor
  · intro hc
    constructor
    · intro i; exact ((right_support p t i).symm.trans (hc i).2).symm
    · intro i hi hocc
      exact left_support_zero p t i hi ((hc i).1.mpr hocc)
    · intro i j hij
      have hj : 0<j.val := by omega
      have he : prev j hj=i := Fin.ext (by simp only [prev]; omega)
      have hh := (left_support_pos p t j hj).symm.trans (hc j).1
      simpa only [he] using hh
  · intro hc row
    refine ⟨?_,(right_support p t row).trans (hc.west row).symm⟩
    by_cases hz : row.val=0
    · exact ⟨fun h => (left_support_zero p t row hz h).elim,
        fun h => (hc.south row hz h).elim⟩
    · have hp : 0<row.val := by omega
      exact (left_support_pos p t row hp).trans (hc.glued (prev row hp) row (prev_val_add row hp))

lemma full_compatible_iff : Circuit.Compatible p.padBottom (circuit t n le_rfl) ↔ InputConditions p t := by
  rw [circuit_compatible_iff]
  exact (show (∀ row : Fin n, row.val<n → inputCompatible p t row) ↔ ∀ row, inputCompatible p t row
    from ⟨fun h row => h row row.isLt, fun h row _ => h row⟩).trans (all_input_iff p t)

end InputCompatibility

variable {n : ℕ} (hn : 0<n) (p q : Pairing n) (t : Configuration n)

lemma fullBoundary_injective : Function.Injective (fullBoundary hn) := by
  intro i j he
  apply boundary_injective n le_rfl
  rw [full_boundary hn,full_boundary hn,he]

lemma east_used (i : Fin n) : Graph.Used (Wiring p t) (i,2) ↔ (t i).Occupied 2 := by
  constructor
  · rintro ⟨⟨j,b⟩,hw⟩
    rcases hw with ⟨_,ht⟩ | hh | hh | hh
    · exact ⟨b,ht⟩
    all_goals simp at hh
  · rintro ⟨b,hb⟩; exact ⟨(i,b),Or.inl ⟨rfl,hb⟩⟩

lemma north_isolated (i : Fin n) (hi : i.val+1=n) (ht : ¬(t i).Occupied 3)
    (v : Vertex n) : ¬Wiring p t (i,3) v := by
  intro hw
  rcases hw with ⟨_,ht'⟩ | hh | ⟨_,_,hij,_⟩ | hh
  · exact ht ⟨v.2,ht'⟩
  · simp at hh
  · have hv:=v.1.isLt; dsimp at hij; omega
  · simp at hh

lemma graph_of_realizes (h : Realizes p q t) : GraphRealizes (Wiring p t) (fullBoundary hn) q.padTop := by
  constructor
  · intro v w hvw
    obtain ⟨i,hi,hr⟩ := h.no_loop v w hvw
    exact ⟨i.castSucc,(q.padTop_occupied_castSucc i).mpr hi,by simpa [fullBoundary,Reach] using hr⟩
  · intro i j
    induction i using Fin.lastCases with
    | last =>
      have hi : (⟨n-1,by omega⟩:Fin n).val+1=n := by dsimp; omega
      have hh (v : Vertex n) := Relation.reflTransGen_iff_eq (b:=v) (north_isolated p t ⟨n-1,by omega⟩ hi (h.north _ hi))
      induction j using Fin.lastCases with
      | last => exact ⟨fun _ => Or.inl rfl,fun _ => .refl⟩
      | cast j =>
        simp only [fullBoundary,Fin.lastCases_last,Fin.lastCases_castSucc]
        rw [hh _]
        simp [(Fin.castSucc_ne_last j).symm]
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [fullBoundary,Fin.lastCases_last,Fin.lastCases_castSucc]
        constructor
        · intro hr
          have hi : (⟨n-1,by omega⟩:Fin n).val+1=n := by dsimp; omega
          have he := (Relation.reflTransGen_iff_eq
            (north_isolated p t ⟨n-1,by omega⟩ hi (h.north _ hi))).mp (reach_symm hr)
          have hf := congrArg Prod.snd he
          simp at hf
        · intro he; simp at he
      | cast j =>
        simp only [fullBoundary,Fin.lastCases_castSucc,Fin.castSucc_inj,Pairing.padTop_adj_castSucc]
        by_cases hij : i=j
        · subst j; exact ⟨fun _ => Or.inl rfl,fun _ => .refl⟩
        · simp only [hij,false_or]
          exact (h.output i j hij).symm

lemma realizes_of_graph (hc : InputConditions p t)
    (h : GraphRealizes (Wiring p t) (fullBoundary hn) q.padTop) : Realizes p q t := by
  refine ⟨hc.west,?_,hc.south,?_,hc.glued,?_,?_⟩
  · intro i
    have hh := h.boundary_used_iff (fullBoundary_injective hn) i.castSucc
    simpa only [fullBoundary,Fin.lastCases_castSucc,east_used,Pairing.padTop_occupied_castSucc] using hh
  · intro i hi ht
    have he : i=(⟨n-1,by omega⟩:Fin n) := Fin.ext (by dsimp; omega)
    obtain ⟨b,hb⟩ := ht
    have hu : Graph.Used (Wiring p t) (fullBoundary hn (Fin.last n)) := by
      rw [he] at hb
      simp only [fullBoundary,Fin.lastCases_last]
      exact ⟨(⟨n-1,by omega⟩,b),Or.inl ⟨rfl,hb⟩⟩
    exact q.padTop_not_occupied_last ((h.boundary_used_iff (fullBoundary_injective hn) _).mp hu)
  · intro v w hvw
    obtain ⟨i,hi,hr⟩ := h.no_loop v w hvw
    induction i using Fin.lastCases with
    | last => exact (q.padTop_not_occupied_last hi).elim
    | cast i => exact ⟨i,(q.padTop_occupied_castSucc i).mp hi,by simpa [fullBoundary,Reach] using hr⟩
  · intro i j hij
    have hh := h.reach i.castSucc j.castSucc
    simpa only [fullBoundary,Fin.lastCases_castSucc,Fin.castSucc_inj,Pairing.padTop_adj_castSucc,
      hij,false_or,Reach] using hh.symm

lemma realizes_graph_iff : Realizes p q t ↔ InputConditions p t ∧
    GraphRealizes (Wiring p t) (fullBoundary hn) q.padTop :=
  ⟨fun h => ⟨⟨h.west,h.south,h.glued⟩,graph_of_realizes hn p q t h⟩,
   fun h => realizes_of_graph hn p q t h.1 h.2⟩

include hn in
lemma column_eval_iff : Circuit.eval p.padBottom (circuit t n le_rfl)=some q.padTop ↔ Realizes p q t := by
  rw [circuit_iff,full_compatible_iff,(fullEquiv hn p t).realizes_iff]
  exact (realizes_graph_iff hn p q t).symm

end ColumnGeometry

open Finset
open scoped Classical
variable {K : Type*} [CommRing K] {n : ℕ}

def position (i : Fin n) : Position (n+1) := ⟨i.castSucc,i.succ,by simp⟩

def program (w : Fin n → Weights K) : (k : ℕ) → k≤n → Program (n+1) K
  | 0,_ => .nil
  | k+1,hk => .snoc (program w k (by omega)) (position ⟨k,hk⟩) (w ⟨k,hk⟩)

def choicesEquiv (w : Fin n → Weights K) : (k : ℕ) → (hk : k≤n) →
    (program w k hk).Choices ≃ (Fin k → Tile)
  | 0,_ => {
      toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => PUnit.unit
      left_inv := fun _ => rfl
      right_inv := fun f => funext (fun i => Fin.elim0 i) }
  | k+1,hk => (Equiv.prodCongr (choicesEquiv w k (by omega)) (Equiv.refl Tile)).trans
      ((Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ : Fin (k+1) => Tile)))

lemma circuit_congr (t u : Configuration n) (k : ℕ) (hk : k≤n)
    (h : ∀ i, i.val<k → t i=u i) : circuit t k hk=circuit u k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change Circuit.snoc (circuit t k _) (gate t ⟨k,hk⟩)=Circuit.snoc (circuit u k _) (gate u ⟨k,hk⟩)
    rw [ih (by omega) (fun i hi => h i (by omega))]
    congr 1
    simp only [gate,h ⟨k,hk⟩ (by simp)]

omit [CommRing K] in
lemma choices_circuit (w : Fin n → Weights K) (k : ℕ) (hk : k≤n)
    (c : (program w k hk).Choices) (t : Configuration n)
    (ht : ∀ i : Fin k, t ⟨i.val,lt_of_lt_of_le i.isLt hk⟩=choicesEquiv w k hk c i) :
    (program w k hk).circuit c=circuit t k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rcases c with ⟨c,v⟩
    change Circuit.snoc ((program w k _).circuit c) ((position ⟨k,hk⟩).gate v)=
      Circuit.snoc (circuit t k _) (gate t ⟨k,hk⟩)
    have he : choicesEquiv w (k+1) hk (c,v) =
        Fin.snoc (choicesEquiv w k (by omega) c) v := by
      simp only [choicesEquiv, Equiv.prodCongr]
      rfl
    have ht' (i : Fin k) : t ⟨i.val,by omega⟩=choicesEquiv w k (by omega) c i := by
      simpa only [he, Fin.snoc_castSucc, Fin.val_castSucc] using ht i.castSucc
    rw [ih (by omega) c ht']
    congr 1
    have hv : t ⟨k,hk⟩=v := by simpa only [he, Fin.snoc_last, Fin.val_last] using ht (Fin.last k)
    simp only [position,Position.gate,gate,hv]

lemma choices_weight (w : Fin n → Weights K) (k : ℕ) (hk : k≤n)
    (c : (program w k hk).Choices) :
    (program w k hk).weight c = ∏ i : Fin k, (w ⟨i.val,lt_of_lt_of_le i.isLt hk⟩).tile
      (choicesEquiv w k hk c i) := by
  induction k with
  | zero => simp [program,Program.weight]
  | succ k ih =>
    rcases c with ⟨c,v⟩
    rw [Fin.prod_univ_castSucc]
    change (program w k _).weight c * (w ⟨k,hk⟩).tile v = _
    rw [ih (by omega) c]
    have he : choicesEquiv w (k+1) hk (c,v) =
        Fin.snoc (choicesEquiv w k (by omega) c) v := by
      simp only [choicesEquiv, Equiv.prodCongr]
      rfl
    simp only [he, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]

lemma program_column (hn : 0<n) (w : Fin n → Weights K) (p q : Pairing n) :
    (program w n le_rfl).matrix q.padTop p.padBottom=column w q p := by
  rw [Program.matrix_apply]
  unfold column
  apply Fintype.sum_equiv (choicesEquiv w n le_rfl)
  intro c
  have hc : (program w n le_rfl).circuit c=circuit (choicesEquiv w n le_rfl c) n le_rfl :=
    choices_circuit w n le_rfl c _ (fun _ => rfl)
  simp only [hc,column_eval_iff hn,choices_weight]

end PartialColumn
end
end CriticalStrip.Diagram

end OAI
