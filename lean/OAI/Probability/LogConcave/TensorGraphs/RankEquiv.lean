import Mathlib
import OAI.Probability.LogConcave.TensorGraphs.History
import OAI.Probability.LogConcave.OraclePrograms.CircuitBoundUpto

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.Frontier
open scoped BigOperators Classical
open TensorEnergy

variable {E C : Type*} [Fintype E] [Fintype C]
    (a b : E → ℕ) (hab : ∀e,a e<b e)
include hab in

theorem coordinate_contraction_bound_upto
    (A : ∀k,(Outgoing a k → C) → (Incoming b k → C) → ℝ) (M : ℕ → ℝ)
    (n : ℕ) (hM : ∀k<n,0≤M k) (hA : ∀k<n,Bound (A k) ((M k)^2))
    (han : ∀e,a e≤n) (close : (Live a b 0 → C) ≃ (Live a b n → C)) :
    |∑c : E → C,(∏k : Fin n,A k.val (fun e => c e.val) (fun e => c e.val))*
      (if (fun e : Live a b n => c e.val)=close (fun e : Live a b 0 => c e.val)
        then 1 else 0)| ≤
      (Fintype.card (Live a b 0 → C):ℝ)*(∏k∈Finset.range n,M k) := by
  rw [coordinate_sum_eq_circuit a b hab A n han
    (fun i j => if j=close i then 1 else 0)]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  exact closed_wire_circuit_bound_upto (D:=fun k => Live a b k → C)
    (I:=fun k => Incoming b k → C) (O:=fun k => Outgoing a k → C)
    (S:=fun k => Spectator a b k → C) A M
    (inputCoordinates a b hab) (outputCoordinates a b hab) n hM hA close
end LogConcaveSampling.Frontier
namespace LogConcaveSampling.GraphSchedule
open scoped BigOperators Classical
open TensorEnergy

variable {V U : Type*} [Fintype V] [Fintype U]
local instance edgeDecEqUp (q : ℕ) : DecidableEq (Edge (U:=U) q) := Classical.decEq _
local instance finDecEqUp (d : ℕ) : DecidableEq (Fin d) := Classical.decEq _

theorem scheduled_coordinate_bound_upto (key : V → ℕ) (src dst : U → V)
    (hkey : Function.Injective key) (hne : ∀e,src e≠dst e)
    (first last : V) (q d : ℕ)
    (A : ∀k,(Frontier.Outgoing (emit key src dst first last q) k → Fin d) →
      (Frontier.Incoming (absorb key src dst first last q) k → Fin d) → ℝ)
    (M : ℕ → ℝ) (hM : ∀k<length key,0≤M k) (hA : ∀k<length key,Bound (A k) ((M k)^2)) :
    |∑c : Edge (U:=U) q → Fin d,
      (∏k : Fin (length key),A k.val (fun e => c e.val) (fun e => c e.val))*
      (if (fun e : Frontier.Live (emit key src dst first last q)
          (absorb key src dst first last q) (length key) => c e.val)=
        close key src dst first last q
          (fun e : Frontier.Live (emit key src dst first last q)
            (absorb key src dst first last q) 0 => c e.val) then 1 else 0)|≤
      (d:ℝ)^q*(∏k∈Finset.range (length key),M k) := by
  calc
    _ ≤ (Fintype.card (Frontier.Live (emit key src dst first last q)
      (absorb key src dst first last q) 0 → Fin d):ℝ)*
        (∏k∈Finset.range (length key),M k) := by
      exact Frontier.coordinate_contraction_bound_upto (E:=Edge (U:=U) q) (C:=Fin d)
        (emit key src dst first last q) (absorb key src dst first last q)
        (emit_lt_absorb key src dst hkey hne first last q) A M (length key) hM hA
        (emit_le_length key src dst first last q) (close key src dst first last q)
    _ = _ := by
      rw [Fintype.card_fun,Fintype.card_fin,
        Fintype.card_congr (inputEdges key src dst first last q),Fintype.card_fin,Nat.cast_pow]
end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.GraphSchedule
open scoped BigOperators Classical
open TensorEnergy

variable {V U : Type*} [Fintype V] [Fintype U]
local instance edgeDecEqRUp (q : ℕ) : DecidableEq (Edge (U:=U) q) := Classical.decEq _
local instance finDecEqRUp (d : ℕ) : DecidableEq (Fin d) := Classical.decEq _

theorem reduced_coordinate_bound_upto (key : V → ℕ) (src dst : U → V)
    (hkey : Function.Injective key) (hne : ∀e,src e≠dst e)
    (first last : V) (q d : ℕ)
    (A : ∀k,(Frontier.Outgoing (emit key src dst first last q) k → Fin d) →
      (Frontier.Incoming (absorb key src dst first last q) k → Fin d) → ℝ)
    (M : ℕ → ℝ) (hM : ∀k<length key,0≤M k) (hA : ∀k<length key,Bound (A k) ((M k)^2)) :
    |∑c : U ⊕ Fin q → Fin d,
      ∏k : Fin (length key),A k.val (fun e => duplicate c e.val) (fun e => duplicate c e.val)|≤
      (d:ℝ)^q*(∏k∈Finset.range (length key),M k) := by
  rw [←sum_closed_coordinates key src dst first last q
    (fun c => ∏k : Fin (length key),A k.val (fun e => c e.val) (fun e => c e.val))]
  exact scheduled_coordinate_bound_upto key src dst hkey hne first last q d A M hM hA
end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.TraceOpening
open scoped Classical

variable {V : Type*} [Fintype V]

noncomputable def rankEquiv (key : V → ℕ) (hkey : Function.Injective key) :
    V ≃ Fin (Fintype.card V) := by
  letI : LinearOrder V := LinearOrder.lift' key hkey
  exact (Fintype.orderIsoFinOfCardEq V rfl).symm.toEquiv

lemma rankEquiv_lt (key : V → ℕ) (hkey : Function.Injective key) (u v : V) :
    rankEquiv key hkey u < rankEquiv key hkey v ↔ key u < key v := by
  let : LinearOrder V := LinearOrder.lift' key hkey
  exact (Fintype.orderIsoFinOfCardEq V rfl).symm.lt_iff_lt

theorem compress_order (key : V → ℕ) (hkey : Function.Injective key) :
    ∃e : V ≃ Fin (Fintype.card V), ∀u v,(e u).val < (e v).val ↔ key u<key v :=
  ⟨rankEquiv key hkey,rankEquiv_lt key hkey⟩
end LogConcaveSampling.TraceOpening
namespace LogConcaveSampling.GraphSchedule
open scoped Classical

variable {V : Type*} [Fintype V] [Nonempty V]

lemma length_equiv_val (e : V ≃ Fin (Fintype.card V)) :
    length (fun v => (e v).val)=Fintype.card V := by
  have hc : 0<Fintype.card V := Fintype.card_pos
  apply Nat.le_antisymm
  · unfold length
    have hh : Finset.univ.sup (fun v => (e v).val)<Fintype.card V := by
      exact (Finset.sup_lt_iff hc).mpr (fun v _ => (e v).isLt)
    omega
  · let v := e.symm ⟨Fintype.card V-1,by omega⟩
    have hv : (e v).val=Fintype.card V-1 := by simp [v]
    have hh := key_lt_length (fun w => (e w).val) v
    rw [hv] at hh
    omega
end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.GraphSchedule
open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [Nonempty V]

noncomputable def stageEquiv (e : V ≃ Fin (Fintype.card V)) :
    V ≃ Fin (length (fun v => (e v).val)) :=
  e.trans (finCongr (length_equiv_val e).symm)

lemma stageEquiv_val (e : V ≃ Fin (Fintype.card V)) (v : V) :
    (stageEquiv e v).val=(e v).val := rfl

lemma product_stages (e : V ≃ Fin (Fintype.card V)) {R : Type*} [CommMonoid R] (f : ℕ → R) :
    (∏k : Fin (length (fun v => (e v).val)),f k.val)=∏v,f (e v).val :=
  Eq.symm ((stageEquiv e).prod_comp (fun k => f k.val))

lemma product_stage_range (e : V ≃ Fin (Fintype.card V)) {R : Type*} [CommMonoid R] (f : ℕ → R) :
    (∏k∈Finset.range (length (fun v => (e v).val)),f k)=∏v,f (e v).val := by
  rw [←Fin.prod_univ_eq_prod_range]
  exact product_stages e f
end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.GraphSchedule
open scoped BigOperators Classical
open TensorEnergy

variable {V U : Type*} [Fintype V] [Fintype U] [Nonempty V]
local instance edgeDecEqRank (q : ℕ) : DecidableEq (Edge (U:=U) q) := Classical.decEq _
local instance finDecEqRank (d : ℕ) : DecidableEq (Fin d) := Classical.decEq _

theorem ranked_coordinate_bound (e : V ≃ Fin (Fintype.card V)) (src dst : U → V)
    (hne : ∀u,src u≠dst u) (first last : V) (q d : ℕ)
    (A : ∀k,(Frontier.Outgoing (emit (fun v => (e v).val) src dst first last q) k → Fin d) →
      (Frontier.Incoming (absorb (fun v => (e v).val) src dst first last q) k → Fin d) → ℝ)
    (M : V → ℝ) (hM : ∀v,0≤M v)
    (hA : ∀v,Bound (A (e v).val) ((M v)^2)) :
    |∑c : U ⊕ Fin q → Fin d,
      ∏v,A (e v).val (fun t => duplicate c t.val) (fun t => duplicate c t.val)|≤
      (d:ℝ)^q*(∏v,M v) := by
  let N : ℕ → ℝ := fun k => if hk : k<Fintype.card V then M (e.symm ⟨k,hk⟩) else 0
  have hN (v : V) : N (e v).val=M v := by
    simp only [N,dite_eq_left (e v).isLt,Fin.eta,Equiv.symm_apply_apply]
  have hkey : Function.Injective (fun v => (e v).val) := Fin.val_injective.comp e.injective
  have hm (k : ℕ) (hk : k<length (fun v => (e v).val)) : 0≤N k := by
    have hk' : k<Fintype.card V := by rwa [length_equiv_val e] at hk
    change 0 ≤ (if hk : k < Fintype.card V then M (e.symm ⟨k,hk⟩) else 0)
    rw [dite_eq_left hk']
    exact hM _
  have ha (k : ℕ) (hk : k<length (fun v => (e v).val)) : Bound (A k) ((N k)^2) := by
    have hk' : k<Fintype.card V := by rwa [length_equiv_val e] at hk
    have hh := hA (e.symm ⟨k,hk'⟩)
    have hkv : (e (e.symm ⟨k,hk'⟩)).val=k :=
      congrArg Fin.val (e.apply_symm_apply ⟨k,hk'⟩)
    rw [hkv] at hh
    simpa only [N,dite_eq_left hk'] using hh
  have hh := reduced_coordinate_bound_upto (fun v => (e v).val) src dst hkey hne
    first last q d A N hm ha
  have hs (c : U ⊕ Fin q → Fin d) := product_stages e (fun k => A k
    (fun t => duplicate c t.val) (fun t => duplicate c t.val))
  simp_rw [hs] at hh
  rw [product_stage_range e] at hh
  simp only [hN] at hh
  exact hh
end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.NetworkMoments
open MeasureTheory
open scoped ENNReal NNReal BigOperators

theorem lintegral_primary_auxiliary_le
    {Ω P H : Type*} [MeasurableSpace Ω] [Fintype P] [Fintype H] [Nonempty P]
    {μ : Measure Ω} {f : P → Ω → ℝ≥0∞} {g : H → Ω → ℝ≥0∞}
    {M : P → ℝ≥0∞} {B : H → ℝ≥0∞}
    (hf : ∀i,AEMeasurable (f i) μ)
    (hm : ∀i,(∫⁻x,(f i x)^(Fintype.card P) ∂μ)≤(M i)^(Fintype.card P))
    (hg : ∀h x,g h x≤B h) (hB : ∀h,B h≠⊤) :
    (∫⁻x,(∏i,f i x)*(∏h,g h x) ∂μ)≤(∏i,M i)*(∏h,B h) := by
  have hb : (∏h,B h)≠⊤ := ENNReal.prod_ne_top (fun h _ => hB h)
  calc
    _ ≤ ∫⁻x,(∏i,f i x)*(∏h,B h) ∂μ :=
      lintegral_mono (fun x => mul_le_mul' le_rfl (Finset.prod_le_prod (fun h _ => hg h x)))
    _ = (∫⁻x,∏i,f i x ∂μ)*(∏h,B h) := lintegral_mul_const' _ _ hb
    _ ≤ _ := by
      apply mul_le_mul' _ le_rfl
      apply lintegral_prod_le Finset.univ Finset.univ_nonempty
      · exact fun i _ => hf i
      · simpa only [Finset.card_univ] using fun i (_ : i∈(Finset.univ : Finset P)) => hm i
end LogConcaveSampling.NetworkMoments
namespace LogConcaveSampling.GraphSchedule
open MeasureTheory TensorEnergy
open scoped BigOperators Classical ENNReal

variable {Ω P H U : Type*} [MeasurableSpace Ω] [Fintype P] [Fintype H] [Fintype U]
    [Nonempty P]
local instance edgeDecEqInt (q : ℕ) : DecidableEq (Edge (U:=U) q) := Classical.decEq _
local instance finDecEqInt (d : ℕ) : DecidableEq (Fin d) := Classical.decEq _

theorem integrated_coordinate_bound (μ : Measure Ω)
    (e : P ⊕ H ≃ Fin (Fintype.card (P ⊕ H))) (src dst : U → P ⊕ H)
    (hne : ∀u,src u≠dst u) (first last : P ⊕ H) (q d : ℕ)
    (A : Ω → ∀k,(Frontier.Outgoing (emit (fun v => (e v).val) src dst first last q) k → Fin d) →
      (Frontier.Incoming (absorb (fun v => (e v).val) src dst first last q) k → Fin d) → ℝ)
    (M : P ⊕ H → Ω → ℝ) (hM : ∀v x,0≤M v x)
    (hA : ∀v x,Bound (A x (e v).val) ((M v x)^2))
    (B : P → ℝ≥0∞) (C : H → ℝ≥0∞)
    (hMp : ∀i,AEMeasurable (fun x => ENNReal.ofReal (M (Sum.inl i) x)) μ)
    (hp : ∀i,(∫⁻x,ENNReal.ofReal (M (Sum.inl i) x)^(Fintype.card P) ∂μ)≤B i^(Fintype.card P))
    (hh : ∀h x,ENNReal.ofReal (M (Sum.inr h) x)≤C h) (hC : ∀h,C h≠⊤) :
    (∫⁻x,ENNReal.ofReal |∑c : U ⊕ Fin q → Fin d,
      ∏v,A x (e v).val (fun t => duplicate c t.val) (fun t => duplicate c t.val)| ∂μ)≤
      (d:ℝ≥0∞)^q*((∏i,B i)*(∏h,C h)) := by
  have hpw (x : Ω) : ENNReal.ofReal |∑c : U ⊕ Fin q → Fin d,
        ∏v,A x (e v).val (fun t => duplicate c t.val) (fun t => duplicate c t.val)|≤
      (d:ℝ≥0∞)^q*((∏i,ENNReal.ofReal (M (Sum.inl i) x))*
        (∏h,ENNReal.ofReal (M (Sum.inr h) x))) := by
    have hb := ENNReal.ofReal_le_ofReal (ranked_coordinate_bound e src dst hne first last q d
      (A x) (fun v => M v x) (fun v => hM v x) (fun v => hA v x))
    rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_natCast,ENNReal.ofReal_prod_of_nonneg (fun v _ => hM v x),
      Fintype.prod_sum_type] at hb
    exact hb
  calc
    _ ≤ ∫⁻x,(d:ℝ≥0∞)^q*((∏i,ENNReal.ofReal (M (Sum.inl i) x))*
        (∏h,ENNReal.ofReal (M (Sum.inr h) x))) ∂μ := lintegral_mono hpw
    _ = (d:ℝ≥0∞)^q*(∫⁻x,(∏i,ENNReal.ofReal (M (Sum.inl i) x))*
        (∏h,ENNReal.ofReal (M (Sum.inr h) x)) ∂μ) :=
      lintegral_const_mul' _ _ (by finiteness)
    _ ≤ _ := mul_le_mul' le_rfl
      (NetworkMoments.lintegral_primary_auxiliary_le hMp hp hh hC)
end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.AdjointRemoval
open scoped BigOperators

variable {P : Type*} [Fintype P] [DecidableEq P]

theorem terminal_moment_budgets {S : State P}
    (hS : S∈expand (Fintype.card P) initial) (j k : ℕ) :
    (∀i,(S.derivatives i).length≤Fintype.card P) ∧
    (∀h∈S.hessians,h.extra.length≤Fintype.card P) ∧
    (∑i,(S.derivatives i).length)+(S.hessians.map (fun h => h.extra.length)).sum≤
      Fintype.card P ∧
    (Fintype.card P)*(k+j)+(∑i,(S.derivatives i).length)+
      (S.hessians.map (fun h => h.extra.length)).sum≤(Fintype.card P)*(k+j+1) ∧
    (Fintype.card P)*(j+1)+(∑i,(S.derivatives i).length)+
      (S.hessians.map (fun h => h.extra.length+1)).sum≤
      2*(Fintype.card P)*(j+1) := by
  have hid := (full_expansion_bookkeeping (P:=P)).2 S hS |>.2.2
  have hsum : (S.hessians.map (fun h => h.extra.length+1)).sum=
      (S.hessians.map (fun h => h.extra.length)).sum+S.hessians.card := by
    induction S.hessians using Multiset.induction_on with
    | empty => simp
    | @cons a t ih => simp only [Multiset.map_cons,Multiset.sum_cons,Multiset.card_cons]; omega
  refine ⟨?_,?_,by omega,?_,?_⟩
  · intro i
    have hi := Finset.single_le_sum (s:=Finset.univ) (f:=fun i => (S.derivatives i).length)
      (fun a _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  · intro h hh
    have hi : h.extra.length≤(S.hessians.map (fun h => h.extra.length)).sum := by
      apply Multiset.le_sum_of_mem
      exact Multiset.mem_map.mpr ⟨h,hh,rfl⟩
    omega
  · nlinarith
  · rw [hsum]
    have hp : Fintype.card P≤Fintype.card P*(j+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    nlinarith
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open scoped Classical

variable {n : ℕ} {S : State (Fin (n+1))}

theorem actual_ranked_schedule
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (hβ : ∀k,0<β k) :
    ∃e : TargetVertex S ≃ Fin (Fintype.card (TargetVertex S)),
      ∀(q : ℕ),0<q → ∀v : TargetVertex S,
        Nonempty (Frontier.Incoming
          (GraphSchedule.absorb (fun v => (e v).val) (edgeSource (S:=S) β) (edgeTarget hS β)
            (Sum.inl 0) (Sum.inl (Fin.last n)) q) (e v).val) ∧
        Nonempty (Frontier.Outgoing
          (GraphSchedule.emit (fun v => (e v).val) (edgeSource (S:=S) β) (edgeTarget hS β)
            (Sum.inl 0) (Sum.inl (Fin.last n)) q) (e v).val) := by
  obtain ⟨key,hkey,_,hsplit⟩ := actual_removal_graph_order hS
  obtain ⟨e,he⟩ := TraceOpening.compress_order key hkey
  refine ⟨e,fun q hq v => ?_⟩
  apply GraphSchedule.factor_splits_nonempty (fun v => (e v).val)
    (edgeSource (S:=S) β) (edgeTarget hS β)
    (Sum.inl 0) (Sum.inl (Fin.last n)) q hq _ v
  intro w
  obtain ⟨hi,ho⟩ := hsplit w
  constructor
  · rcases hi with h | ⟨u,hu,hk⟩
    · exact Or.inl h
    · exact Or.inr ⟨u,adjacent_has_edge hS β hβ hu,(he u w).mpr hk⟩
  · rcases ho with h | ⟨u,hu,hk⟩
    · exact Or.inl h
    · exact Or.inr ⟨u,adjacent_has_edge hS β hβ hu,(he w u).mpr hk⟩
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.GraphSchedule
open scoped Classical

variable {V U : Type*} [Fintype V] (key : V → ℕ) (src dst : U → V)

def IncidentAt (first last v : V) (q : ℕ) : Edge (U:=U) q → Prop
  | Sum.inl u => src u=v ∨ dst u=v
  | Sum.inr (Sum.inl _) => first=v
  | Sum.inr (Sum.inr _) => last=v

lemma incidentAt_iff (hkey : Function.Injective key) (first last v : V) (q : ℕ)
    (t : Edge (U:=U) q) :
    IncidentAt src dst first last v q t ↔
      absorb key src dst first last q t=key v+1 ∨ emit key src dst first last q t=key v+1 := by
  rcases t with u | (i|i)
  · simp only [IncidentAt,absorb,emit]
    constructor
    · rintro (hs|ht)
      · rw [hs]; omega
      · rw [ht]; omega
    · intro h
      have he : key (src u)=key v ∨ key (dst u)=key v := by omega
      exact he.imp (fun hh => hkey hh) (fun hh => hkey hh)
  · simp only [IncidentAt,absorb,emit]
    constructor
    · intro h; exact Or.inl (congrArg (fun w => key w+1) h)
    · rintro (h|h)
      · exact hkey (by omega)
      · omega
  · simp only [IncidentAt,absorb,emit]
    have hv := key_lt_length key v
    constructor
    · intro h; exact Or.inr (congrArg (fun w => key w+1) h)
    · rintro (h|h)
      · omega
      · exact hkey (by omega)

noncomputable def incidentSplit (hkey : Function.Injective key) (hne : ∀u,src u≠dst u)
    (first last v : V) (q : ℕ) :
    {t : Edge (U:=U) q // IncidentAt src dst first last v q t} ≃
      Frontier.Incoming (absorb key src dst first last q) (key v) ⊕
      Frontier.Outgoing (emit key src dst first last q) (key v) where
  toFun t := if h : absorb key src dst first last q t.val=key v+1 then Sum.inl ⟨t.val,h⟩
    else Sum.inr ⟨t.val,((incidentAt_iff key src dst hkey first last v q t.val).mp t.property).resolve_left h⟩
  invFun t := match t with
    | Sum.inl t => ⟨t.val,(incidentAt_iff key src dst hkey first last v q t.val).mpr (Or.inl t.property)⟩
    | Sum.inr t => ⟨t.val,(incidentAt_iff key src dst hkey first last v q t.val).mpr (Or.inr t.property)⟩
  left_inv t := by dsimp only; split_ifs <;> rfl
  right_inv t := by
    rcases t with t|t
    · simp only [t.property,dite_eq_left]
    · have hn : absorb key src dst first last q t.val≠key v+1 := by
        have hh := emit_lt_absorb key src dst hkey hne first last q t.val
        have ht := t.property
        omega
      simp [hn]
end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.AdjointRemoval
open scoped BigOperators

variable {P : Type*} [Fintype P] [DecidableEq P] {S : State P}

lemma destination_iff_mem (hS : S∈expand (Fintype.card P) initial)
    (i : P) (v : TargetVertex S) : destination hS i=v ↔ i∈ports S v := by
  constructor
  · intro h
    simpa only [h] using label_mem_destination hS i
  · intro h
    let p : ports S v := (ports S v).mkToType i ⟨0,Multiset.count_pos.mpr h⟩
    exact destination_label hS ⟨v,p⟩

lemma ports_nodup (hS : S∈expand (Fintype.card P) initial) (v : TargetVertex S) :
    (ports S v).Nodup := by
  have hs : (∑v,ports S v)=Finset.univ.val := (sum_ports S).trans (terminal_ports hS)
  have hv := Finset.single_le_sum (s:=Finset.univ) (f:=ports S)
    (fun _ _ => Multiset.zero_le _) (Finset.mem_univ v)
  rw [hs] at hv
  exact Multiset.nodup_of_le hv (Finset.univ : Finset P).nodup

lemma derivatives_nodup (hS : S∈expand (Fintype.card P) initial) (i : P) :
    (S.derivatives i).Nodup := ports_nodup hS (Sum.inl i)

noncomputable def derivativeEdgeEquiv (hS : S∈expand (Fintype.card P) initial) (i : P) :
    Fin (S.derivatives i).length ≃ {j : P // destination hS j=Sum.inl i} :=
  (List.Nodup.getEquiv (S.derivatives i) (derivatives_nodup hS i)).trans
    (Equiv.subtypeEquivRight (fun j => (destination_iff_mem hS j (Sum.inl i)).symm))

lemma derivativeEdgeEquiv_val (hS : S∈expand (Fintype.card P) initial) (i : P)
    (k : Fin (S.derivatives i).length) :
    (derivativeEdgeEquiv hS i k).val=(S.derivatives i).get k := rfl

lemma hessian_slots_nodup (hS : S∈expand (Fintype.card P) initial) (h : S.hessians) :
    ((h : Hessian P).first::(h : Hessian P).second::(h : Hessian P).extra).Nodup :=
  ports_nodup hS (Sum.inr h)

noncomputable def hessianEdgeEquiv (hS : S∈expand (Fintype.card P) initial) (h : S.hessians) :
    Fin ((h : Hessian P).first::(h : Hessian P).second::(h : Hessian P).extra).length ≃
      {j : P // destination hS j=Sum.inr h} :=
  (List.Nodup.getEquiv _ (hessian_slots_nodup hS h)).trans
    (Equiv.subtypeEquivRight (fun j => (destination_iff_mem hS j (Sum.inr h)).symm))

lemma hessianEdgeEquiv_val (hS : S∈expand (Fintype.card P) initial) (h : S.hessians)
    (k : Fin ((h : Hessian P).first::(h : Hessian P).second::(h : Hessian P).extra).length) :
    (hessianEdgeEquiv hS h k).val=
      ((h : Hessian P).first::(h : Hessian P).second::(h : Hessian P).extra).get k := rfl
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.GraphSchedule
variable {V : Type*} [Fintype V]

noncomputable def rankExtend (e : V ≃ Fin (Fintype.card V)) {D : ℕ → Type*}
    (z : ∀k,D k) (a : ∀v,D (e v).val) (k : ℕ) : D k :=
  if hk : k<Fintype.card V then
    cast (congrArg D (congrArg Fin.val (e.apply_symm_apply ⟨k,hk⟩))) (a (e.symm ⟨k,hk⟩))
  else z k

lemma rankExtend_at (e : V ≃ Fin (Fintype.card V)) {D : ℕ → Type*}
    (z : ∀k,D k) (a : ∀v,D (e v).val) (v : V) :
    rankExtend e z a (e v).val=a v := by
  simp only [rankExtend,dite_eq_left (e v).isLt,Fin.eta]
  apply eq_of_heq
  exact (cast_heq _ _).trans (congr_arg_heq a (e.symm_apply_apply v))
end LogConcaveSampling.GraphSchedule

end UpperProof
end
end
end

end OAI
