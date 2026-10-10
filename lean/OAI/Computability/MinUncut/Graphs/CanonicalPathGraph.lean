import Mathlib
import OAI.Computability.MinUncut.PCP.Occurrences
import OAI.Computability.MinUncut.Graphs.GraphOutput
import OAI.Computability.MinUncut.Estimates.PolynomialRecursor

namespace OAI

section
open scoped BigOperators
namespace MinUncut.PathRealization

def number (N M : ℕ) : Vertex (Fin N) (Fin M) ≃ Fin (N+M*3) :=
  (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv

lemma number_left (N M : ℕ) (v : Fin N) : (number N M (.inl v)).val=v.val := rfl
lemma number_right (N M : ℕ) (d : Fin M) (i : Fin 3) :
    (number N M (.inr (d,i))).val=N+i.val+3*d.val := by
  simp [number,finProdFinEquiv,finSumFinEquiv,Nat.add_assoc]

def canonicalAdjacent {N M : ℕ} (e : Fin M → Demand (Fin N))
    (u v : Fin (N+M*3)) : Bool :=
  decide (∃ d : Fin M, ∃ j : Fin 4,
    j.val < (if (e d).equal then 4 else 3) ∧
      ((u=number N M (ends e (d,j)).1 ∧ v=number N M (ends e (d,j)).2) ∨
       (v=number N M (ends e (d,j)).1 ∧ u=number N M (ends e (d,j)).2)))

lemma canonicalAdjacent_symmetric {N M : ℕ} (e : Fin M → Demand (Fin N))
    (u v : Fin (N+M*3)) : canonicalAdjacent e u v=canonicalAdjacent e v u := by
  simp only [canonicalAdjacent,decide_eq_decide]
  apply exists_congr
  intro d
  apply exists_congr
  intro j
  exact and_congr_right (fun _ => or_comm)

lemma canonicalAdjacent_loopless {N M : ℕ} (e : Fin M → Demand (Fin N))
    (u : Fin (N+M*3)) : canonicalAdjacent e u u=false := by
  simp only [canonicalAdjacent,decide_eq_false_iff_not]
  rintro ⟨d,j,hj,h|h⟩ <;>
    exact ends_ne e ⟨(d,j),hj⟩ ((number N M).injective (h.1.symm.trans h.2))

def canonicalOutput {N M : ℕ} (e : Fin M → Demand (Fin N)) (k : ℕ) (hk : 1≤k) : Output where
  vertices := N+M*3
  adjacent := canonicalAdjacent e
  symmetric := canonicalAdjacent_symmetric e
  loopless := canonicalAdjacent_loopless e
  threshold := k
  threshold_pos := hk

lemma canonicalOutput_eq {N M : ℕ} (e : Fin M → Demand (Fin N)) (k : ℕ) (hk : 1≤k) :
    canonicalOutput e k hk=output e (number N M) k hk := by
  have ha : canonicalAdjacent e=(output e (number N M) k hk).adjacent := by
    funext u v
    apply Bool.eq_iff_iff.mpr
    rw [output_adjacent_iff]
    simp only [canonicalAdjacent,decide_eq_true_eq]
    constructor
    · rintro ⟨d,j,hj,h⟩
      refine ⟨⟨(d,j),hj⟩,?_⟩
      change s(u,v)=s(number N M (ends e (d,j)).1,number N M (ends e (d,j)).2)
      exact Sym2.eq_iff.mpr (h.imp id And.symm)
    · rintro ⟨⟨⟨d,j⟩,hj⟩,h⟩
      exact ⟨d,j,hj,(Sym2.eq_iff.mp h).imp id And.symm⟩
  unfold output at ha
  unfold canonicalOutput output
  congr 1

lemma canonicalOutput_yes {N M : ℕ} (e : Fin M → Demand (Fin N)) (k : ℕ) (hk : 1≤k)
    (s : Fin N → Bool) (h : totalFailure e s≤k) : (canonicalOutput e k hk).opt≤k := by
  rw [canonicalOutput_eq]
  exact output_yes _ _ _ _ s h

lemma canonicalOutput_no {N M : ℕ} (e : Fin M → Demand (Fin N)) (k : ℕ) (hk : 1≤k)
    (K : ℕ) (h : ∀ s, K*k<totalFailure e s) : K*k<(canonicalOutput e k hk).opt := by
  rw [canonicalOutput_eq]
  exact output_no _ _ _ _ _ h

end MinUncut.PathRealization

end
namespace MinUncut.Costed.GraphRegisters
open MinUncut.Costed.Expr

def demandOffset : Expr := .add (.const 11) (.add (.reg 8) (.mul (.const 3) (.reg 0)))
def demandLeft : Expr := .at demandOffset
def demandRight : Expr := .at (.add demandOffset (.const 1))
def demandEqual : Expr := .at (.add demandOffset (.const 2))
def privateBase : Expr := .add (.reg 2) (.mul (.const 3) (.reg 0))
def localEdge : Expr :=
  (Expr.edge (.reg 6) (.reg 7) demandLeft privateBase).or
  ((Expr.edge (.reg 6) (.reg 7) privateBase (.add privateBase (.const 1))).or
    (.cond demandEqual
      (Expr.edge (.reg 6) (.reg 7) (.add privateBase (.const 1)) demandRight)
      ((Expr.edge (.reg 6) (.reg 7) (.add privateBase (.const 1))
        (.add privateBase (.const 2))).or
       (Expr.edge (.reg 6) (.reg 7) (.add privateBase (.const 2)) demandRight))))
def accumulatedEdge : Expr := (Expr.reg 1).or localEdge

lemma localEdge_le_one (v : List ℕ) : localEdge.eval v≤1 := by
  apply Expr.eval_or_le_one
  apply Expr.eval_or_le_one
  simp only [Expr.eval]
  split_ifs
  · exact Expr.eval_edge_le_one ..
  · exact Expr.eval_or_le_one _ _ _ (Expr.eval_edge_le_one ..)

lemma accumulatedEdge_le_one (v : List ℕ) : accumulatedEdge.eval v≤1 :=
  Expr.eval_or_le_one _ _ _ (localEdge_le_one v)

open PolyProgram Polynomial

def cumulative (v : List ℕ) : ℕ → ℕ :=
  scalarRec (fun _=>[0]) (fun w=>[accumulatedEdge.eval w]) v

lemma cumulative_le_one (v : List ℕ) (n : ℕ) : cumulative v n≤1 := by
  cases n with
  | zero => simp only [cumulative,scalarRec,List.headI_cons]; omega
  | succ n => exact accumulatedEdge_le_one _

noncomputable def adjacencyProgram : PolyProgram (fun v=>[cumulative v (v.drop 1).headI]) :=
  (prec (const 0) accumulatedEdge.program 1 (by
    intro n v i hi
    simpa only [eval_one,cumulative] using cumulative_le_one v i)).comp
      ((projection 1).cons id)

open PolyProgram Polynomial

structure RenderState where
  N : ℕ
  M : ℕ
  threshold : ℕ
  V : ℕ
  row : ℕ
  col : ℕ
  q : ℕ
  tape : List ℕ

def RenderState.encode (s : RenderState) : List ℕ :=
  s.N::s.M::s.threshold::s.V::s.row::s.col::s.q::s.tape

def parseState (v : List ℕ) : RenderState :=
  ⟨v.headI,(v.drop 1).headI,(v.drop 2).headI,(v.drop 3).headI,
    (v.drop 4).headI,(v.drop 5).headI,(v.drop 6).headI,v.drop 7⟩

@[simp] lemma parse_encode (s : RenderState) : parseState s.encode=s := by
  cases s; rfl

def RenderState.tick (s : RenderState) : RenderState :=
  {s with row := if s.col=0 then s.row-1 else s.row
          col := if s.col=0 then s.V-1 else s.col-1
          q := s.q+1
          tape := cumulative s.encode s.M::s.tape}

def renderTick (v : List ℕ) : List ℕ := (parseState v).tick.encode

lemma renderTick_encode (s : RenderState) : renderTick s.encode=s.tick.encode := by
  simp only [renderTick,parse_encode]

def nextRow : Expr := .cond (.reg 5) (.sub (.reg 4) (.const 1)) (.reg 4)
def nextCol : Expr := .cond (.reg 5) (.sub (.reg 3) (.const 1)) (.sub (.reg 5) (.const 1))
def nextCount : Expr := .add (.reg 6) (.const 1)

noncomputable def normalizeProgram : PolyProgram (fun v=>(parseState v).encode) :=
  ((projection 0).cons ((projection 1).cons ((projection 2).cons ((projection 3).cons
    ((projection 4).cons ((projection 5).cons ((projection 6).cons (drop 7)))))))).ofEq (by intro v; rfl)

noncomputable def tickProgram : PolyProgram renderTick :=
  (((projection 0).cons ((projection 1).cons ((projection 2).cons ((projection 3).cons
    (nextRow.program.cons (nextCol.program.cons (nextCount.program.cons
      (adjacencyProgram.cons (drop 7))))))))).comp normalizeProgram).ofEq (by
        intro v
        rfl)

lemma parse_encode_magnitude (v : List ℕ) : magnitude (parseState v).encode≤8*magnitude v+7 := by
  have h (i : ℕ) := (magnitude_head (v.drop i)).trans (magnitude_drop i v)
  have h₀ := h 0; have h₁ := h 1; have h₂ := h 2; have h₃ := h 3
  have h₄ := h 4; have h₅ := h 5; have h₆ := h 6
  have ht := magnitude_drop 7 v
  simp only [parseState,RenderState.encode,magnitude_cons]
  simp only [List.drop_zero] at h₀
  omega

lemma tick_V (s : RenderState) : s.tick.V=s.V := rfl

lemma tick_magnitude (s : RenderState) :
    magnitude s.tick.encode≤ magnitude s.encode+s.V+3 := by
  have h := cumulative_le_one s.encode s.M
  simp only [RenderState.encode] at h
  have hr : (if s.col=0 then s.row-1 else s.row)≤ s.row := by split_ifs <;> omega
  have hc : (if s.col=0 then s.V-1 else s.col-1)≤ s.col+s.V := by split_ifs <;> omega
  simp only [RenderState.encode,RenderState.tick,magnitude_cons]
  omega

lemma tick_iter_V (n : ℕ) (s : RenderState) : (RenderState.tick^[n] s).V=s.V := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply',tick_V] using ih

lemma tick_iter_magnitude (n : ℕ) (s : RenderState) :
    magnitude (RenderState.tick^[n] s).encode≤ magnitude s.encode+n*(s.V+3) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := tick_magnitude (RenderState.tick^[n] s)
    rw [tick_iter_V] at h
    simp only [Function.iterate_succ_apply']
    simp only [Nat.succ_mul] at *
    omega

lemma renderTick_iter_encode (n : ℕ) (s : RenderState) :
    renderTick^[n] s.encode=(RenderState.tick^[n] s).encode := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply',ih,renderTick_encode]

lemma renderTick_iter_succ (n : ℕ) (v : List ℕ) :
    renderTick^[n+1] v=(RenderState.tick^[n+1] (parseState v)).encode := by
  rw [Function.iterate_succ_apply,renderTick,renderTick_iter_encode,Function.iterate_succ_apply]

lemma renderTick_iter_bound (n : ℕ) (v : List ℕ) (i : ℕ) (hi : i≤n) :
    magnitude (renderTick^[i] v)≤(C 20*(X+1)^2:Polynomial ℕ).eval (magnitude (n::v)) := by
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, magnitude_cons]
  let s := n+1+magnitude v+1
  have hs : 1≤ s := by dsimp [s]; omega
  have hm : magnitude v≤ s := by dsimp [s]; omega
  have hn : n≤ s := by dsimp [s]; omega
  have hsq : s≤ s^2 := Nat.le_self_pow (by omega) _
  cases i with
  | zero => simp only [Function.iterate_zero,Function.id_def]; nlinarith
  | succ i =>
    rw [renderTick_iter_succ]
    have h := tick_iter_magnitude (i+1) (parseState v)
    have h₀ := parse_encode_magnitude v
    have hv : (parseState v).V≤ magnitude v :=
      (magnitude_head (v.drop 3)).trans (magnitude_drop 3 v)
    have hprod : (i+1)*((parseState v).V+3)≤ s*(3*s) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hh : magnitude (RenderState.tick^[i+1] (parseState v)).encode≤8*s+7+3*s^2 := by
      nlinarith
    change _≤20*s^2
    nlinarith

noncomputable def renderLoop : PolyProgram (fun v=>renderTick^[v.headI] v.tail) :=
  iterate tickProgram (C 20*(X+1)^2) renderTick_iter_bound

open MinUncut.PathRealization
open PolyProgram

def queryState (N M k V u v : ℕ) (acc data : List ℕ) : RenderState :=
  ⟨N,M,k,V,u,v,acc.length,acc++2::k::data⟩

def endpoint (u v a b : ℕ) : Prop := (u=a ∧ v=b) ∨ (u=b ∧ v=a)
instance (u v a b : ℕ) : Decidable (endpoint u v a b) := inferInstanceAs (Decidable (_∨_))

def localAdj (N d l r e u v : ℕ) : Prop :=
  endpoint u v l (N+3*d) ∨ endpoint u v (N+3*d) (N+3*d+1) ∨
    if e=0 then endpoint u v (N+3*d+1) r
    else endpoint u v (N+3*d+1) (N+3*d+2) ∨ endpoint u v (N+3*d+2) r
instance (N d l r e u v : ℕ) : Decidable (localAdj N d l r e u v) := by
  unfold localAdj; infer_instance

def rawLocal (N d : ℕ) (data : List ℕ) (u v : ℕ) : Prop :=
  localAdj N d (data.drop (3*d)).headI (data.drop (3*d+1)).headI
    (data.drop (3*d+2)).headI u v
instance (N d : ℕ) (data : List ℕ) (u v : ℕ) : Decidable (rawLocal N d data u v) :=
  inferInstanceAs (Decidable (localAdj ..))

lemma data_address (N M k V u v d a j : ℕ) (acc data : List ℕ) :
    ((d::a::(queryState N M k V u v acc data).encode).drop
      (11+acc.length+3*d+j)).headI=(data.drop (3*d+j)).headI := by
  have he : 11+acc.length+3*d+j=9+(acc.length+(2+(3*d+j))) := by omega
  rw [he,← List.drop_drop]
  change ((acc++2::k::data).drop (acc.length+(2+(3*d+j)))).headI=_
  rw [← List.drop_drop,List.drop_left]
  rw [Nat.add_comm 2 _]
  rfl

lemma bit_or (P Q : Prop) [Decidable P] [Decidable Q] :
    (if (if P then 1 else 0 : ℕ)=0 then (if Q then 1 else 0) else 1)=
      if P∨Q then 1 else 0 := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp,hq]

lemma localEdge_query (N M k V u v d a : ℕ) (acc data : List ℕ) :
    localEdge.eval (d::a::(queryState N M k V u v acc data).encode)=
      if rawLocal N d data u v then 1 else 0 := by
  have hL : demandLeft.eval (d::a::(queryState N M k V u v acc data).encode)=
      (data.drop (3*d)).headI := by
        simpa only [demandLeft,demandOffset,Expr.eval,queryState,RenderState.encode,
          List.drop_succ_cons,List.drop_zero,List.headI_cons,Nat.add_zero,Nat.add_assoc]
          using data_address N M k V u v d a 0 acc data
  have hR : demandRight.eval (d::a::(queryState N M k V u v acc data).encode)=
      (data.drop (3*d+1)).headI  := by
        simpa only [demandRight,demandOffset,Expr.eval,queryState,RenderState.encode,
          List.drop_succ_cons,List.drop_zero,List.headI_cons,Nat.add_assoc]
          using data_address N M k V u v d a 1 acc data
  have hE : demandEqual.eval (d::a::(queryState N M k V u v acc data).encode)=
      (data.drop (3*d+2)).headI  := by
        simpa only [demandEqual,demandOffset,Expr.eval,queryState,RenderState.encode,
          List.drop_succ_cons,List.drop_zero,List.headI_cons,Nat.add_assoc]
          using data_address N M k V u v d a 2 acc data
  simp only [localEdge,Expr.eval_or,Expr.eval_edge,Expr.eval_cond,hL,hR,hE]
  simp only [privateBase,Expr.eval_add,Expr.eval_mul,Expr.eval_const,Expr.eval_reg,
    queryState,RenderState.encode,List.drop_succ_cons,List.drop_zero,List.headI_cons]
  simp only [rawLocal,localAdj,endpoint]
  by_cases he : (data.drop (3*d+2)).headI=0 <;>
    simp only [he,ite_true,ite_false,bit_or]

lemma cumulative_query (N M k V u v n : ℕ) (acc data : List ℕ) :
    cumulative (queryState N M k V u v acc data).encode n=
      if ∃d<n,rawLocal N d data u v then 1 else 0 := by
  induction n with
  | zero => simp [cumulative,scalarRec]
  | succ n ih =>
    change (if cumulative (queryState N M k V u v acc data).encode n=0 then
      localEdge.eval (n::cumulative (queryState N M k V u v acc data).encode n::
        (queryState N M k V u v acc data).encode) else 1)=_
    rw [localEdge_query,ih,bit_or]
    congr 1
    apply propext
    constructor
    · rintro (⟨d,hd,h⟩|h)
      · exact ⟨d,by omega,h⟩
      · exact ⟨n,by omega,h⟩
    · rintro ⟨d,hd,h⟩
      by_cases he : d<n
      · exact Or.inl ⟨d,he,h⟩
      · have heq : d=n := by omega
        exact Or.inr (heq ▸ h)

def rawCell (N M : ℕ) (data : List ℕ) (u v : ℕ) : ℕ :=
  if ∃ d<M, rawLocal N d data u v then 1 else 0

def rawRow (N M : ℕ) (data : List ℕ) (u c : ℕ) : List ℕ :=
  (List.range c).map (rawCell N M data u)

def rawTable (N M : ℕ) (data : List ℕ) (r c : ℕ) : List ℕ :=
  (List.range r).flatMap (fun u=>rawRow N M data u c)

lemma tick_query (N M k V u v : ℕ) (acc data : List ℕ) :
    (queryState N M k V u v acc data).tick=
      queryState N M k V (if v=0 then u-1 else u) (if v=0 then V-1 else v-1)
        (rawCell N M data u v::acc) data := by
  simp only [RenderState.tick,cumulative_query]
  unfold queryState rawCell
  simp only [List.length_cons,List.cons_append]

lemma tick_row (N M k V r c : ℕ) (acc data : List ℕ) :
    RenderState.tick^[c+1] (queryState N M k V r c acc data)=
      queryState N M k V (r-1) (V-1) (rawRow N M data r (c+1)++acc) data := by
  induction c generalizing acc with
  | zero =>
    simp only [Nat.zero_add,Function.iterate_one,tick_query]
    simp [rawRow]
  | succ c ih =>
    rw [Function.iterate_succ_apply,tick_query]
    simp only [Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel]
    rw [ih]
    simp only [rawRow,List.range_succ,List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.cons_append,List.nil_append]

lemma tick_rows (N M k V r : ℕ) (hV : 0<V) (acc data : List ℕ) :
    RenderState.tick^[(r+1)*V] (queryState N M k V r (V-1) acc data)=
      queryState N M k V 0 (V-1) (rawTable N M data (r+1) V++acc) data := by
  have hV' : V-1+1=V := by omega
  have hrow (r : ℕ) (acc : List ℕ) :
      RenderState.tick^[V] (queryState N M k V r (V-1) acc data)=
        queryState N M k V (r-1) (V-1) (rawRow N M data r V++acc) data := by
    simpa only [hV'] using tick_row N M k V r (V-1) acc data
  induction r generalizing acc with
  | zero =>
    simpa only [Nat.zero_add,Nat.one_mul,Nat.zero_sub,rawTable,List.range_one,
      List.flatMap_cons,List.flatMap_nil,List.append_nil] using hrow 0 acc
  | succ r ih =>
    rw [show (r+1+1)*V=(r+1)*V+V by ring,Function.iterate_add_apply,hrow]
    simp only [Nat.add_sub_cancel]
    rw [ih]
    simp only [rawTable,List.range_succ,List.flatMap_append,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]

lemma tick_table (N M k V : ℕ) (acc data : List ℕ) :
    (RenderState.tick^[V^2] (queryState N M k V (V-1) (V-1) acc data)).tape=
      rawTable N M data V V++(acc++2::k::data) := by
  by_cases hV : V=0
  · subst V
    simp [rawTable,queryState]
  · have hp : 0<V := by omega
    have he : (V-1+1)*V=V^2 := by rw [Nat.sub_add_cancel hp]; ring
    rw [←he,tick_rows N M k V (V-1) hp,show V-1+1=V by omega]
    simp only [queryState,List.append_assoc]

end MinUncut.Costed.GraphRegisters

open scoped BigOperators
namespace MinUncut.PathRealization
open MinUncut.FiniteProof MinUncutGames.Foundations.Hastad.SourceOccurrences

def Demand.map {V W : Type*} (f : V → W) (d : Demand V) : Demand W :=
  ⟨f d.left,f d.right,d.equal⟩

lemma failure_map {V W : Type*} (f : V → W) (d : Demand V) (s : W → Bool) :
    failure (d.map f) s=failure d (s ∘ f) := rfl

def listFailure {V : Type*} (ds : List (Demand V)) (s : V → Bool) : ℕ :=
  (ds.map (fun d => failure d s)).sum

lemma listFailure_eq {V : Type*} (ds : List (Demand V)) (s : V → Bool) :
    listFailure ds s=totalFailure (fun i : Fin ds.length => ds[i]) s := by
  unfold listFailure totalFailure
  simp only [Fin.getElem_fin]
  rw [← List.sum_ofFn]
  exact (congrArg List.sum (List.ofFn_getElem_eq_map ds (fun d => failure d s))).symm

def demandList {V E : Type} (D : ℕ) (w : E → ℚ) (d : E → Demand V) (enc : Encoding E) : List (Demand V) :=
  enc.enumerate.flatMap (fun e => List.replicate (multiplicity D (w e)) (d e))

lemma sum_enumerate {E : Type} [Fintype E] (enc : Encoding E) (f : E → ℕ) :
    (enc.enumerate.map f).sum=∑e, f e := by
  simp only [Encoding.enumerate,List.map_ofFn,List.sum_ofFn]
  exact Equiv.sum_comp enc.code.symm f

lemma listFailure_demandList {E V : Type} [Fintype E] (D : ℕ) (w : E → ℚ)
    (d : E → Demand V) (enc : Encoding E) (s : V → Bool) :
    listFailure (demandList D w d enc) s=∑e, multiplicity D (w e)*failure (d e) s := by
  have h : ∀ es : List E,
      ((es.flatMap (fun e => List.replicate (multiplicity D (w e)) (d e))).map
        (fun d => failure d s)).sum =
        (es.map (fun e => multiplicity D (w e)*failure (d e) s)).sum := by
    intro es
    induction es with
    | nil => simp
    | cons e es ih =>
      simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_replicate,
        List.sum_replicate,nsmul_eq_mul,Nat.cast_id,List.map_cons,List.sum_cons,ih]
  unfold listFailure demandList
  rw [h]
  exact sum_enumerate enc _

lemma length_demandList {E V : Type} [Fintype E] (D : ℕ) (w : E → ℚ)
    (d : E → Demand V) (enc : Encoding E) :
    (demandList D w d enc).length=∑e, multiplicity D (w e) := by
  rw [demandList,List.length_flatMap]
  simp only [List.length_replicate]
  exact sum_enumerate enc _

noncomputable def extendAssignment {V W : Type*} (f : V → W) (s : V → Bool) (w : W) : Bool :=
  by
    classical
    exact if h : ∃ v, f v=w then s (Classical.choose h) else false

lemma extendAssignment_apply {V W : Type*} (f : V → W) (hf : Function.Injective f) (s : V → Bool) (v : V) :
    extendAssignment f s (f v)=s v := by
  rw [extendAssignment,dite_eq_left ⟨v,rfl⟩]
  exact congrArg s (hf (Classical.choose_spec (show ∃u, f u=f v from ⟨v,rfl⟩)))

lemma mapDemand_extend {V W : Type*} (f : V → W) (hf : Function.Injective f) (s : V → Bool) (d : Demand V) :
    failure (d.map f) (extendAssignment f s)=failure d s := by
  simp only [failure,Demand.map,extendAssignment_apply f hf]

end MinUncut.PathRealization

end OAI
