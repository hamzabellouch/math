import Mathlib
import OAI.Computability.MinUncut.Estimates.UniformEquationOutput

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Costed.SourceWords
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncut.PathRealization MinUncut.FiniteProof MinUncutGames.Reduction MinUncut.SourceBridge
open MinUncutGames.Foundations.Hastad.SourceOccurrences
attribute [local instance] Classical.propDecidable
variable {J : ℕ} (P : Parameters J) (input : SourceEncoding.Input)
  [Nonempty (Fin input.equations.length)]
  (E : Enumeration (Index (Fin P.o.t) P.o.k P.d.m P.d.n P.grid))

def generatedGraph : MinUncut.Output :=
  listOutput (generatedDemands input E (rationalRate J P.d) (rationalBudgets J P.d P.o)
    (rationalSigma J) (rationalEta J)) (5*P.denominator (Fin input.equations.length))
    (threshold_positive P.denominator_pos)

lemma generatedGraph_yes (s : Fin input.«variables» → F₂)
    (hs : (P.o.t:ℝ)*(1-equationFraction (equations input) s)≤P.o.b4) :
    (generatedGraph P input E).opt≤(generatedGraph P input E).threshold := by
  let y := (honestProof (I:=Fin P.o.t) s).assignment
  have hy : ∑e,(P.weight (equations input) e:ℝ)*(failure (P.demand (equations input) e) y:ℝ)≤9/2 := by
    rw [P.failure_eq,ProofFamily.variableProof_assignment]
    exact (finite_honest_cost P.hJ P.d P.hd P.o P.ho (equations input) s (Fintype.card_fin _) hs).le
  apply listOutput_yes _ _ _ (extendAssignment variableCode y)
  rw [generated_failure_eq]
  have hh := listFailure_weight (P.denominator (Fin input.equations.length)) (P.weight (equations input))
    (P.weight_nonneg _) (P.weight_den _) (P.demand (equations input))
    (SampleEnumeration.all (equations input) P.o.k P.d.m P.d.n P.grid).encoding y
  have he : listFailure (P.canonicalDemands (equations input)) (extendAssignment variableCode y)=
      listFailure (demandList (P.denominator (Fin input.equations.length)) (P.weight (equations input))
        (P.demand (equations input))
        (SampleEnumeration.all (equations input) P.o.k P.d.m P.d.n P.grid).encoding) y :=
    listFailure_extend variableCode variableCode_injective _ y
  have hD : (0:ℝ)<P.denominator (Fin input.equations.length) := by exact_mod_cast P.denominator_pos
  have h : (listFailure (P.canonicalDemands (equations input)) (extendAssignment variableCode y):ℝ)≤
      5*P.denominator (Fin input.equations.length) := by
    rw [he,hh]
    have h' := mul_le_mul_of_nonneg_left (hy.trans (by norm_num : (9/2:ℝ)≤5)) hD.le
    simpa only [mul_comm] using h'
  exact_mod_cast h

lemma generatedGraph_no {K : ℕ} (hK : 2≤K) (hKJ : 8*K≤J)
    (hs : ∀ s : Fin input.«variables» → F₂,equationFraction (equations input) s≤3/4) :
    K*(generatedGraph P input E).threshold<(generatedGraph P input E).opt := by
  let : NeZero P.o.t := ⟨ne_of_gt P.t_pos⟩
  apply listOutput_no
  intro y
  rw [generated_failure_eq]
  have hh := P.canonicalGraph_failure (equations input) y
  have hK' : (2:ℝ)≤K := by exact_mod_cast hK
  have hJ' : 8*(K:ℝ)≤J := by exact_mod_cast hKJ
  have hD : (0:ℝ)<P.denominator (Fin input.equations.length) := by exact_mod_cast P.denominator_pos
  have hg : 5*(K:ℝ)<∑e,(P.weight (equations input) e:ℝ)*
      (failure (P.demand (equations input) e) (y ∘ variableCode):ℝ) := by
    rw [P.failure_eq]
    have h := finite_unsound_cost P.hJ P.d P.hd P.o P.ho (variableProof (y ∘ variableCode))
      (equations input) (Fintype.card_fin _) hs
    change (J:ℝ)-1/2 < (variableProof (y ∘ variableCode)).finiteCost _ _ P.grid (equations input) at h
    linarith
  have h : (K:ℝ)*(5*P.denominator (Fin input.equations.length))<
      (listFailure (P.canonicalDemands (equations input)) y:ℝ) := by
    rw [hh]
    have h' := mul_lt_mul_of_pos_left hg hD
    simpa only [mul_assoc,mul_comm,mul_left_comm] using h'
  exact_mod_cast h
end MinUncut.Costed.SourceWords

end
end
section
namespace MinUncut.Costed.Arena
open Turing.ToPartrec

def Extends (h h' : Heap) : Prop := ∃g,h'=g++h
lemma Extends.refl (h : Heap) : Extends h h := ⟨[],rfl⟩
lemma Extends.cons (h : Heap) (n : Node) : Extends h (n::h) := ⟨[n],rfl⟩
lemma Extends.trans {h h' h''} (he : Extends h h') (he' : Extends h' h'') : Extends h h'' := by
  obtain ⟨a,rfl⟩ := he
  obtain ⟨b,rfl⟩ := he'
  exact ⟨b++a,(List.append_assoc _ _ _).symm⟩
lemma Extends.length {h h'} (he : Extends h h') : h.length≤h'.length := by
  obtain ⟨a,rfl⟩ := he
  simp
lemma Extends.read {h h'} (he : Extends h h') (p : ℕ) (hp : p≤h.length) (j : Fin 4) :
    read h' p j=read h p j := by
  obtain ⟨a,rfl⟩ := he
  induction a with
  | nil => rfl
  | cons n a ih =>
    rw [List.cons_append,read_old (a++h) n p (by simp; omega),ih]
lemma ListRep.mono {h h' p v} (hv : ListRep h p v) (he : Extends h h') : ListRep h' p v := by
  obtain ⟨a,rfl⟩ := he
  exact hv.prepend a
lemma CodeAt.mono {h h' p c} (hc : CodeAt h p c) (he : Extends h h') : CodeAt h' p c := by
  obtain ⟨a,rfl⟩ := he
  exact hc.prepend a

def Trace (s s' : State) (n : ℕ) : Prop := State.tick^[n] s=s'
lemma Trace.refl (s : State) : Trace s s 0 := rfl
lemma Trace.one {s s'} (he : s.tick=s') : Trace s s' 1 := he
lemma Trace.trans {s s' s'' n m} (h : Trace s s' n) (h' : Trace s' s'' m) :
    Trace s s'' (n+m) := by
  unfold Trace at *
  rw [Nat.add_comm n m,Function.iterate_add_apply,h,h']

def Simulates (c : Code) (v w : List ℕ) (B : ℕ) : Prop :=
  ∀h pc env kont,CodeAt h pc c → ListRep h env v →
    ∃h' out n,n≤B ∧ Extends h h' ∧ ListRep h' out w ∧
      Trace ⟨0,pc,env,kont,h⟩ ⟨1,0,out,kont,h'⟩ n

lemma simulate_zero (v : List ℕ) : Simulates .zero' v (0::v) 1 := by
  intro h pc env k hc hv
  cases hc with
  | zero hp hb ht =>
    refine ⟨node 0 env 0 0::h,h.length+1,1,le_rfl,Extends.cons h _,hv.push 0,Trace.one ?_⟩
    simp only [State.tick,ht,ite_true]

lemma simulate_succ (v : List ℕ) : Simulates .succ v [v.headI+1] 1 := by
  intro h pc env k hc hv
  cases hc with
  | succ hp hb ht =>
    refine ⟨node (v.headI+1) 0 0 0::h,h.length+1,1,le_rfl,Extends.cons h _,ListRep.nil.push _,Trace.one ?_⟩
    simp only [State.tick,ht,ite_true,hv.head]

lemma simulate_tail (v : List ℕ) : Simulates .tail v v.tail 1 := by
  intro h pc env k hc hv
  cases hc with
  | tail hp hb ht =>
    refine ⟨h,read h env 1,1,le_rfl,Extends.refl h,hv.tail,Trace.one ?_⟩
    simp only [State.tick,ht,ite_true]

lemma simulate_comp {f g v u w A B} (hg : Simulates g v u A) (hf : Simulates f u w B) :
    Simulates (.comp f g) v w (A+B+2) := by
  intro h pc env k hc hv
  cases hc with
  | comp hp hb ht hcf hcg =>
    let frame := node 2 (read h pc 1) 0 k
    let h₁ := frame::h
    have hv₁ : ListRep h₁ env v := hv.extend frame
    have hc₁ := hcg.extend frame
    obtain ⟨h₂,out,n,hn,he,ho,htrace⟩ := hg h₁ (read h pc 2) env (h.length+1) hc₁ hv₁
    have hh : Extends h h₂ := (Extends.cons h frame).trans he
    have hr (j : Fin 4) : read h₂ (h.length+1) j=frame j := by
      rw [he.read _ (by simp [h₁]),read_new]
    have hs : Trace ⟨0,pc,env,k,h⟩ ⟨0,read h pc 2,env,h.length+1,h₁⟩ 1 := by
      apply Trace.one
      simp only [State.tick,ht,ite_true,h₁,frame]
    have hs' : Trace ⟨1,0,out,h.length+1,h₂⟩ ⟨0,read h pc 1,out,k,h₂⟩ 1 := by
      apply Trace.one
      simp only [State.tick,show (1:ℕ)≠0 by omega,ite_false,ite_true,
        show h.length+1≠0 by omega,hr,frame,node_zero,node_one,node_three]
    obtain ⟨h₃,out',m,hm,he',ho',htrace'⟩ := hf h₂ (read h pc 1) out k (hcf.mono hh) ho
    refine ⟨h₃,out',1+n+1+m,by omega,hh.trans he',ho',?_⟩
    exact ((hs.trans htrace).trans hs').trans htrace'

lemma simulate_caseZero {f g v w A} (hz : v.headI=0) (hf : Simulates f v.tail w A) :
    Simulates (.case f g) v w (A+1) := by
  intro h pc env k hc hv
  cases hc with
  | case hp hb ht hcf hcg =>
    obtain ⟨h',out,n,hn,he,ho,tr⟩ := hf h (read h pc 1) (read h env 1) k hcf hv.tail
    refine ⟨h',out,1+n,by omega,he,ho,(Trace.one ?_).trans tr⟩
    simp only [State.tick,ht,ite_true,hv.head,hz]

lemma simulate_caseSucc {f g v a w A} (hg : Simulates g (a::v) w A) :
    Simulates (.case f g) ((a+1)::v) w (A+1) := by
  intro h pc env k hc hv
  cases hc with
  | case hp hb ht hcf hcg =>
    let cell := node a (read h env 1) 0 0
    have hh := hv.tail.push a
    obtain ⟨h',out,n,hn,he,ho,tr⟩ := hg (cell::h) (read h pc 2) (h.length+1) k
      (hcg.extend cell) hh
    refine ⟨h',out,1+n,by omega,(Extends.cons h cell).trans he,ho,(Trace.one ?_).trans tr⟩
    simp only [State.tick,ht,ite_true,hv.head,List.headI_cons,show a+1≠0 by omega,ite_false,
      Nat.add_sub_cancel,cell]

end MinUncut.Costed.Arena

end

end OAI
