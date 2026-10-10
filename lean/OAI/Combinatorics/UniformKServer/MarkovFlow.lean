import Mathlib
import OAI.Combinatorics.UniformKServer.LawKernel
import OAI.Combinatorics.UniformKServer.RealFlow

namespace OAI

noncomputable section

/-! Eliminate a finite private state by its exact configuration/action flows.
No private state or future observation is exposed in the resulting rows. -/
namespace UniformKServer.MarkovFlow
open Finset FiniteProbability
open scoped Classical
variable {R C J V : Type*} [Fintype C] [Fintype V]

structure Model (R C J V : Type*) [Fintype V] where
  kernel : List R→R→V×C→Law V
  choice : List R→R→V×C→V→J
  transition : C→R→J→C

namespace Model
variable (M : Model R C J V)

def successor (w : List R) (r : R) (q : (V×C)×V) : V×C :=
  (q.2,M.transition q.1.2 r (M.choice w r q.1 q.2))

def joint (P : Law (V×C)) (w : List R) (r : R) : Law ((V×C)×V) :=
  P.bind (fun s=>(M.kernel w r s).map (fun v=>(s,v)))

def advance (P : Law (V×C)) (w : List R) (r : R) : Law (V×C) :=
  (M.joint P w r).map (M.successor w r)

def evolve : List R→Law (V×C)→List R→Law (V×C)
  | _,P,[] => P
  | w,P,r::rs => evolve (w++[r]) (M.advance P w r) rs

def process (P : Law (V×C)) (w : List R) : Law (V×C) := M.evolve [] P w

theorem evolve_append (w u v : List R) (P : Law (V×C)) :
    M.evolve w P (u++v)=M.evolve (w++u) (M.evolve w P u) v := by
  induction u generalizing w P with
  | nil => simp [evolve]
  | cons r rs ih =>
    simpa only [evolve,List.cons_append,List.append_assoc,List.singleton_append,List.nil_append] using
      (ih (w++[r]) (M.advance P w r))

theorem process_snoc (P : Law (V×C)) (w : List R) (r : R) :
    M.process P (w++[r])=M.advance (M.process P w) w r := by
  rw [process,M.evolve_append]
  rfl

theorem joint_first (P : Law (V×C)) (w : List R) (r : R) (f : V×C→ℝ) :
    (M.joint P w r).expect (f ∘ Prod.fst)=P.expect f := by
  simp only [joint,Law.expect_bind,Law.expect_map,Function.comp_def]
  simp only [Law.expect_const]

theorem advance_expect (P : Law (V×C)) (w : List R) (r : R) (f : V×C→ℝ) :
    (M.advance P w r).expect f=(M.joint P w r).expect (f ∘ M.successor w r) :=
  Law.expect_map _ _ _

variable [Fintype J]

def actions (P : Law (V×C)) (w : List R) (r : R) : Law (C×J) :=
  (M.joint P w r).map (fun q=>(q.1.2,M.choice w r q.1 q.2))

def flow (P : Law (V×C)) : RealFlow.Data R C J where
  mass w c := ((M.process P w).map Prod.snd).weight c
  flow w r c j := (M.actions (M.process P w) w r).weight (c,j)

theorem sum_row (P : Law (V×C)) (w : List R) (r : R) (c : C) :
    ∑ j,(M.actions P w r).weight (c,j)=(P.map Prod.snd).weight c := by
  have h₁ : (∑ j,(M.actions P w r).weight (c,j))=
      (M.actions P w r).expect (fun cj=>if cj.1=c then 1 else 0) := by
    simp only [Law.expect,Fintype.sum_prod_type,mul_ite,mul_one,mul_zero]
    rw [sum_comm]
    simp only [sum_ite_eq',mem_univ,ite_true]
  rw [h₁,actions,Law.expect_map]
  change (M.joint P w r).expect ((fun s : V×C=>if s.2=c then 1 else 0) ∘ Prod.fst)=_
  rw [M.joint_first]
  simp only [Law.expect,Law.map,mul_ite,mul_one,mul_zero]

theorem action_cost (P : Law (V×C)) (w : List R) (r : R) (d : C→J→ℝ) :
    (∑ c,∑ j,(M.actions P w r).weight (c,j)*d c j)=
      (M.joint P w r).expect (fun q=>d q.1.2 (M.choice w r q.1 q.2)) := by
  have h := (M.joint P w r).expect_map (fun q=>(q.1.2,M.choice w r q.1 q.2)) (fun cj=>d cj.1 cj.2)
  simpa only [Law.expect,Fintype.sum_prod_type,actions,Function.comp_def] using h

theorem sum_inflow (P : Law (V×C)) (w : List R) (r : R) (c' : C) :
    (∑ c,∑ j,if M.transition c r j=c' then (M.actions P w r).weight (c,j) else 0)=
      ((M.advance P w r).map Prod.snd).weight c' := by
  have ha := M.action_cost P w r (fun c j=>if M.transition c r j=c' then 1 else 0)
  simp only [mul_ite,mul_one,mul_zero] at ha
  rw [ha]
  have hn := (M.advance P w r).expect_map Prod.snd (fun c=>if c=c' then 1 else 0)
  have he := M.advance_expect P w r (fun s=>if s.2=c' then 1 else 0)
  have hz : ((M.advance P w r).map Prod.snd).expect (fun c=>if c=c' then 1 else 0)=
      ((M.advance P w r).map Prod.snd).weight c' := by simp [Law.expect]
  rw [hz] at hn
  exact (he.symm.trans hn.symm)

theorem action_support (P : Law (V×C)) (w : List R) (r : R)
    (allowed : C→R→J→Prop) (hc : ∀ s v,allowed s.2 r (M.choice w r s v))
    (c : C) (j : J) (hj : ¬allowed c r j) : (M.actions P w r).weight (c,j)=0 := by
  unfold actions Law.map
  apply sum_eq_zero
  intro q _
  split_ifs with he
  · have h₁ : q.1.2=c := congrArg Prod.fst he
    have h₂ : M.choice w r q.1 q.2=j := congrArg Prod.snd he
    have hh := hc q.1 q.2
    rw [h₁,h₂] at hh
    exact (hj hh).elim
  · rfl

theorem valid (P : Law (V×C)) (c₀ : C) (H : ℕ) (allowed : C→R→J→Prop)
    (hinit : P.map Prod.snd=Law.pure c₀)
    (hc : ∀ w r s v,allowed s.2 r (M.choice w r s v)) :
    RealFlow.Valid (M.flow P) M.transition allowed c₀ H := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro w _ c; exact ((M.process P w).map Prod.snd).nonneg c
  · intro w _; exact ((M.process P w).map Prod.snd).total
  · intro c
    change (P.map Prod.snd).weight c=_
    rw [hinit]
    rfl
  · intro w _ r c j; exact (M.actions (M.process P w) w r).nonneg (c,j)
  · intro w _ r c j hj; exact M.action_support _ _ _ allowed (hc w r) c j hj
  · intro w _ r c; exact M.sum_row _ _ _ c
  · intro w _ r c'
    change _=((M.process P (w++[r])).map Prod.snd).weight c'
    rw [M.process_snoc]
    exact M.sum_inflow _ _ _ c'

end Model
end UniformKServer.MarkovFlow

end

end OAI
