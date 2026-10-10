import Mathlib
import OAI.Combinatorics.UniformKServer.MarkovFlow
import OAI.Combinatorics.UniformKServer.LawSupport
import OAI.Combinatorics.UniformKServer.LazyFinance

namespace OAI

noncomputable section

/-! Strongly-lazy metric serving from finite private virtual states. The exact
old and new marginals, legal actions, and potential charge are all explicit. -/
namespace UniformKServer.LazyMarkov
open Finset FiniteProbability
open scoped Classical
variable {X V : Type*} [Fintype X] [MetricSpace X] [Fintype V] {k : ℕ}

structure Input (X V : Type*) [Fintype V] (k : ℕ) where
  kernel : List X→X→V→Law V
  location : List X→V→Fin k→X

namespace Input
variable (D : Input X V k) (hk : 0<k)

def model : MarkovFlow.Model X (Fin k→X) (Fin k) V where
  kernel w r s := D.kernel w r s.1
  choice w r s v := LazyFinance.choice hk s.2 (D.location (w++[r]) v) r
  transition c r j := Function.update c j r

def potential (w : List X) (s : V×(Fin k→X)) : ℝ :=
  LazyFinance.mismatch s.2 (D.location w s.1)

def transport (P : Law V) (w : List X) (r : X) : ℝ :=
  P.expect (fun v=>(D.kernel w r v).expect (fun v'=>
    LazyFinance.mismatch (D.location w v) (D.location (w++[r]) v')))

def charge (Q : Law (V×(Fin k→X))) (w : List X) (r : X) : ℝ :=
  ∑ c,∑ j,((D.model hk).actions Q w r).weight (c,j)*dist (c j) r

omit [MetricSpace X] in
theorem marginal_next (Q : Law (V×(Fin k→X))) (w : List X) (r : X) :
    ((D.model hk).advance Q w r).map Prod.fst=(Q.map Prod.fst).bind (D.kernel w r) := by
  apply Law.ext_expect
  intro f
  simp only [MarkovFlow.Model.advance,MarkovFlow.Model.joint,Law.expect_map,Law.expect_bind,
    MarkovFlow.Model.successor,model,Function.comp_def]

omit [Fintype X] [MetricSpace X] in
theorem legal (w : List X) (r : X) (s : V×(Fin k→X)) (v : V)
    (h : ∃ i,s.2 i=r) : s.2 ((D.model hk).choice w r s v)=r :=
  LazyFinance.lazy hk _ _ _ h

theorem step (Q : Law (V×(Fin k→X))) (w : List X) (r : X)
    (hcover : ∀ v v',0<(Q.map Prod.fst).weight v → 0<(D.kernel w r v).weight v' →
      ∃ i,D.location (w++[r]) v' i=r) :
    D.charge hk Q w r+((D.model hk).advance Q w r).expect (D.potential (w++[r])) ≤
      Q.expect (D.potential w)+D.transport (Q.map Prod.fst) w r := by
  have hs (s : V×(Fin k→X)) (hpos : 0<Q.weight s) :
      (D.kernel w r s.1).expect (fun v=>
        dist (s.2 (LazyFinance.choice hk s.2 (D.location (w++[r]) v) r)) r+
          LazyFinance.mismatch (Function.update s.2 (LazyFinance.choice hk s.2 (D.location (w++[r]) v) r) r)
            (D.location (w++[r]) v)) ≤
      D.potential w s+(D.kernel w r s.1).expect (fun v=>
        LazyFinance.mismatch (D.location w s.1) (D.location (w++[r]) v)) := by
    have hp : 0<(Q.map Prod.fst).weight s.1 := lt_of_lt_of_le hpos (Q.weight_le_map Prod.fst s)
    have hb := (D.kernel w r s.1).expect_mono_support _ _ (fun v hv=>
      LazyFinance.step hk s.2 (D.location w s.1) (D.location (w++[r]) v) r (hcover s.1 v hp hv))
    simpa only [Law.expect_add,Law.expect_const,potential] using hb
  have hh := Q.expect_mono_support _ _ hs
  rw [Law.expect_add] at hh
  have he : Q.expect (fun s=>(D.kernel w r s.1).expect (fun v=>
      LazyFinance.mismatch (D.location w s.1) (D.location (w++[r]) v)))=
      D.transport (Q.map Prod.fst) w r := by
    rw [transport,Law.expect_map]
    rfl
  rw [he] at hh
  have hc := (D.model hk).action_cost Q w r (fun c j=>dist (c j) r)
  change D.charge hk Q w r=_ at hc
  rw [hc,MarkovFlow.Model.advance,Law.expect_map,←Law.expect_add]
  simpa only [MarkovFlow.Model.joint,Law.expect_bind,Law.expect_map,
    MarkovFlow.Model.successor,model,Function.comp_def,potential] using hh

omit [MetricSpace X] in
theorem initial_marginal (P : Law V) (s : Fin k→X) :
    (P.map (fun v=>(v,s))).map Prod.snd=Law.pure s := by
  apply Law.ext_expect
  intro f
  simp only [Law.expect_map,Function.comp_def,Law.expect_const,Law.expect_pure]

theorem initial_potential (P : Law V) (s : Fin k→X) (Δ : ℝ)
    (hdiam : ∀ x y : X,dist x y≤Δ) :
    (P.map (fun v=>(v,s))).expect (D.potential [])≤k*Δ := by
  rw [Law.expect_map]
  exact (P.expect_mono _ _ (fun v=>LazyFinance.initial_bound s _ Δ hdiam)).trans_eq (P.expect_const _)

end Input
end UniformKServer.LazyMarkov

end

end OAI
