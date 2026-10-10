import Mathlib
import OAI.Combinatorics.UniformKServer.RoundingChain
import OAI.Combinatorics.UniformKServer.RoundingKernel
import OAI.Combinatorics.UniformKServer.LazyMarkov

namespace OAI

noncomputable section

/-! Causal rounded distributions are realized without exposing the hidden
trajectory. Only an observed request prefix selects the conditional rows. -/
namespace UniformKServer.TreeRounding
open Finset FiniteProbability
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X Ω : Type} [Fintype X] [MetricSpace X]

structure PublicInput (D : ChainInput S k X Ω) where
  default : Ω
  request : ℕ→Ω→X
  trace : ℕ→Ω→List X
  trace_zero : ∀ ω,trace 0 ω=[]
  trace_snoc : ∀ t ω,trace (t+1) ω=trace t ω++[request t ω]
  trace_length : ∀ t ω,(trace t ω).length=t
  reflects : ∀ t ω v,trace t ω=trace t v → (D.filtration t).r ω v

namespace PublicInput
variable {D : ChainInput S k X Ω} (O : PublicInput D)

def pick (w : List X) : Ω :=
  if h : ∃ ω,O.trace w.length ω=w then h.choose else O.default

omit [Fintype X] in
theorem pick_trace (t : ℕ) (ω : Ω) : O.trace t (O.pick (O.trace t ω))=O.trace t ω := by
  have he : ∃ v,O.trace (O.trace t ω).length v=O.trace t ω := ⟨ω,by rw [O.trace_length]⟩
  unfold pick
  rw [dite_eq_left he]
  simpa only [O.trace_length] using he.choose_spec

omit [Fintype X] in
theorem pick_related (t : ℕ) (ω : Ω) : (D.filtration t).r (O.pick (O.trace t ω)) ω :=
  O.reflects t _ _ (O.pick_trace t ω)

def input : LazyMarkov.Input X (State S k) k where
  kernel w r := D.kernel w.length (O.pick (w++[r]))
  location w s i := D.anchors w.length (O.pick w) (s.realization.tuple i)

omit [Fintype X] in
theorem kernel_trace (t : ℕ) (ω : Ω) :
    O.input.kernel (O.trace t ω) (O.request t ω)=D.kernel t ω := by
  change D.kernel (O.trace t ω).length (O.pick (O.trace t ω++[O.request t ω]))=_
  rw [O.trace_length,←O.trace_snoc]
  exact D.kernel_causal t _ _ (O.pick_related (t+1) ω)

omit [Fintype X] in
theorem location_trace (t : ℕ) (ω : Ω) :
    O.input.location (O.trace t ω)=fun s i=>D.anchors t ω (s.realization.tuple i) := by
  funext s i
  change D.anchors (O.trace t ω).length (O.pick (O.trace t ω)) _=_
  rw [O.trace_length,D.anchors_causal t _ _ (O.pick_related t ω)]

def initial (s : Fin k→X) : FiniteProbability.Law (State S k×(Fin k→X)) :=
  (D.distribution 0 O.default).law.map (fun v=>(v,s))

theorem initial_first (s : Fin k→X) (ω : Ω) :
    (O.initial s).map Prod.fst=(D.distribution 0 ω).law := by
  have hh : (D.filtration 0).r O.default ω := O.reflects 0 _ _ (by rw [O.trace_zero,O.trace_zero])
  rw [initial,Law.map_comp]
  change (D.distribution 0 O.default).law.map id=_
  rw [Law.map_id,D.distribution_causal 0 _ _ hh]

theorem process_marginal (hk : 0<k) (s : Fin k→X) (t : ℕ) (ω : Ω) :
    (((O.input.model hk).process (O.initial s) (O.trace t ω)).map Prod.fst)=
      (D.distribution t ω).law := by
  induction t with
  | zero => rw [O.trace_zero]; exact O.initial_first s ω
  | succ t ih =>
    rw [O.trace_snoc,MarkovFlow.Model.process_snoc,O.input.marginal_next hk,ih,O.kernel_trace,D.kernel_next]

def potential (hk : 0<k) (s : Fin k→X) (t : ℕ) (ω : Ω) : ℝ :=
  ((O.input.model hk).process (O.initial s) (O.trace t ω)).expect (O.input.potential (O.trace t ω))

def charge (hk : 0<k) (s : Fin k→X) (t : ℕ) (ω : Ω) : ℝ :=
  O.input.charge hk ((O.input.model hk).process (O.initial s) (O.trace t ω)) (O.trace t ω) (O.request t ω)

def transport (_O : PublicInput D) (t : ℕ) (ω : Ω) : ℝ :=
  (D.joint t ω).expect (fun st=>stateDistance (D.anchors t ω) (D.anchors (t+1) ω) st.1 st.2)

theorem step (hk : 0<k) (s : Fin k→X) (t : ℕ) (ω : Ω)
    (hcover : ∀ v : State S k,Rounded (D.allocation (t+1) ω) v.value →
      ∃ i,D.anchors (t+1) ω (v.realization.tuple i)=O.request t ω) :
    O.charge hk s t ω+O.potential hk s (t+1) ω≤O.potential hk s t ω+O.transport t ω := by
  let Q := (O.input.model hk).process (O.initial s) (O.trace t ω)
  have hh := O.input.step hk Q (O.trace t ω) (O.request t ω) (by
    intro v v' hv hv'
    rw [O.process_marginal hk s t ω] at hv
    rw [O.kernel_trace] at hv'
    rw [←O.trace_snoc,O.location_trace]
    exact hcover v' (D.kernel_rounded t ω v v' hv hv'))
  have hp : ((O.input.model hk).advance Q (O.trace t ω) (O.request t ω)).expect
      (O.input.potential (O.trace t ω++[O.request t ω]))=O.potential hk s (t+1) ω := by
    rw [potential,O.trace_snoc,MarkovFlow.Model.process_snoc]
  have ht : O.input.transport (Q.map Prod.fst) (O.trace t ω) (O.request t ω)=O.transport t ω := by
    unfold LazyMarkov.Input.transport
    rw [O.process_marginal hk s t ω,O.kernel_trace]
    simp_rw [O.location_trace t ω,←O.trace_snoc,O.location_trace (t+1) ω]
    rw [D.kernel_cost]
    rfl
  rw [hp,ht] at hh
  exact hh

theorem potential_nonneg (hk : 0<k) (s : Fin k→X) (t : ℕ) (ω : Ω) :
    0≤O.potential hk s t ω := by
  apply Law.expect_nonneg
  intro v
  exact LazyFinance.mismatch_nonneg _ _

theorem potential_initial (hk : 0<k) (s : Fin k→X) (ω : Ω) (Δ : ℝ)
    (hdiam : ∀ x y : X,dist x y≤Δ) : O.potential hk s 0 ω≤k*Δ := by
  rw [potential,O.trace_zero]
  exact O.input.initial_potential _ s Δ hdiam

theorem total_charge (hk : 0<k) (s : Fin k→X) (N : ℕ) (ω : Ω) (Δ : ℝ)
    (hdiam : ∀ x y : X,dist x y≤Δ)
    (hcover : ∀ t<N,∀ v : State S k,Rounded (D.allocation (t+1) ω) v.value →
      ∃ i,D.anchors (t+1) ω (v.realization.tuple i)=O.request t ω) :
    (∑ t∈range N,O.charge hk s t ω)≤(∑ t∈range N,O.transport t ω)+k*Δ := by
  have hh : (∑ t∈range N,O.charge hk s t ω)+O.potential hk s N ω≤
      (∑ t∈range N,O.transport t ω)+O.potential hk s 0 ω := by
    induction N with
    | zero => simp
    | succ N ih =>
      have hh := ih (fun t ht=>hcover t (by omega))
      have hs := O.step hk s N ω (hcover N (by omega))
      simp only [sum_range_succ]
      linarith
  have h₀ := O.potential_initial hk s ω Δ hdiam
  have hn := O.potential_nonneg hk s N ω
  linarith

end PublicInput
end UniformKServer.TreeRounding

end

end OAI
