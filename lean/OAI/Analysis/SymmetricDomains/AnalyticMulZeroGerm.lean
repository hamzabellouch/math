import Mathlib
import OAI.Analysis.SymmetricDomains.DifferentialMemSpanTranscendence

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Metric
open scoped Topology

theorem meromorphicAt_of_power_bound {f : ℂ → ℂ} {r C : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (ball 0 r \ {0})) (M : ℕ)
    (hbound : ∀ z ∈ ball 0 r \ {0}, ‖z^M * f z‖ ≤ C) :
    MeromorphicAt f 0 := by
  obtain ⟨g,hg,heq,_⟩ := bounded_removable_finite isOpen_ball (finite_singleton 0)
    (fun z => z^M * f z) ((analyticOnNhd_id.pow M).mul hf).differentiableOn hbound
  have hmer := (hg 0 (mem_ball_self hr)).meromorphicAt.div
    ((analyticAt_id (𝕜 := ℂ) (z := (0 : ℂ))).pow M).meromorphicAt
  apply hmer.congr
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hr))] with z hz hzball
  change g z / z^M = f z
  rw [heq z ⟨hzball,hz⟩]
  exact mul_div_cancel_left₀ (f z) (pow_ne_zero M hz)

end

section
open Set Algebra KaehlerDifferential Module

theorem differential_span_rank_eq_trdeg
    {R K κ : Type} [Field R] [CharZero R] [Field K] [Algebra R K]
    (q : κ → K) :
    Module.rank K (Submodule.span K (range (fun j => D R K (q j)))) =
      Algebra.trdeg R (IntermediateField.adjoin R (range q)) := by
  let L := IntermediateField.adjoin R (range q)
  obtain ⟨t,ht⟩ := exists_isTranscendenceBasis R L
  let x : t → K := fun i => i.val.val
  have hx : AlgebraicIndependent R x := ht.1.map' (f := L.val) Subtype.val_injective
  have hlin := algebraicIndependent_differentials x hx
  have hspan : Submodule.span K (range (fun j => D R K (q j))) =
      Submodule.span K (range (fun i => D R K (x i))) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      let y : L := ⟨q j,IntermediateField.subset_adjoin _ _ (mem_range_self j)⟩
      exact differential_mem_span_transcendenceBasis (K := K) (fun i : t => i.val) ht y
    · apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact differential_mem_span_adjoin q i.val.property
  rw [hspan,rank_span hlin]
  calc
    Cardinal.mk (range (fun i => D R K (x i))) = Cardinal.mk t := by
      simpa only [Cardinal.lift_id] using Cardinal.mk_range_eq_of_injective hlin.injective
    _ = _ := ht.cardinalMk_eq_trdeg

end

open Set Filter Topology

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

def analyticGermRing : Subring (Filter.Germ (𝓝 (0 : E)) ℂ) where
  carrier := {g | ∃ f : E → ℂ, AnalyticAt ℂ f 0 ∧ (f : Filter.Germ (𝓝 (0 : E)) ℂ) = g}
  zero_mem' := ⟨0, analyticAt_const, rfl⟩
  one_mem' := ⟨1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f,hf,rfl⟩ ⟨g,hg,rfl⟩
    exact ⟨f+g, hf.add hg, rfl⟩
  neg_mem' := by
    rintro _ ⟨f,hf,rfl⟩
    exact ⟨-f,hf.neg,rfl⟩
  mul_mem' := by
    rintro _ _ ⟨f,hf,rfl⟩ ⟨g,hg,rfl⟩
    exact ⟨f*g,hf.mul hg,rfl⟩

abbrev AnalyticGerm := analyticGermRing E

noncomputable def analyticGermConst : ℂ →+* AnalyticGerm E where
  toFun c := ⟨Filter.Germ.const c,⟨fun _ => c,analyticAt_const,rfl⟩⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

noncomputable instance : Algebra ℂ (AnalyticGerm E) :=
  (analyticGermConst E).toAlgebra

instance : Nontrivial (AnalyticGerm E) := by
  exact ⟨⟨0,1,fun h => zero_ne_one (congrArg Subtype.val h)⟩⟩

theorem analyticAt_mul_eq_zero_germ {f g : E → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hfg : f*g =ᶠ[𝓝 (0 : E)] 0) :
    f =ᶠ[𝓝 (0 : E)] 0 ∨ g =ᶠ[𝓝 (0 : E)] 0 := by
  classical
  by_cases h : f =ᶠ[𝓝 (0 : E)] 0
  · exact Or.inl h
  right
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp
    (hf.eventually_analyticAt.and (hg.eventually_analyticAt.and hfg))
  have hfball : AnalyticOnNhd ℂ f (Metric.ball 0 r) := fun z hz => (hball hz).1
  have hgball : AnalyticOnNhd ℂ g (Metric.ball 0 r) := fun z hz => (hball hz).2.1
  have hex : ∃ z ∈ Metric.ball (0 : E) r, f z ≠ 0 := by
    by_contra hn
    push Not at hn
    exact h (Filter.eventually_of_mem (Metric.ball_mem_nhds _ hr) hn)
  obtain ⟨z,hz,hfz⟩ := hex
  have hgn : g =ᶠ[𝓝 z] 0 := by
    filter_upwards [(hfball z hz).continuousAt.eventually_ne hfz,
      Metric.isOpen_ball.mem_nhds hz] with w hw hwball
    exact (mul_eq_zero.mp (hball hwball).2.2).resolve_left hw
  have hgzero := hgball.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0 : E) r).isPreconnected hz hgn
  exact Filter.eventually_of_mem (Metric.ball_mem_nhds _ hr) hgzero

instance : NoZeroDivisors (AnalyticGerm E) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    rintro ⟨a,f,hf,rfl⟩ ⟨b,g,hg,rfl⟩ hab
    have hfg : f*g =ᶠ[𝓝 (0 : E)] 0 := Filter.Germ.coe_eq.mp (congrArg Subtype.val hab)
    rcases analyticAt_mul_eq_zero_germ E hf hg hfg with h | h
    · exact Or.inl (Subtype.ext (Filter.Germ.coe_eq.mpr h))
    · exact Or.inr (Subtype.ext (Filter.Germ.coe_eq.mpr h))

end Release061

end

end OAI
