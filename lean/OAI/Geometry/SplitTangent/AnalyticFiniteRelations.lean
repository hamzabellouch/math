import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing

namespace OAI

/-! Analytic Finite Relations. -/

noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace AnalyticFiniteRelations
variable {A B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] {n : ℕ}

lemma analyticAt_det {v : B → Matrix (Fin n) (Fin n) ℂ} {b : B}
    (h : ∀i j,AnalyticAt ℂ (fun t => v t i j) b) :
    AnalyticAt ℂ (fun t => Matrix.det (v t)) b := by
  classical
  simp only [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ hσ
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_prod
  intro i hi
  exact h _ _

def locus (v : A → B → Fin n → ℂ) : Set B :=
  {b | ∃c : Fin n → ℂ,c≠0 ∧ ∀a,∑i,v a b i*c i=0}

omit [NormedAddCommGroup B] [NormedSpace ℂ B] in
lemma locus_iff (v : A → B → Fin n → ℂ) (b : B) :
    b∈locus v ↔ ∀s : Fin n → A,Matrix.det (fun i j => v (s i) b j)=0 :=
  FiniteSampling.relation_iff_det_zero _

lemma closure_interior_subset (v : A → B → Fin n → ℂ) {V : Set B}
    (hV : IsOpen V) (hv : ∀a i,AnalyticOnNhd ℂ (fun b => v a b i) V) :
    closure (interior (locus v)) ∩ V ⊆ interior (locus v) := by
  intro b hb
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hb.2)
  obtain ⟨c,hc,hcr⟩ := ((mem_closure_iff_frequently.mp hb.1).and_eventually
    (Metric.ball_mem_nhds b hr)).exists
  have hdet (s : Fin n → A) :
      AnalyticOnNhd ℂ (fun t => Matrix.det (fun i j => v (s i) t j)) (Metric.ball b r) := by
    intro t ht
    exact analyticAt_det (fun i j => hv (s i) j t (hrV ht))
  have hz (s : Fin n → A) :
      (fun t => Matrix.det (fun i j => v (s i) t j)) =ᶠ[𝓝 c] 0 := by
    filter_upwards [isOpen_interior.mem_nhds hc] with t ht
    exact (locus_iff v t).mp (interior_subset ht) s
  have he (s : Fin n → A) := (hdet s).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball b r).isPreconnected hcr (hz s)
  rw [mem_interior_iff_mem_nhds]
  apply Filter.mem_of_superset (Metric.ball_mem_nhds b hr)
  intro t ht
  exact (locus_iff v t).mpr (fun s => he s ht)

lemma eventually_not_mem (v : A → B → Fin n → ℂ) {V : Set B}
    (hV : IsOpen V) (hv : ∀a i,AnalyticOnNhd ℂ (fun b => v a b i) V)
    {b : B} (hb : b∈V) (hn : b∉locus v) : ∀ᶠt in 𝓝 b,t∉locus v := by
  rw [locus_iff] at hn
  push Not at hn
  obtain ⟨s,hs⟩ := hn
  have hc := (analyticAt_det (fun i j => hv (s i) j b hb)).continuousAt
  filter_upwards [hV.mem_nhds hb, hc.eventually_ne hs] with t _ ht
  exact fun hm => ht ((locus_iff v t).mp hm s)

end AnalyticFiniteRelations

end

end OAI
