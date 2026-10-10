import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

open Set Filter Metric
open scoped Topology
namespace SymmetricMahler

/-- Compactness supplies a single positive bound, and uniform convergence
preserves half of it simultaneously at every point. -/
theorem eventually_uniform_pos {X I : Type*} [TopologicalSpace X]
    {K : Set X} {l : Filter I} {u : I → X → ℝ} {t : X → ℝ}
    (hK : IsCompact K) (ht : ContinuousOn t K)
    (hp : ∀ x ∈ K, 0 < t x) (hu : TendstoUniformlyOn u t l K) :
    ∃ c : ℝ, 0 < c ∧ (∀ x ∈ K, 2*c ≤ t x) ∧
      ∀ᶠ i in l, ∀ x ∈ K, c ≤ u i x := by
  by_cases hn : K.Nonempty
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hn ht
    refine ⟨t x / 2, by linarith [hp x hx], ?_, ?_⟩
    · intro y hy
      have hb : t x ≤ t y := hmin hy
      linarith
    · have hc : 0 < t x / 2 := by linarith [hp x hx]
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu (t x / 2) hc] with i hi
      intro y hy
      have hd := hi y hy
      rw [Real.dist_eq] at hd
      have ha := (abs_lt.mp hd).2
      have hb : t x ≤ t y := hmin hy
      linarith
  · refine ⟨1, by norm_num, ?_, Filter.Eventually.of_forall ?_⟩ <;>
      simp_all [Set.not_nonempty_iff_eq_empty]

/-- A continuous operation preserves uniform convergence when its inputs
converge uniformly to a continuous function on a compact set in a proper space. -/
theorem uniform_comp_of_compact {X I E H : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [ProperSpace E] [UniformSpace H]
    {K : Set X} {l : Filter I} {u : I → X → E} {t : X → E}
    (hK : IsCompact K) (ht : ContinuousOn t K)
    (hu : TendstoUniformlyOn u t l K) {g : E → H} (hg : Continuous g) :
    TendstoUniformlyOn (fun i x => g (u i x)) (fun x => g (t x)) l K := by
  obtain ⟨R, hR⟩ := (hK.image_of_continuousOn ht).isBounded.subset_closedBall (0 : E)
  have hf : ∀ x ∈ K, t x ∈ closedBall (0 : E) (R+1) := by
    intro x hx
    exact closedBall_subset_closedBall (by linarith) (hR (mem_image_of_mem t hx))
  have he : ∀ᶠ i in l, ∀ x ∈ K, u i x ∈ closedBall (0 : E) (R+1) := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu 1 (by norm_num)] with i hi
    intro x hx
    have hb := hR (mem_image_of_mem t hx)
    have hd := hi x hx
    rw [mem_closedBall] at hb ⊢
    calc
      dist (u i x) 0 ≤ dist (u i x) (t x) + dist (t x) 0 := dist_triangle _ _ _
      _ ≤ R + 1 := by rw [dist_comm] at hd; linarith
  exact (isCompact_closedBall (0 : E) (R+1)).uniformContinuousOn_of_continuous hg.continuousOn
    |>.comp_tendstoUniformlyOn_eventually he hf hu

/-- Uniform convergence of a finite family, in its product norm. -/
theorem uniform_finite_pi {X I J V : Type*} [Fintype J] [PseudoMetricSpace V]
    {K : Set X} {l : Filter I} {u : I → J → X → V} {t : J → X → V}
    (h : ∀ j, TendstoUniformlyOn (fun i => u i j) (t j) l K) :
    TendstoUniformlyOn (fun i x j => u i j x) (fun x j => t j x) l K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have he : ∀ᶠ i in l, ∀ j, ∀ x ∈ K, dist (t j x) (u i j x) < ε :=
    (Filter.eventually_all).mpr (fun j => Metric.tendstoUniformlyOn_iff.mp (h j) ε hε)
  filter_upwards [he] with i hi
  intro x hx
  exact (dist_pi_lt_iff hε).mpr (fun j => hi j x hx)

/-- Same-parameter product version of uniform convergence. -/
theorem uniform_pair {X I V W : Type*} [UniformSpace V] [UniformSpace W]
    {K : Set X} {l : Filter I} {u : I → X → V} {v : I → X → W}
    {t : X → V} {s : X → W}
    (hu : TendstoUniformlyOn u t l K) (hv : TendstoUniformlyOn v s l K) :
    TendstoUniformlyOn (fun i x => (u i x, v i x)) (fun x => (t x, s x)) l K := by
  intro d hd
  exact ((hu.prodMk hv) d hd).diag_of_prod

end SymmetricMahler

end OAI
