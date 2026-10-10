import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCompactSubsequence
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.UniformApproximation

namespace OAI

/-! Compactness preserves uniform limits under maps continuous at the limiting data. -/

open Filter
namespace DefocusingNLS

theorem radial_compact_transform_limit {K E F : Type*}
    [MetricSpace K] [CompactSpace K] [MetricSpace E] [MetricSpace F]
    (f : ℕ → K → E) (g : K → E) (hg : Continuous g)
    (hf : TendstoUniformly f g atTop) (T : K × E → F)
    (hT : ∀ x, ContinuousAt T (x,g x)) :
    TendstoUniformly (fun n x => T (x,f n x)) (fun x => T (x,g x)) atTop := by
  classical
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  by_contra h
  obtain ⟨s,hs,x,x₀,hx,hbad⟩ := radial_compact_bad_subsequence
    (fun n x => dist (T (x,g x)) (T (x,f n x)) < ε) h
  have hsub : TendstoUniformly (fun i => f (s i)) g atTop :=
    fun u hu => hs.tendsto_atTop.eventually (hf u hu)
  have hdata := hsub.tendsto_comp hg.continuousAt hx
  have hactual := (hT x₀).tendsto.comp (hx.prodMk_nhds hdata)
  have href := (hT x₀).tendsto.comp (hx.prodMk_nhds (hg.continuousAt.tendsto.comp hx))
  have hd : Tendsto (fun i => dist (T (x i,g (x i))) (T (x i,f (s i) (x i)))) atTop
      (nhds 0) := by
    simpa only [dist_self] using! href.dist hactual
  obtain ⟨i,hi⟩ := (hd.eventually (gt_mem_nhds hε)).exists
  exact hbad i hi

end DefocusingNLS

end OAI
