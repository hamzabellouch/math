import OAI.Analysis.CircleDomains.Modulus.RegularCurveNormalChart
import OAI.Analysis.CircleDomains.Topology.RegularCurveParameterIsolation

namespace OAI

/-! The local normal chart straightens the entire Jordan boundary, not
only the chosen parameter arc. Compact parameter isolation excludes other arcs. -/
open Set Function Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma exists_regular_jordan_boundary_chart
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ) (t : ℝ) :
    ∃ (e : OpenPartialHomeomorph (ℝ × ℝ) ℂ) (U : Set ℂ),
      (t,0) ∈ e.source ∧ (∀ p, e p = curveNormalStrip γ p) ∧
      ContDiff ℝ ∞ e ∧ ContDiffAt ℝ ∞ e.symm (γ t) ∧
      IsOpen U ∧ γ t ∈ U ∧ U ⊆ e.target ∧
      (∀ z ∈ U, z ∈ frontier (jordanInterior H) ↔ (e.symm z).2 = 0) := by
  obtain ⟨e,ht,he,hs,his⟩ := exists_regular_curve_normal_chart hγ.smooth t (hγ.regular t)
  have hopen : IsOpen {s : ℝ | (s,0) ∈ e.source} :=
    e.open_source.preimage (continuous_id.prodMk continuous_const)
  obtain ⟨δ,hδ,hδs⟩ := Metric.isOpen_iff.mp hopen t ht
  obtain ⟨ε,hε,hiso⟩ := hγ.local_parameter_isolation t hδ
  let U := ball (γ t) ε ∩ e.target
  have hval : e (t,0) = γ t := by simp [he,curveNormalStrip]
  refine ⟨e,U,ht,he,hs,his,isOpen_ball.inter e.open_target,
    ⟨mem_ball_self hε,hval ▸ e.map_source ht⟩,inter_subset_right,?_⟩
  intro z hz
  constructor
  · intro hzf
    obtain ⟨s,_,hes⟩ := hγ.boundary.symm ▸ hzf
    have hdist : dist (γ s) (γ t) < ε := hes.symm ▸ hz.1
    obtain ⟨u,hu,hue⟩ := hiso s hdist
    have huS : (u,0) ∈ e.source := hδs (by
      rw [mem_ball,Real.dist_eq]
      exact abs_sub_lt_iff.mpr ⟨by linarith [hu.2],by linarith [hu.1]⟩)
    have hue' : e (u,0) = z := by simpa [he,curveNormalStrip] using hue.trans hes
    have hinv := e.left_inv huS
    rw [hue'] at hinv
    exact congrArg Prod.snd hinv
  · intro hz0
    have hinv := e.right_inv hz.2
    have hpair : e.symm z = ((e.symm z).1,0) := Prod.ext rfl hz0
    rw [hpair,he] at hinv
    have hzγ : γ (e.symm z).1 = z := by
      simpa only [curveNormalStrip,zero_smul,add_zero] using hinv
    rw [← hzγ]
    exact hγ.mem_frontier _

end CircleDomainRigidity

end

end OAI
