import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothLocalSection

namespace OAI

/-! # A local homeomorphism from an invertible manifold derivative -/

noncomputable section
namespace PolycyclicRecognition
open Set
open scoped Manifold ContDiff

variable {V E M : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]

theorem exists_manifold_local_parameter {P : V → M} {x₀ : V} {d : V ≃L[ℝ] E}
    (hP : ContMDiff (𝓘(ℝ,V)) (𝓘(ℝ,E)) ∞ P)
    (hd : HasMFDerivAt (𝓘(ℝ,V)) (𝓘(ℝ,E)) P x₀ d.toContinuousLinearMap) :
    ∃ p : OpenPartialHomeomorph V M, x₀ ∈ p.source ∧ p x₀ = P x₀ ∧
      ∀ x ∈ p.source, p x = P x := by
  let c := chartAt E (P x₀)
  let Q : V → E := c ∘ P
  have hc : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ c (P x₀) := by
    change ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ (extChartAt (𝓘(ℝ,E)) (P x₀)) (P x₀)
    exact contMDiffAt_extChartAt
  have hQ : ContDiffAt ℝ ∞ Q x₀ := (hc.comp x₀ hP.contMDiffAt).contDiffAt
  have hcder : HasMFDerivAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) c (P x₀)
      (ContinuousLinearMap.id ℝ E) := by
    apply hc.mdifferentiableAt (by simp) |>.hasMFDerivAt |>.congr_mfderiv
    change mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (extChartAt (𝓘(ℝ,E)) (P x₀)) (P x₀) = _
    rw [mfderiv_extChartAt_self]
    rfl
  have hQd : HasFDerivAt Q d.toContinuousLinearMap x₀ := by
    have hh : HasFDerivAt Q ((ContinuousLinearMap.id ℝ E).comp d.toContinuousLinearMap) x₀ :=
      (hcder.comp x₀ hd).hasFDerivAt
    simpa only [ContinuousLinearMap.id_comp] using hh
  let q := hQ.toOpenPartialHomeomorph Q hQd (by simp)
  let u := {x | P x ∈ c.source}
  have hu : IsOpen u := c.open_source.preimage hP.continuous
  let r := q.restr u
  let p := r.trans c.symm
  have hpP (x : V) (hx : x ∈ p.source) : p x = P x := by
    have hxr : x ∈ (q.restr u).source := hx.1
    rw [q.restr_source' u hu] at hxr
    exact c.left_inv hxr.2
  have hx : x₀ ∈ p.source := by
    refine ⟨?_, ?_⟩
    · change x₀ ∈ (q.restr u).source
      rw [q.restr_source' u hu]
      exact ⟨hQ.mem_toOpenPartialHomeomorph_source hQd (by simp), mem_chart_source E (P x₀)⟩
    · exact c.map_source (mem_chart_source E (P x₀))
  exact ⟨p,hx,hpP x₀ hx,hpP⟩

end PolycyclicRecognition

end

end OAI
