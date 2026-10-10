import OAI.Geometry.EinsteinFour.FlowJointDifferentiability

namespace OAI

/-! Uniform local uniqueness for parameterized actual ODE solutions.
This identifies the existing flow with its variational lifts on a whole
neighborhood, as required for higher derivatives in the initial data. -/

namespace PositiveEinsteinFour.FlowCalculus

open Set Metric Filter
open scoped ContDiff Topology

noncomputable section

variable {P E : Type*} [NormedAddCommGroup P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem local_solution_family_eventuallyEq (f : E → E) (α β : P × ℝ → E)
    (p : P) (hαc : ContinuousAt α (p, 0)) (hβc : ContinuousAt β (p, 0))
    (hinit : ∀ᶠ q in 𝓝 p, α (q, 0) = β (q, 0))
    (hα : ∀ᶠ z in 𝓝 (p, (0 : ℝ)),
      HasDerivAt (fun t => α (z.1, t)) (f (α z)) z.2)
    (hβ : ∀ᶠ z in 𝓝 (p, (0 : ℝ)),
      HasDerivAt (fun t => β (z.1, t)) (f (β z)) z.2)
    (hf : ContDiffAt ℝ 1 f (α (p, 0))) : α =ᶠ[𝓝 (p, (0 : ℝ))] β := by
  obtain ⟨K, U, hU, hLip⟩ := hf.exists_lipschitzOnWith
  have hαU : ∀ᶠ z in 𝓝 (p, (0 : ℝ)), α z ∈ U := hαc.preimage_mem_nhds hU
  have hβU : ∀ᶠ z in 𝓝 (p, (0 : ℝ)), β z ∈ U :=
    hβc.preimage_mem_nhds (by simpa only [hinit.self_of_nhds] using hU)
  have hi : ∀ᶠ z in 𝓝 (p, (0 : ℝ)), α (z.1, 0) = β (z.1, 0) := by
    have ht : Tendsto (fun z : P × ℝ => z.1) (𝓝 (p, 0)) (𝓝 p) :=
      continuous_fst.continuousAt
    exact ht.eventually hinit
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp
    (hα.and (hβ.and (hαU.and (hβU.and hi))))
  have hh : 0 < δ / 2 := half_pos hδ
  have hrect (q : P) (hq : q ∈ ball p (δ / 2)) (t : ℝ)
      (ht : t ∈ Ioo (-(δ / 2)) (δ / 2)) :
      dist (q, t) (p, (0 : ℝ)) < δ := by
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨(mem_ball.mp hq).trans (half_lt_self hδ),
      ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hz : (0 : ℝ) ∈ Ioo (-(δ / 2)) (δ / 2) := ⟨by linarith, hh⟩
  have hn : ball p (δ / 2) ×ˢ Ioo (-(δ / 2)) (δ / 2) ∈ 𝓝 (p, (0 : ℝ)) :=
    (isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨mem_ball_self hh, hz⟩
  filter_upwards [hn] with z hz'
  have heq := ODE_solution_unique_of_mem_Ioo
    (v := fun _ => f) (s := fun _ => U)
    (fun _ _ => hLip) hz
    (fun t ht => ⟨(hnear (hrect z.1 hz'.1 t ht)).1,
      (hnear (hrect z.1 hz'.1 t ht)).2.2.1⟩)
    (fun t ht => ⟨(hnear (hrect z.1 hz'.1 t ht)).2.1,
      (hnear (hrect z.1 hz'.1 t ht)).2.2.2.1⟩)
    (hnear (hrect z.1 hz'.1 0 hz)).2.2.2.2
  exact heq hz'.2

end
end PositiveEinsteinFour.FlowCalculus

end OAI
