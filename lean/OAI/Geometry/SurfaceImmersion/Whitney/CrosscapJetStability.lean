import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceDirectionEstimates

namespace OAI

/-! A nondegenerate crosscap direction remains the only zero in a fixed
neighborhood after a sufficiently small second-jet change fixing its first jet. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem crosscap_jet_stability {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (b : Bool) (z : Base × ℝ)
    (hzero : surfaceDirection f b z = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection f b) z)) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧
      ∀ g : Base → ProjectionTarget 3, ContDiff ℝ ∞ g →
        fderiv ℝ g z.1 = fderiv ℝ f z.1 →
        (∀ x ∈ Metric.ball z.1 r,
          ‖fderiv ℝ g x-fderiv ℝ f x‖ ≤ δ ∧
          ‖fderiv ℝ (fderiv ℝ g) x-fderiv ℝ (fderiv ℝ f) x‖ ≤ δ) →
        ∀ w ∈ Metric.ball z r, surfaceDirection g b w = 0 ↔ w = z := by
  obtain ⟨r₀,ε,hr₀,hε,hstable⟩ :=
    local_linearization_stability_on (surfaceDirection_smooth hf b) z hreg
  let r := min r₀ 1
  let δ := ε/(|z.2|+3)
  have hr : 0 < r := lt_min hr₀ zero_lt_one
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨r,δ,hr,hδ,?_⟩
  intro g hg hfix hnear
  have hzeroG : surfaceDirection g b z = 0 := by
    simpa only [surfaceDirection,hfix] using hzero
  have hclose : ∀ w ∈ Metric.ball z r,
      ‖fderiv ℝ (surfaceDirection g b) w-fderiv ℝ (surfaceDirection f b) w‖ ≤ ε := by
    intro w hw
    have hw' : ‖w-z‖ < r := by simpa only [Metric.mem_ball,dist_eq_norm] using hw
    have hwbase : w.1 ∈ Metric.ball z.1 r := by
      rw [Metric.mem_ball,dist_eq_norm]
      exact (norm_fst_le (w-z)).trans_lt hw'
    have hθ : |w.2| ≤ |z.2|+1 := by
      have hd : |w.2-z.2| ≤ 1 := by
        have hh := (norm_snd_le (w-z)).trans hw'.le
        change |w.2-z.2| ≤ r at hh
        exact hh.trans (min_le_right _ _)
      calc
        _ ≤ |w.2-z.2|+|z.2| := by simpa using abs_add_le (w.2-z.2) z.2
        _ ≤ |z.2|+1 := by linarith
    obtain ⟨h₁,h₂⟩ := hnear w.1 hwbase
    calc
      _ ≤ ‖fderiv ℝ g w.1-fderiv ℝ f w.1‖*‖tangentRayVelocity b‖ +
          ‖fderiv ℝ (fderiv ℝ g) w.1-fderiv ℝ (fderiv ℝ f) w.1‖*‖tangentRay b w.2‖ :=
        norm_surfaceDirection_fderiv_sub hf hg b w
      _ ≤ δ*1+δ*(|z.2|+2) := by
        rw [tangentRayVelocity_norm]
        gcongr
        exact (tangentRay_norm_le b w.2).trans (by linarith)
      _ = ε := by dsimp [δ]; field_simp; ring
  have hinj : (Metric.ball z r).InjOn (surfaceDirection g b) := by
    exact hstable _ (convex_ball z r) (Metric.ball_subset_ball (min_le_left _ _))
      _ (surfaceDirection_smooth hg b) hclose
  intro w hw
  constructor
  · intro h
    exact hinj hw (Metric.mem_ball_self hr) (h.trans hzeroG.symm)
  · rintro rfl
    exact hzeroG

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
