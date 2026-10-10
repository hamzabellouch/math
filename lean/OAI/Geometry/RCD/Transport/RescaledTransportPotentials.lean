import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Scale-invariant potentials for bounded endpoint transport -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X]

/-- The linear-radius potential theorem has uniform constants after rescaling.
Only its value bounds, dual inequality and exact contact are retained here. -/
theorem rescaled_transport_potentials (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (hQ : QuadraticCheegerEnergy μ) (hgeo : IsGeodesicSpace X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (hac : ν₀ ≪ μ) {π : Measure (X×X)} (hp : IsOptimalCoupling ν₀ ν₁ π)
    (p : X) {ρ r : ℝ} (hρ : 0≤ρ) (hr : 0<r)
    (h0 : ∀ᵐ x ∂ν₀, dist x p≤ρ*r) (h1 : ∀ᵐ x ∂ν₁, dist x p≤ρ*r) :
    ∃ φ ψ : X → ℝ,
      LipschitzWith ⟨5*ρ/r,by positivity⟩ φ ∧
      LipschitzWith ⟨5*ρ/r,by positivity⟩ ψ ∧
      (∀ x, |φ x|≤10*ρ^2) ∧ (∀ x, |ψ x|≤10*ρ^2) ∧
      (∀ x y, φ x+ψ y≤(dist x y/r)^2/2) ∧
      (∀ᵐ xy ∂π, φ xy.1+ψ xy.2=(dist xy.1 xy.2/r)^2/2) := by
  obtain ⟨_,a,b,ha,hb,hab,hbb,_,_,_,_,_,had,hc,_⟩ :=
    hp.linear_radius_bounded_sobolev_potential μ hQ hgeo ν₀ ν₁ hac p
      (mul_nonneg hρ hr.le) h0 h1
  have hscale (q : X → ℝ) (hq : LipschitzWith ⟨5*(ρ*r),by positivity⟩ q) :
      LipschitzWith ⟨5*ρ/r,by positivity⟩ (fun x => q x/r^2) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq,← sub_div,abs_div,abs_of_pos (sq_pos_of_pos hr)]
    change |q x-q y|/r^2≤(5*ρ/r)*dist x y
    have hxy := hq.dist_le_mul x y
    change dist (q x) (q y)≤(5*(ρ*r))*dist x y at hxy
    rw [Real.dist_eq] at hxy
    calc
      |q x-q y|/r^2≤(5*(ρ*r)*dist x y)/r^2 :=
        div_le_div_of_nonneg_right hxy
          (sq_nonneg r)
      _ = (5*ρ/r)*dist x y := by field_simp [hr.ne']
  have hbound (q : X → ℝ) (hq : ∀ x, |q x|≤10*(ρ*r)^2) (x : X) :
      |q x/r^2|≤10*ρ^2 := by
    rw [abs_div,abs_of_pos (sq_pos_of_pos hr)]
    calc |q x|/r^2≤(10*(ρ*r)^2)/r^2 :=
        div_le_div_of_nonneg_right (hq x) (sq_nonneg r)
      _ = 10*ρ^2 := by field_simp [hr.ne']
  refine ⟨fun x => a x/r^2,fun x => b x/r^2,hscale a ha,hscale b hb,?_,?_,?_,?_⟩
  · exact hbound a (fun x => by rw [abs_of_nonneg (hab x).1]; exact (hab x).2)
  · apply hbound b
    intro x
    rw [abs_of_nonpos (hbb x).2]
    linarith [(hbb x).1]
  · intro x y
    rw [← add_div]
    calc (a x+b y)/r^2≤(dist x y^2/2)/r^2 :=
        div_le_div_of_nonneg_right (had x y) (sq_nonneg r)
      _ = (dist x y/r)^2/2 := by ring
  · filter_upwards [hc] with xy hxy
    rw [← add_div,hxy]
    ring

end RegularPointCoordinates

end

end OAI
