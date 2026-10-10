import OAI.MeasureTheory.Falconer.Estimates.EndpointSubprobability
import OAI.MeasureTheory.Falconer.Estimates.RotatedTubeData
import OAI.MeasureTheory.Falconer.Slicing.PlanarSliceGeometry

namespace OAI

/-! # The endpoint small-cap estimate in every orientation -/

namespace Falconer
open Set MeasureTheory Real
open scoped ENNReal

theorem endpoint_oriented_chart_gain (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {t ζ C ρ : ℝ}
    (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2) (hζ : 0 < ζ)
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/8)
    (hstable : (h:ℝ)*((h+3:ℝ)*(2*ρ)) ≤ 1/2) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      ∀ (μ : Measure (Space (h+3))) (ν : Measure (Sphere (h+3)))
        [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      ∀ (w₀ : Sphere (h+3)) (E : Set (Space (h+3) × Sphere (h+3)))
        (J : Sphere (h+3) → Finset ι) (v : ι → Space (h+3)),
      (∀ᵐ w ∂ν, dist w w₀ ≤ ρ) →
      (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
      (∀ x : Space (h+3), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ N → ν (Metric.ball w (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ))) →
      (∀ w : Sphere (h+3), ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
        ν {u : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (u:Space (h+3))| ≤ r} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*r^ζ)) →
      MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
      (∀ w, ((J w).card : ℝ) ≤ (1/(2:ℝ)^N)^(-(h+1:ℝ)-ε)) →
      (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖v i‖ ≤ 1/4) →
      (∀ u ∈ E, ∃ i ∈ J u.2,
        ‖perpendicularPart (u.2:Space (h+3)) (u.1-v i)‖ ≤ C*(1/(2:ℝ)^N)) →
      (μ.prod ν) E ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^c) := by
  obtain ⟨ε,c,hε,hc,N₀,hgain⟩ := endpoint_chart_subprobability_gain hLW ht ht' hζ hC hρ hρsmall hstable
  refine ⟨ε,c,hε,hc,N₀,?_⟩
  intro N hN ι _ _ μ ν _ _ w₀ E J v hν hμ hμmass hνmass hμball hνball hslab hE hJ hJN hEb hanchors hcover
  let north : Sphere (h+3) := gnomonicChart (0 : Space (h+2))
  let e : Space (h+3) ≃ₗᵢ[ℝ] Space (h+3) :=
    (ℝ ∙ ((w₀:Space (h+3))-(north:Space (h+3))))ᗮ.reflection
  have he : sphereMap e w₀ = north := by
    apply Subtype.ext
    exact Submodule.reflection_sub ((sphere_norm w₀).trans (sphere_norm north).symm)
  let μ' := Measure.map e μ
  let ν' := Measure.map (sphereMap e) ν
  let E' := rotatedTubeRelation e E
  let J' : Sphere (h+3) → Finset ι := fun w => J (sphereMap e.symm w)
  let v' : ι → Space (h+3) := fun i => e (v i)
  have hν' : ∀ᵐ w ∂ν', dist w north ≤ ρ := by
    rw [← he]
    exact rotated_direction_cap_ae ν e hν
  have hμ'mass : μ' univ ≤ 1 := by
    simpa only [μ',Measure.map_apply e.continuous.measurable MeasurableSet.univ,preimage_univ] using hμmass
  have hν'mass : ν' univ ≤ 1 := by
    simpa only [ν',Measure.map_apply (continuous_sphereMap e).measurable MeasurableSet.univ,preimage_univ] using hνmass
  have hμ'ball (x : Space (h+3)) (j : ℕ) (hj : j ≤ N) :
      μ' (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t) := by
    rw [rotated_point_ball]
    exact hμball _ j hj
  have hν'ball (w : Sphere (h+3)) (j : ℕ) (hj : j ≤ N) :
      ν' (Metric.ball w (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ)) := by
    rw [rotated_direction_ball]
    exact hνball _ j hj
  have hslab' (w : Sphere (h+3)) (r : ℝ) (hr : 1/(2:ℝ)^N ≤ r) (hr1 : r ≤ 1) :
      ν' {u : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (u:Space (h+3))| ≤ r} ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*r^ζ) := by
    rw [rotated_direction_slab]
    exact hslab _ r hr hr1
  have hg := hgain N hN ι μ' ν' E' J' v' hν' (rotated_point_norm_ae μ e hμ)
    hμ'mass hν'mass hμ'ball hν'ball hslab' (rotatedTubeRelation_measurable e hE)
    (fun i => (hJ i).preimage (continuous_sphereMap e.symm).measurable)
    (fun w => hJN (sphereMap e.symm w)) (rotatedTubeRelation_point_bound e hEb)
    (fun w i hi => by simpa only [v',e.norm_map] using hanchors (sphereMap e.symm w) i hi)
    (rotatedTubeRelation_cover e J v hcover)
  have hmass : (μ'.prod ν') E' = (μ.prod ν) E := rotated_incidence μ ν e E hE
  rw [hmass] at hg
  exact hg

end Falconer

end OAI
