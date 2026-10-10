import OAI.MeasureTheory.Falconer.Graphs.GraphAmplitudeRepresentative
import OAI.MeasureTheory.Falconer.Graphs.GraphParentDiameter
import OAI.MeasureTheory.Falconer.Graphs.GraphNonedgeErrorScale

namespace OAI

namespace PlanarFalconer
open Set

noncomputable def graphNonedgeThreshold (N : ℕ) (sig p : ℝ) : ℝ :=
  (2:ℝ)^(-p)*((2:ℝ)^N)^(30*sig)

noncomputable def graphRepresentativeZ (distance plus : Bool) (q : UnitCircle × UnitCircle) : ℝ :=
  graphChartZ (q.1:Plane) (graphSourceSign distance plus • (q.2:Plane))

noncomputable def graphRepresentativeAxis (distance plus : Bool) (q : UnitCircle × UnitCircle) : Plane :=
  graphChartAxis (q.1:Plane) (graphSourceSign distance plus • (q.2:Plane))

theorem uniform_graph_actual_nonedge_geometry {sig : ℝ} (hsig : 0 < sig) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a p c₀ : ℝ, 0 < c₀ →
    ∀ P : Fin 4 → DyadicSquare, (∀ i, 0 < (P i).side) →
    (∀ i, (P i).side ≤ (2:ℝ)^(-p)) →
    ‖(P 0).center-(P 1).center‖ ≤ 2004*(2:ℝ)^(-a) →
    ‖(P 2).center-(P 3).center‖ ≤ 2004*(2:ℝ)^(-a) →
    ∀ (distance plus : Bool) (axis : ℝ) (j k : ℕ) (q : UnitCircle × UnitCircle),
    GraphSourceRepresentative distance plus axis (graphAngularScale N sig (p-a) c₀) j k q →
    ∀ (b : Fin 4 → Plane → UnitCircle → ℂ) (x : Fin 4 → Plane),
    (∀ i, x i ∈ (P i).carrier) →
    ∀ Ψ : ℝ → ℝ, (∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) →
    ∀ η : Plane, ∀ z : ℝ,
    graphAmplitudePullback b x distance plus axis (graphAngularScale N sig (p-a) c₀) j k Ψ (η,z) ≠ 0 →
    let s := graphSourceSign distance plus
    let z₀ := graphRepresentativeZ distance plus q
    let e₀ := graphRepresentativeAxis distance plus q
    let v₀ := (P 0).center-(P 1).center
    let w₀ := (P 2).center-(P 3).center
    ‖(graphA z (x 0-x 1)+s • graphB z (x 2-x 3))-(graphA z₀ v₀+s • graphB z₀ w₀)‖ ≤
      graphNonedgeThreshold N sig p/2 ∧
    |inner ℝ (graphNormalizedAxis η) (graphDerivative s (x 0-x 1) (x 2-x 3))-
      inner ℝ e₀ (graphDerivative s v₀ w₀)| ≤ graphNonedgeThreshold N sig p/2 := by
  obtain ⟨N₀,hN₀⟩ := graph_representative_error_small (C := 112*2004) hsig (by norm_num)
  refine ⟨N₀,?_⟩
  intro N hN a p c₀ hc P hP hPp hc₀ hc₁ distance plus axis j k q hq b x hx Ψ hsupp η z hf
  dsimp only
  let δ := graphAngularScale N sig (p-a) c₀
  let ℓ := 2004*(2:ℝ)^(-a)
  have hδ : 0 ≤ δ := (graphAngularScale_pos N sig (p-a) hc).le
  have hℓ : 0 ≤ ℓ := by dsimp [ℓ]; positivity
  have hsmall : 20*(2:ℝ)^(-p)+(112*δ)*ℓ ≤ graphNonedgeThreshold N sig p/2 := by
    have he := hN₀ N hN a p δ (112*ℓ) hδ (by positivity) (min_le_right _ _)
      (by dsimp [ℓ]; ring_nf; exact le_rfl)
    dsimp only [graphNonedgeThreshold]
    convert he using 1
    ring
  have hmove := hq.amplitude_coordinates b x hsupp hf
  have hzmove : |z-graphRepresentativeZ distance plus q| ≤ 112*δ :=
    (le_add_of_nonneg_right (dist_nonneg)).trans hmove
  have hemove : ‖graphNormalizedAxis η-graphRepresentativeAxis distance plus q‖ ≤ 112*δ := by
    rw [← dist_eq_norm]
    exact (le_add_of_nonneg_left (abs_nonneg _)).trans hmove
  have hs : |graphSourceSign distance plus| = 1 := by
    rcases graphSourceSign_cases distance plus with he | he <;> rw [he] <;> norm_num
  have hv := dyadic_four_endpoint_errors P x hP hPp hx 0 1
  have hw := dyadic_four_endpoint_errors P x hP hPp hx 2 3
  have hsupport := graphAmplitudePullback_tsupport b x distance plus axis δ j k hsupp (subset_closure hf)
  have hz : |z| ≤ 4 := abs_le.mpr hsupport.1.2
  have hlo : (1:ℝ)/8 ≤ ‖η‖ := hsupport.2
  have hη : η ≠ 0 := norm_pos_iff.mp (by linarith)
  have he : ‖graphNormalizedAxis η‖ = 1 := by
    rw [graphNormalizedAxis_eq_all hη,norm_sourceDirection]
  constructor
  · exact (graph_vector_perturbation _ z _ _ _ _ _ hs (by positivity) (by positivity) hℓ
      hz hzmove hv hw hc₀ hc₁).trans hsmall
  · apply (graph_scalar_perturbation _ _ _ _ _ _ _ hs (by positivity) (by positivity) hℓ
      he hemove hv hw hc₀ hc₁).trans
    exact (by nlinarith [show (0:ℝ) ≤ (2:ℝ)^(-p) by positivity] :
      4*(2:ℝ)^(-p)+(112*δ)*ℓ ≤ 20*(2:ℝ)^(-p)+(112*δ)*ℓ).trans hsmall

end PlanarFalconer

end OAI
