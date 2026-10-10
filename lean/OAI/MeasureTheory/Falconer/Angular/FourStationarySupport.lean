import OAI.MeasureTheory.Falconer.Angular.StationaryApproximantSupport
import OAI.MeasureTheory.Falconer.Measures.FourSpatialPairMeasure

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem pair_ae_four_restrictions (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (X : Fin 4 → Set Plane) (P Q : Plane × Plane → Prop)
    (hP : ∀ᵐ z ∂ρ.prod ρ, P z) (hQ : ∀ᵐ z ∂ν.prod ν, Q z) :
    ∀ᵐ x ∂Measure.pi (fun i => (![ρ,ρ,ν,ν] i).restrict (X i)),
      P (x 0,x 1) ∧ Q (x 2,x 3) := by
  let μ : Fin 4 → Measure Plane := fun i => (![ρ,ρ,ν,ν] i).restrict (X i)
  let : ∀ i, IsFiniteMeasure (μ i) := by
    intro i; fin_cases i <;> dsimp [μ] <;> infer_instance
  have hP' : ∀ᵐ z ∂(μ 0).prod (μ 1), P z :=
    (ae_mono (Measure.prod_mono (μ' := ρ) (ν' := ρ) Measure.restrict_le_self Measure.restrict_le_self)) hP
  have hQ' : ∀ᵐ z ∂(μ 2).prod (μ 3), Q z :=
    (ae_mono (Measure.prod_mono (μ' := ν) (ν' := ν) Measure.restrict_le_self Measure.restrict_le_self)) hQ
  have hpq : ∀ᵐ z ∂((μ 0).prod (μ 1)).prod ((μ 2).prod (μ 3)), P z.1 ∧ Q z.2 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hP',
      Measure.quasiMeasurePreserving_snd.ae hQ'] with z hz₁ hz₂
    exact ⟨hz₁,hz₂⟩
  exact (measurePreserving_fourSpatialPair μ).quasiMeasurePreserving.ae hpq

theorem stationary_spatial_good_of_pair_good (β γ : Plane → UnitCircle → ℂ)
    (G H : Set (Plane × Plane)) (x : Fin 4 → Plane)
    (hβ : ∀ n r, 0 < r → x 0 ≠ x 1 → angularPairStationary β n (x 0) (x 1) r ≠ 0 → (x 0,x 1) ∈ G)
    (hγ : ∀ n r, 0 < r → x 2 ≠ x 3 → angularPairStationary γ n (x 2) (x 3) r ≠ 0 → (x 2,x 3) ∈ H)
    {Ψ : ℝ → ℝ} (hs : ∀ t, Ψ t ≠ 0 → 0 < t) (n : ℕ) (v : ℝ)
    (hx : x 0 ≠ x 1) (hy : x 2 ≠ x 3)
    (hn : angularStationarySpatialKernel β γ n v Ψ x ≠ 0) :
    (x 0,x 1) ∈ G ∧ (x 2,x 3) ∈ H := by
  by_contra hbad
  apply hn
  unfold angularStationarySpatialKernel
  have hz : (∫ r : ℝ, Ψ (r/(2:ℝ)^v) •
      (angularPairStationary β n (x 0) (x 1) r * angularPairStationary γ n (x 2) (x 3) r)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards with r
    by_cases hp : Ψ (r/(2:ℝ)^v) = 0
    · simp [hp]
    · have hr : 0 < r := (div_pos_iff.mp (hs _ hp)).resolve_right (fun hz => (not_lt_of_ge (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) v)) hz.2) |>.1
      by_contra hne
      apply hbad
      constructor
      · apply hβ n r hr hx
        intro hz
        exact hne (by simp [hz])
      · apply hγ n r hr hy
        intro hz
        exact hne (by simp [hz])
  rw [hz,smul_zero]

end PlanarFalconer

end OAI
