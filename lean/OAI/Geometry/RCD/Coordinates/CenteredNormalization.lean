import OAI.Geometry.RCD.Coordinates.CenteredSplitting
import OAI.Geometry.RCD.Coordinates.GramNormalization

namespace OAI

/-! # Exact harmonic normalization survives centering -/

open Set MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Centering has zero local gradient in every covector, so it preserves
the complete actual mean Gram operator on the region. -/
theorem centeredColumn_meanGram {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (Ω : Set X) (hΩ : MeasurableSet Ω) (c : Euclidean n) (eta : SobolevSpace μ hQ)
    (heta : SobolevSpace.toLp μ hQ eta =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ)) :
    sobolevMeanGram μ hQ (sobolevColumnMap μ hQ (centeredColumn μ hQ u c eta)) Ω hΩ =
      sobolevMeanGram μ hQ (sobolevColumnMap μ hQ u) Ω hΩ := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℝ
  intro z
  rw [sobolevMeanGram_inner, sobolevMeanGram_inner]
  congr 1
  apply integral_congr_ae
  let U := sobolevColumnMap μ hQ u
  let V := sobolevColumnMap μ hQ (centeredColumn μ hQ u c eta)
  have hv := localGamma_eq_of_constant_difference μ hQ Ω (V v) (U v) (V z)
    (-⟪c, v⟫_ℝ) (centeredColumn_covector_difference μ hQ u Ω c v eta heta)
  have hz := localGamma_eq_of_constant_difference μ hQ Ω (V z) (U z) (U v)
    (-⟪c, z⟫_ℝ) (centeredColumn_covector_difference μ hQ u Ω c z eta heta)
  filter_upwards [hv, hz, ae_restrict_of_ae (localGamma_comm μ hQ (U v) (V z)),
    ae_restrict_of_ae (localGamma_comm μ hQ (U z) (U v))] with x hv hz hc hd
  exact hv.trans (hc.trans (hz.trans hd))

/-- The exact same frame normalizes both the original and centered
coordinate columns; no new normalizing matrix is chosen. -/
theorem IsExactMeanNormalization.center {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (Ω : Set X) (hΩ : MeasurableSet Ω) (c : Euclidean n) (eta : SobolevSpace μ hQ)
    (heta : SobolevSpace.toLp μ hQ eta =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ))
    (N : Euclidean n ≃L[ℝ] Euclidean n)
    (hN : IsExactMeanNormalization μ hQ (sobolevColumnMap μ hQ u) Ω hΩ N) :
    IsExactMeanNormalization μ hQ (sobolevColumnMap μ hQ (centeredColumn μ hQ u c eta)) Ω hΩ N := by
  unfold IsExactMeanNormalization at hN ⊢
  rw [sobolevMeanGram_comp, centeredColumn_meanGram μ hQ u Ω hΩ c eta heta,
    ← sobolevMeanGram_comp]
  exact hN

/-- Globally clipped coordinate extensions retain the same local mean
Gram whenever their representatives agree on the region. -/
theorem sobolevMeanGram_eq_of_local_representatives {n : ℕ}
    (u v : Fin n → SobolevSpace μ hQ) (Ω : Set X) (hΩ : MeasurableSet Ω)
    (hrep : ∀ j, SobolevSpace.toLp μ hQ (u j) =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ (v j)) :
    sobolevMeanGram μ hQ (sobolevColumnMap μ hQ u) Ω hΩ =
      sobolevMeanGram μ hQ (sobolevColumnMap μ hQ v) Ω hΩ := by
  classical
  apply ContinuousLinearMap.ext
  intro a
  apply ext_inner_right ℝ
  intro b
  rw [sobolevMeanGram_inner, sobolevMeanGram_inner]
  congr 1
  apply integral_congr_ae
  have hcol (a : Euclidean n) : SobolevSpace.toLp μ hQ (sobolevColumnMap μ hQ u a) =ᵐ[μ.restrict Ω]
      SobolevSpace.toLp μ hQ (sobolevColumnMap μ hQ v a) := by
    have hlocal (j : Fin n) : SobolevSpace.restrictLp μ hQ Ω (u j) =
        SobolevSpace.restrictLp μ hQ Ω (v j) := by
      apply Lp.ext
      exact (SobolevSpace.restrictLp_coe μ hQ Ω (u j)).trans
        ((hrep j).trans (SobolevSpace.restrictLp_coe μ hQ Ω (v j)).symm)
    have heq : SobolevSpace.restrictLp μ hQ Ω (sobolevColumnMap μ hQ u a) =
        SobolevSpace.restrictLp μ hQ Ω (sobolevColumnMap μ hQ v a) := by
      simp only [sobolevColumnMap_apply, map_sum, map_smul, hlocal]
    filter_upwards [SobolevSpace.restrictLp_coe μ hQ Ω (sobolevColumnMap μ hQ u a),
      SobolevSpace.restrictLp_coe μ hQ Ω (sobolevColumnMap μ hQ v a)] with x hu hv
    exact hu.symm.trans ((congrArg (fun f : Lp ℝ 2 (μ.restrict Ω) => f x) heq).trans hv)
  exact localGamma_pair_congr_ae μ hQ (hcol a) (hcol b)

end RegularPointCoordinates

end

end OAI
