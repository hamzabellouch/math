import OAI.Geometry.RCD.Harmonic.AffineValuePairings

namespace OAI

/-! # Finite affine Hilbert moments from the actual pointed value limit -/

open Set Metric Filter MeasureTheory
open scoped Topology InnerProductSpace NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.affine_value_moments_of_limit {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) {S : ℝ} (hS : 0<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (hr : ∀ k, 0<r k)
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n) (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (hε : Tendsto ε atTop (𝓝 0))
    (hrep : ∀ k j, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k j)=ᵐ[
      (hausdorff n X).restrict (ball (p k) (S*r k))] fun x => v k x j)
    (g : Euclidean n → ℝ) (hg : MemLp g 2 (volume.restrict (ball 0 S)))
    (hmodel : ∀ τ<S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 τ))
    (hconv : ∀ ρ : ℝ, 0<ρ → ρ<S → ∀ η : ℝ, 0<η → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (ρ*r k)),
      |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-g (v k x)|≤η) :
    ∀ ρ : ℝ, 0<ρ → ∀ hρS : ρ<S, ∀ i j,
      Tendsto (fun k =>
        ⟪localAffineMomentFamily (hausdorff n X) hX.quadratic (u k) (w k)
            (ball (p k) (ρ*r k)) (hX.finiteOnBounded _ isBounded_ball).ne i,
          localAffineMomentFamily (hausdorff n X) hX.quadratic (u k) (w k)
            (ball (p k) (ρ*r k)) (hX.finiteOnBounded _ isBounded_ball).ne j⟫_ℝ)
        atTop (𝓝 ⟪euclideanValueMoments g hg hρS.le i,euclideanValueMoments g hg hρS.le j⟫_ℝ) := by
  intro ρ hρ hρS i j
  let μ := hausdorff n X
  let τ := (ρ+S)/2
  have hρτ : ρ<τ := by dsimp only [τ]; linarith
  have hτS : τ<S := by dsimp only [τ]; linarith
  have hLift (a) : ∃ L : ℝ≥0,
      LipschitzOnWith L (affineValueFamily g id a) (closedBall 0 τ) := by
    rcases a with _ | (_ | k)
    · exact hmodel τ hτS
    · exact ⟨0,(LipschitzWith.const (1:ℝ)).lipschitzOnWith⟩
    · exact ⟨_,(EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) k).lipschitzWith.lipschitzOnWith⟩
  obtain ⟨Li,hLi⟩ := hLift i
  obtain ⟨Lj,hLj⟩ := hLift j
  have hrep' (k a) : SobolevSpace.toLp μ hX.quadratic (u k a)=ᵐ[
      μ.restrict (ball (p k) (ρ*r k))] fun x => v k x a :=
    ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (mul_le_mul_of_nonneg_right hρS.le (hr k).le)) (hrep k a)
  have hprod (k) : Integrable (fun x =>
      affineValueFamily (SobolevSpace.toLp μ hX.quadratic (w k)) (v k) i x*
      affineValueFamily (SobolevSpace.toLp μ hX.quadratic (w k)) (v k) j x)
      (μ.restrict (ball (p k) (ρ*r k))) :=
    (affineValueFamily_memLp μ hX.quadratic (u k) (w k) (v k) _
      (hX.finiteOnBounded _ isBounded_ball).ne (hrep' k) i).integrable_mul
    (affineValueFamily_memLp μ hX.quadratic (u k) (w k) (v k) _
      (hX.finiteOnBounded _ isBounded_ball).ne (hrep' k) j)
  have hconv' (a) : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop,
      ∀ᵐ x ∂μ.restrict (ball (p k) (ρ*r k)),
      |affineValueFamily (SobolevSpace.toLp μ hX.quadratic (w k)) (v k) a x-
        affineValueFamily g id a (v k x)|≤η := by
    rcases a with _ | (_ | k)
    · exact hconv ρ hρ hρS
    · intro η hη
      exact Eventually.of_forall fun _ => Eventually.of_forall fun _ => by
        simpa only [affineValueFamily,affineMomentFamily,sub_self,abs_zero] using hη.le
    · intro η hη
      exact Eventually.of_forall fun _ => Eventually.of_forall fun _ => by
        simpa only [affineValueFamily,affineMomentFamily,id_eq,sub_self,abs_zero] using hη.le
  have ht := inner_ball_value_moment_tendsto hS hρ hρτ hτS.le hr hv
    (fun _ => (hX.finiteOnBounded _ isBounded_ball).ne)
    (fun k => ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hS (hr k))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne)
    (fun k => ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hρ (hr k))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne) hε
    (fun k => affineValueFamily (SobolevSpace.toLp μ hX.quadratic (w k)) (v k) i)
    (fun k => affineValueFamily (SobolevSpace.toLp μ hX.quadratic (w k)) (v k) j)
    (affineValueFamily g id i) (affineValueFamily g id j)
    hLi hLj hprod (hconv' i) (hconv' j)
  rw [euclideanValueMoments_pairing g hg hρS.le i j]
  apply ht.congr'
  exact Eventually.of_forall fun k =>
    (localAffineMomentFamily_pairing μ hX.quadratic (u k) (w k) (v k)
      (ball (p k) (ρ*r k)) (hX.finiteOnBounded _ isBounded_ball).ne (hrep' k) i j).symm

end RegularPointCoordinates

end

end OAI
