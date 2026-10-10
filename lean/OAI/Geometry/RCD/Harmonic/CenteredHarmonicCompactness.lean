import OAI.Geometry.RCD.Harmonic.ExpandingHarmonicCompactness
import OAI.Geometry.RCD.Harmonic.CenteredHarmonicDirection

namespace OAI

/-! # Entire limits of the original centered and rescaled harmonic functions -/

open Set Metric Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.centered_harmonic_compactness {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (p : ℕ → X) (r ε T : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hε : ∀ k, 0 ≤ ε k) (hε1 : ∀ k, ε k ≤ 1)
    (hεlim : Tendsto ε atTop (𝓝 0)) (hT : Tendsto T atTop atTop)
    (u : ℕ → SobolevSpace (hausdorff n X) hX.quadratic) (v : ℕ → X → ℝ)
    (hu : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (T k*r k)) (u k))
    (hrep : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) =ᵐ[
      (hausdorff n X).restrict (ball (p k) (T k*r k))] v k)
    (L : ℕ → ℝ≥0) (A : ℕ → ℝ) (hA : ∀ m, 0 ≤ A m)
    (hdata : ∀ m : ℕ, ∀ᶠ k in atTop, -1 ≤ K*(r k)^2 ∧
      IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k)
        ((m : ℝ)+1) (ε k) (V k) ∧
      (∀ x, dist x (p k) ≤ ((m : ℝ)+1)*r k → |(v k x-v k (p k))/r k| ≤ A m) ∧
      (∀ x y, dist x (p k) ≤ ((m : ℝ)+1)*r k → dist y (p k) ≤ ((m : ℝ)+1)*r k →
        |(v k x-v k (p k))/r k-(v k y-v k (p k))/r k| ≤ (L m : ℝ)*(dist x y/r k))) :
    ∃ (a : ℕ → ℕ) (f : Euclidean n → ℝ), StrictMono a ∧ Continuous f ∧
      InnerProductSpace.HarmonicOnNhd f univ ∧
      (∀ ρ : ℝ, ∃ C : ℝ≥0, LipschitzOnWith C f (closedBall 0 ρ)) ∧
      ∀ W : ℝ, 0 < W → ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ x,
        dist x (p (a k)) ≤ W*r (a k) →
          |(v (a k) x-v (a k) (p (a k)))/r (a k)-f (V (a k) x)| < η := by
  classical
  let μ := hausdorff n X
  let f₀ := fun k x => (v k x-v k (p k))/r k
  let Good := fun (m k : ℕ) => (m : ℝ)+1 ≤ T k ∧
    ∀ x, dist x (p k) ≤ ((m : ℝ)+1)*r k → |f₀ k x| ≤ A m
  have hex (m k : ℕ) : ∃ w : SobolevSpace μ hX.quadratic, Good m k →
      IsSobolevHarmonicOn μ hX.quadratic (ball (p k) (((m : ℝ)+1)*r k)) w ∧
      (SobolevSpace.toLp μ hX.quadratic w =ᵐ[
        μ.restrict (ball (p k) (((m : ℝ)+1)*r k))] f₀ k) ∧
      harmonicTargetNorm hX (p k) (((m : ℝ)+1)*r k) w ≤ A m := by
    by_cases hg : Good m k
    · have hsub : ball (p k) (((m : ℝ)+1)*r k) ⊆ ball (p k) (T k*r k) :=
        ball_subset_ball (mul_le_mul_of_nonneg_right hg.1 (hr k).le)
      obtain ⟨w,hw,hwr,hwn⟩ := hX.centered_harmonic_direction hn (p k)
        (mul_pos (by positivity : 0 < (m : ℝ)+1) (hr k)) (hr k) (hA m)
        (u k) (v k) (v k (p k)) ((hu k).mono μ hX.quadratic hsub)
        (ae_restrict_of_ae_restrict_of_subset hsub (hrep k)) (by
          intro x hx
          have hh := hg.2 x hx.le
          rw [abs_div,abs_of_pos (hr k)] at hh
          exact (div_le_iff₀ (hr k)).mp hh)
      exact ⟨w,fun _ => ⟨hw,hwr,hwn⟩⟩
    · exact ⟨0,fun hh => (hg hh).elim⟩
  choose w hw using hex
  apply hX.expanding_harmonic_compactness hn p r ε V hr hε hε1 hεlim f₀ w L A
    (fun m => A m+1) hA (fun m => by linarith [hA m])
  intro m
  filter_upwards [hdata m,hT.eventually (eventually_ge_atTop ((m : ℝ)+1))] with k hk ht
  have hgood : Good m k := ⟨ht,hk.2.2.1⟩
  have hloc := hw m k hgood
  exact ⟨hk.1,hk.2.1,hloc.1,hloc.2.1,hloc.2.2.trans (by linarith),hk.2.2.1,hk.2.2.2⟩

end RegularPointCoordinates

end

end OAI
