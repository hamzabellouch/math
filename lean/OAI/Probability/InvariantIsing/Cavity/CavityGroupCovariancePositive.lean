import OAI.Probability.InvariantIsing.Cavity.CavityGroupCovariance
import OAI.Probability.InvariantIsing.Cavity.CavitySpectralGaussianTest

namespace OAI

/-! Positivity of the actual block covariance for all spectral groups
and all fresh axes. No invertibility is needed. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology BoundedContinuousFunction Matrix

namespace InvariantIsing

lemma continuous_cavityGroupReplicaCovariance {m r : ℕ} (q : ℕ) :
    Continuous (cavityGroupReplicaCovariance (m := m) (r := r) q) := by
  classical
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases h : i.1 = j.1 ∧ i.2.2 = j.2.2
  · simpa only [cavityGroupReplicaCovariance, ite_eq_left h] using
      (show Continuous (fun Q : Fin m → Matrix (Fin r) (Fin r) ℝ => Q i.1 i.2.1 j.2.1) from by fun_prop)
  · simp only [cavityGroupReplicaCovariance, ite_eq_right h]
    exact continuous_const

lemma cavityGroupReplicaCovariance_posSemidef {m r q : ℕ}
    (Q : Fin m → Matrix (Fin r) (Fin r) ℝ) (hQ : ∀ a, (Q a).PosSemidef) :
    (cavityGroupReplicaCovariance q Q).PosSemidef := by
  classical
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    rintro ⟨a, i, t⟩ ⟨b, j, s⟩
    by_cases hab : a = b
    · subst b
      by_cases hts : t = s
      · subst s
        simpa only [cavityGroupReplicaCovariance, and_self, ite_true, star_trivial] using
          (hQ a).isHermitian.apply i j
      · simp [cavityGroupReplicaCovariance, hts, Ne.symm hts]
    · simp [cavityGroupReplicaCovariance, hab, Ne.symm hab]
  · intro v
    have hm (a : Fin m) (i : Fin r) (t : Fin q) :
        (cavityGroupReplicaCovariance q Q *ᵥ v) (a, i, t) =
          ∑ j, Q a i j * v (a, j, t) := by
      simp [Matrix.mulVec, dotProduct, cavityGroupReplicaCovariance,
        Fintype.sum_prod_type, ite_and, ite_mul]
    have he : star v ⬝ᵥ (cavityGroupReplicaCovariance q Q *ᵥ v) =
        ∑ a : Fin m, ∑ t : Fin q,
          star (fun i : Fin r => v (a, i, t)) ⬝ᵥ (Q a *ᵥ fun i => v (a, i, t)) := by
      simp only [dotProduct, Pi.star_apply, star_trivial, Fintype.sum_prod_type]
      simp_rw [hm]
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    rw [he]
    exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun t _ =>
      (hQ a).dotProduct_mulVec_nonneg (fun i => v (a, i, t))

def cavitySpectralBlockCovariance {m r : ℕ} (q : ℕ) (ρ : Fin m → ℝ)
    (x : SpectralBlock (m + 1) r) :
    Matrix (Fin m × (Fin r × Fin q)) (Fin m × (Fin r × Fin q)) ℝ :=
  cavityGroupReplicaCovariance q (fun a i j => (x i j a.castSucc : ℝ) / ρ a)

lemma continuous_cavitySpectralBlockCovariance {m r : ℕ} (q : ℕ) (ρ : Fin m → ℝ) :
    Continuous (cavitySpectralBlockCovariance (r := r) q ρ) := by
  apply (continuous_cavityGroupReplicaCovariance q).comp
  fun_prop

lemma cavitySpectralBlockCovariance_posSemidef {m r q : ℕ}
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 ≤ ρ a) (x : SpectralArray (m + 1)) (hx : SpectralGram x) :
    (cavitySpectralBlockCovariance q ρ (spectralBlockView (m + 1) r x)).PosSemidef := by
  apply cavityGroupReplicaCovariance_posSemidef
  intro a
  have hh := (hx a.castSucc r).smul (inv_nonneg.mpr (hρ a))
  have he : (fun i j : Fin r => (spectralBlockView (m + 1) r x i j a.castSucc : ℝ) / ρ a) =
      (ρ a)⁻¹ • (fun i j : Fin r => spectralCoordinateArray a.castSucc x i j) := by
    ext i j
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm,
      spectralBlockView, spectralCoordinateArray]
  rw [he]
  exact hh

theorem cavity_spectral_frame_gaussian_test_tendsto {m r q : ℕ}
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 ≤ ρ a)
    (P : ℕ → ProbabilityMeasure (SpectralArray (m + 1)))
    (P₀ : ProbabilityMeasure (SpectralArray (m + 1))) (hP : Filter.Tendsto P Filter.atTop (𝓝 P₀))
    (hG : ∀ n, ∀ᵐ x ∂(P n : Measure (SpectralArray (m + 1))), SpectralGram x)
    (hG₀ : ∀ᵐ x ∂(P₀ : Measure (SpectralArray (m + 1))), SpectralGram x)
    (F : SpectralBlock (m + 1) r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) :
    Filter.Tendsto (fun n => ∫ x, ∫ z, F (spectralBlockView (m + 1) r x, z)
      ∂multivariateGaussian 0 (cavitySpectralBlockCovariance q ρ (spectralBlockView (m + 1) r x))
      ∂(P n : Measure (SpectralArray (m + 1)))) Filter.atTop
      (𝓝 (∫ x, ∫ z, F (spectralBlockView (m + 1) r x, z)
      ∂multivariateGaussian 0 (cavitySpectralBlockCovariance q ρ (spectralBlockView (m + 1) r x))
      ∂(P₀ : Measure (SpectralArray (m + 1))))) :=
  cavity_spectral_gaussian_test_tendsto P P₀ hP _ (continuous_cavitySpectralBlockCovariance q ρ)
    (fun n => (hG n).mono fun x hx => cavitySpectralBlockCovariance_posSemidef ρ hρ x hx)
    (hG₀.mono fun x hx => cavitySpectralBlockCovariance_posSemidef ρ hρ x hx) F

end InvariantIsing

end

end OAI
