import OAI.Probability.InvariantIsing.Cavity.CavityDisorderMean
import OAI.Probability.InvariantIsing.Cavity.CavityPhysicalProjection

namespace OAI

/-! The full perturbed Gibbs law has at most unit mean squared
spectral projection at every physical site. No cutoff is imposed. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def cavityProjectionSiteTest {N depth : ℕ} (J : Finset (Fin N)) (j : Fin N)
    (U : SpecialOrthogonal N) (σ : Fin 2 → Spin N × LabeledLeaf depth) : ℝ :=
  (cavitySpectralProjection (specialRotation U) J (spinVector (σ 0).1) j) ^ 2

lemma measurable_cavityProjectionSiteTest {N depth : ℕ}
    (J : Finset (Fin N)) (j : Fin N) :
    Measurable (Function.uncurry (cavityProjectionSiteTest (depth := depth) J j)) := by
  apply measurable_from_prod_countable_left
  intro σ
  exact (measurable_cavitySpectralProjection_site J (σ 0).1 j).pow_const 2

lemma cavityProjectionSiteTest_bound {N depth : ℕ}
    (J : Finset (Fin N)) (j : Fin N) (U : SpecialOrthogonal N)
    (σ : Fin 2 → Spin N × LabeledLeaf depth) :
    |cavityProjectionSiteTest J j U σ| ≤ N := by
  rw [cavityProjectionSiteTest, abs_sq]
  exact cavitySpectralProjection_site_sq_le _ J _ j

theorem cavity_full_projection_site_mean_le_one {N m depth : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 2)
    (J : Finset (Fin N)) (j : Fin N) :
    cavityFullDisorderTest μ T eig I u (cavityProjectionSiteTest J j) ≤ 1 := by
  let F := cavityProjectionSiteTest (depth := depth) J
  let a := fun i => cavityFullDisorderTest μ T eig I u (F i)
  have he (i : Fin N) : a i = a j := by
    have ht := cavity_full_disorder_site_symmetry hN μ T eig I u hu (Equiv.swap i j)
      (F i) (measurable_cavityProjectionSiteTest J i) (Nat.cast_nonneg N)
      (cavityProjectionSiteTest_bound J i)
    change a i = cavityFullDisorderTest μ T eig I u _ at ht
    have hf : (fun U σ => F i (U * (spectralPermutation hN (Equiv.swap i j))⁻¹)
        (fun k => (cavitySignedSpinPermutation (Equiv.swap i j)
          (cavityPermutationFlip hN (Equiv.swap i j)) (σ k).1, (σ k).2))) = F j := by
      funext U σ
      simp only [F, cavityProjectionSiteTest, cavitySpectralProjection_permutation_sq,
        Equiv.swap_apply_left]
    rw [hf] at ht
    exact ht
  have hsum : |cavityFullDisorderTest μ T eig I u (fun U σ => ∑ i, F i U σ)| ≤ N := by
    apply cavityFullDisorderTest_abs_le μ T eig I u _
      (Finset.measurable_sum _ fun i _ => measurable_cavityProjectionSiteTest J i)
      (Nat.cast_nonneg N)
    intro U σ
    have hs : (∑ i, F i U σ) =
        ‖cavitySpectralProjection (specialRotation U) J (spinVector (σ 0).1)‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      rfl
    rw [hs, abs_sq]
    exact (cavitySpectralProjection_norm_sq_le _ J _).trans_eq (spinVector_norm_sq _)
  rw [cavityFullDisorderTest_sum μ T eig I u F
    (fun i => measurable_cavityProjectionSiteTest J i) (Nat.cast_nonneg N)
    (fun i => cavityProjectionSiteTest_bound J i)] at hsum
  change |∑ i, a i| ≤ N at hsum
  simp_rw [he] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hle := (le_abs_self ((N : ℝ) * a j)).trans hsum
  change a j ≤ 1
  nlinarith

end InvariantIsing

end

end OAI
