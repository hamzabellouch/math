import OAI.Probability.InvariantIsing.Cavity.ConsecutiveBlockPrior
import OAI.Probability.InvariantIsing.Magnetic.RestrictedDisorderTest
import OAI.Probability.InvariantIsing.Cavity.CavityFullProjectionMoment

namespace OAI

/-! A fixed position in repeated constrained blocks has a projection
moment bounded by the block size, uniformly in the number of blocks. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

theorem consecutive_block_projection_mean_le {n K m depth : ℕ}
    (hn : 0 < n) (hK : 3 ≤ K) (C : Finset (Spin n)) (hC : C.Nonempty)
    (μ : Measure (SpecialOrthogonal (K*n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin (K*n) → ℝ)
    (I : Fin m → Finset (Fin (K*n))) (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 2)
    (J : Finset (Fin (K*n))) (i : Fin n) (b₀ : Fin K) :
    restrictedCavityFullDisorderTest (consecutiveBlockConstraint n K C) (consecutiveBlockConstraint_nonempty C hC)
      μ T eig I u (cavityProjectionSiteTest J (finProdFinEquiv (b₀,i))) ≤ n := by
  have hN : 0 < K*n := Nat.mul_pos (by omega) hn
  let S := consecutiveBlockConstraint n K C
  have hS : S.Nonempty := consecutiveBlockConstraint_nonempty C hC
  let F := fun b : Fin K => cavityProjectionSiteTest (depth := depth) J (finProdFinEquiv (b,i))
  let a := fun b => restrictedCavityFullDisorderTest S hS μ T eig I u (F b)
  have he (b : Fin K) : a b = a b₀ := by
    obtain ⟨p,hp,hpb⟩ := even_block_permutation hK b b₀
    have ht := restricted_full_disorder_site_symmetry hN S hS μ T eig I u hu
      (consecutiveBlockSitePermutation (n := n) p) (consecutiveBlockConstraint_permutation hN C p hp)
      (F b) (measurable_cavityProjectionSiteTest J _) (Nat.cast_nonneg (K*n))
      (cavityProjectionSiteTest_bound J _)
    change a b = restrictedCavityFullDisorderTest S hS μ T eig I u _ at ht
    have hf : (fun U σ => F b (U * (spectralPermutation hN (consecutiveBlockSitePermutation p))⁻¹)
        (fun k => (cavitySignedSpinPermutation (consecutiveBlockSitePermutation p)
          (cavityPermutationFlip hN (consecutiveBlockSitePermutation p)) (σ k).1, (σ k).2))) = F b₀ := by
      funext U σ
      simp only [F, cavityProjectionSiteTest, cavitySpectralProjection_permutation_sq,
        consecutiveBlockSitePermutation_apply, hpb]
    rw [hf] at ht
    exact ht
  have hsum : |restrictedCavityFullDisorderTest S hS μ T eig I u
      (fun U σ => ∑ b, F b U σ)| ≤ ((K*n : ℕ) : ℝ) := by
    apply restrictedCavityFullDisorderTest_abs_le S hS μ T eig I u _
      (Finset.measurable_sum _ fun b _ => measurable_cavityProjectionSiteTest J _)
      (Nat.cast_nonneg (K*n))
    intro U σ
    have hinj : Function.Injective (fun b : Fin K => finProdFinEquiv (b,i)) := by
      intro b c hbc
      exact congrArg Prod.fst (finProdFinEquiv.injective hbc)
    have hpart : (∑ b, F b U σ) ≤ ∑ j : Fin (K*n),
        (cavitySpectralProjection (specialRotation U) J (spinVector (σ 0).1) j)^2 := by
      let f := fun j : Fin (K*n) =>
        (cavitySpectralProjection (specialRotation U) J (spinVector (σ 0).1) j)^2
      have hsumimage : (∑ j ∈ Finset.univ.image (fun b : Fin K => finProdFinEquiv (b,i)), f j) =
          ∑ b : Fin K, f (finProdFinEquiv (b,i)) := by
        rw [Finset.sum_image]
        exact fun b _ c _ hbc => hinj hbc
      change (∑ b : Fin K, f (finProdFinEquiv (b,i))) ≤ ∑ j, f j
      rw [← hsumimage]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => sq_nonneg _)
    rw [abs_of_nonneg (Finset.sum_nonneg (fun b _ => sq_nonneg _))]
    exact hpart.trans (by
      rw [← EuclideanSpace.real_norm_sq_eq]
      exact (cavitySpectralProjection_norm_sq_le _ J _).trans_eq (spinVector_norm_sq _))
  rw [restrictedCavityFullDisorderTest_sum S hS μ T eig I u F
    (fun b => measurable_cavityProjectionSiteTest J _) (Nat.cast_nonneg (K*n))
    (fun b => cavityProjectionSiteTest_bound J _)] at hsum
  simp only [Nat.cast_mul] at hsum
  change |∑ b, a b| ≤ K*n at hsum
  simp_rw [he] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hkpos : (0 : ℝ) < K := Nat.cast_pos.mpr (by omega)
  have hle := (le_abs_self ((K : ℝ) * a b₀)).trans hsum
  change a b₀ ≤ n
  nlinarith

end InvariantIsing

end

end OAI
