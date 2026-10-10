import OAI.Probability.InvariantIsing.Cavity.ConsecutiveProductPrior
import OAI.Probability.InvariantIsing.Magnetic.RestrictedDisorderTest
import OAI.Probability.InvariantIsing.Cavity.CavityFullProjectionMoment
import OAI.Probability.InvariantIsing.Cavity.CavityFullTail

namespace OAI

/-! A fixed position in repeated constrained blocks has a projection
moment bounded by the block size, uniformly in the number of blocks. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

theorem consecutive_product_projection_mean_le {n K m depth : ℕ}
    (hn : 0 < n) (hK : 2 ≤ K) (C : Finset (Spin n)) (hC : C.Nonempty)
    (μ : Measure (SpecialOrthogonal (K*n+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin (K*n+n) → ℝ)
    (I : Fin m → Finset (Fin (K*n+n))) (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 2)
    (J : Finset (Fin (K*n+n))) (i : Fin n) (b₀ : Fin (K+1)) :
    restrictedCavityFullDisorderTest (cavityProductSlice (consecutiveBlockConstraint n K C) C) (cavityProductSlice_nonempty _ (consecutiveBlockConstraint_nonempty C hC) C hC)
      μ T eig I u (cavityProjectionSiteTest J (consecutiveProductSite n K b₀ i)) ≤ n := by
  have hN : 0 < K*n+n := by omega
  let S := cavityProductSlice (consecutiveBlockConstraint n K C) C
  have hS : S.Nonempty := cavityProductSlice_nonempty _ (consecutiveBlockConstraint_nonempty C hC) C hC
  let F := fun b : Fin (K+1) => cavityProjectionSiteTest (depth := depth) J (consecutiveProductSite n K b i)
  let a := fun b => restrictedCavityFullDisorderTest S hS μ T eig I u (F b)
  have he (b : Fin (K+1)) : a b = a b₀ := by
    obtain ⟨p,hp,hpb⟩ := even_block_permutation (by omega : 3 ≤ K+1) b b₀
    have ht := restricted_full_disorder_site_symmetry hN S hS μ T eig I u hu
      (consecutiveProductSitePermutation (n := n) p) (consecutiveProduct_permutation hN C p hp)
      (F b) (measurable_cavityProjectionSiteTest J _) (Nat.cast_nonneg (K*n+n))
      (cavityProjectionSiteTest_bound J _)
    change a b = restrictedCavityFullDisorderTest S hS μ T eig I u _ at ht
    have hf : (fun U σ => F b (U * (spectralPermutation hN (consecutiveProductSitePermutation p))⁻¹)
        (fun k => (cavitySignedSpinPermutation (consecutiveProductSitePermutation p)
          (cavityPermutationFlip hN (consecutiveProductSitePermutation p)) (σ k).1, (σ k).2))) = F b₀ := by
      funext U σ
      simp only [F, cavityProjectionSiteTest, cavitySpectralProjection_permutation_sq,
        consecutiveProductSitePermutation_apply, hpb]
    rw [hf] at ht
    exact ht
  have hsum : |restrictedCavityFullDisorderTest S hS μ T eig I u
      (fun U σ => ∑ b, F b U σ)| ≤ ((K*n+n : ℕ) : ℝ) := by
    apply restrictedCavityFullDisorderTest_abs_le S hS μ T eig I u _
      (Finset.measurable_sum _ fun b _ => measurable_cavityProjectionSiteTest J _)
      (Nat.cast_nonneg (K*n+n))
    intro U σ
    have hinj : Function.Injective (fun b : Fin (K+1) => consecutiveProductSite n K b i) := by
      intro b c hbc
      exact consecutiveProductSite_injective i hbc
    have hpart : (∑ b, F b U σ) ≤ ∑ j : Fin (K*n+n),
        (cavitySpectralProjection (specialRotation U) J (spinVector (σ 0).1) j)^2 := by
      let f := fun j : Fin (K*n+n) =>
        (cavitySpectralProjection (specialRotation U) J (spinVector (σ 0).1) j)^2
      have hsumimage : (∑ j ∈ Finset.univ.image (fun b : Fin (K+1) => consecutiveProductSite n K b i), f j) =
          ∑ b : Fin (K+1), f (consecutiveProductSite n K b i) := by
        rw [Finset.sum_image]
        exact fun b _ c _ hbc => hinj hbc
      change (∑ b : Fin (K+1), f (consecutiveProductSite n K b i)) ≤ ∑ j, f j
      rw [← hsumimage]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => sq_nonneg _)
    rw [abs_of_nonneg (Finset.sum_nonneg (fun b _ => sq_nonneg _))]
    exact hpart.trans (by
      rw [← EuclideanSpace.real_norm_sq_eq]
      exact (cavitySpectralProjection_norm_sq_le _ J _).trans_eq (spinVector_norm_sq _))
  rw [restrictedCavityFullDisorderTest_sum S hS μ T eig I u F
    (fun b => measurable_cavityProjectionSiteTest J _) (Nat.cast_nonneg (K*n+n))
    (fun b => cavityProjectionSiteTest_bound J _)] at hsum
  change |∑ b, a b| ≤ ((K*n+n : ℕ) : ℝ) at hsum
  simp_rw [he] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hkpos : (0 : ℝ) < (K+1 : ℕ) := Nat.cast_pos.mpr (by omega)
  have hle := (le_abs_self (((K+1 : ℕ) : ℝ) * a b₀)).trans hsum
  push_cast at hle hkpos
  change a b₀ ≤ n
  nlinarith

theorem consecutive_product_projection_axes_mean {n K m depth : ℕ}
    (hn : 0 < n) (hK : 2 ≤ K) (C : Finset (Spin n)) (hC : C.Nonempty)
    (μ : Measure (SpecialOrthogonal (K*n+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin (K*n+n) → ℝ)
    (I : Fin m → Finset (Fin (K*n+n))) (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 2)
    (b₀ : Fin (K+1)) :
    restrictedCavityFullDisorderTest (cavityProductSlice (consecutiveBlockConstraint n K C) C) (cavityProductSlice_nonempty _ (consecutiveBlockConstraint_nonempty C hC) C hC)
      μ T eig I u (cavityProjectionAxesTest I (fun i => consecutiveProductSite n K b₀ i)) ≤
        (m : ℝ) * n * n := by
  change restrictedCavityFullDisorderTest _ _ μ T eig I u
    (fun U σ => ∑ t : Fin m × Fin n,
      cavityProjectionSiteTest (I t.1) (consecutiveProductSite n K b₀ t.2) U σ) ≤ _
  rw [restrictedCavityFullDisorderTest_sum _ _ μ T eig I u
    (fun t : Fin m × Fin n => cavityProjectionSiteTest (I t.1) (consecutiveProductSite n K b₀ t.2))
    (fun t => measurable_cavityProjectionSiteTest _ _)
    (Nat.cast_nonneg (K*n+n)) (fun t => cavityProjectionSiteTest_bound _ _)]
  calc
    _ ≤ ∑ _ : Fin m × Fin n, (n : ℝ) := Finset.sum_le_sum fun t _ =>
      consecutive_product_projection_mean_le hn hK C hC μ T eig I u hu (I t.1) t.2 b₀
    _ = _ := by simp [Fintype.card_prod, Nat.cast_mul, mul_assoc]

theorem consecutive_product_last_axes_mean {n K m depth : ℕ}
    (hn : 0 < n) (hK : 2 ≤ K) (C : Finset (Spin n)) (hC : C.Nonempty)
    (μ : Measure (SpecialOrthogonal (K*n+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin (K*n+n) → ℝ)
    (I : Fin m → Finset (Fin (K*n+n))) (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 2) :
    restrictedCavityFullDisorderTest
      (cavityProductSlice (consecutiveBlockConstraint n K C) C)
      (cavityProductSlice_nonempty _ (consecutiveBlockConstraint_nonempty C hC) C hC)
      μ T eig I u (cavityProjectionAxesTest I (Fin.natAdd (K*n))) ≤ (m : ℝ)*n*n := by
  simpa only [consecutiveProductSite_last] using
    consecutive_product_projection_axes_mean hn hK C hC μ T eig I u hu (Fin.last K)

end InvariantIsing

end

end OAI
