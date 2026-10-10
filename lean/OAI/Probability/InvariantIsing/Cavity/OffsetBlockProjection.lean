import OAI.Probability.InvariantIsing.Cavity.OffsetBlockSymmetry
import OAI.Probability.InvariantIsing.Magnetic.RestrictedDisorderTest
import OAI.Probability.InvariantIsing.Cavity.CavityFullProjectionMoment

namespace OAI

/-! A fixed position in repeated constrained blocks has a projection
moment bounded by the block size, uniformly in the number of blocks. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

theorem offset_block_projection_mean_le {n K r m depth : ℕ}
    (hn : 0 < n) (hK : 3 ≤ K) (C : Finset (Spin n)) (hC : C.Nonempty) (R : Finset (Spin r)) (hR : R.Nonempty)
    (μ : Measure (SpecialOrthogonal (r+K*n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin (r+K*n) → ℝ)
    (I : Fin m → Finset (Fin (r+K*n))) (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 2)
    (J : Finset (Fin (r+K*n))) (i : Fin n) (b₀ : Fin K) :
    restrictedCavityFullDisorderTest (offsetBlockConstraint K R C)
      (offsetBlockConstraint_nonempty R hR C hC)
      μ T eig I u (cavityProjectionSiteTest J (Fin.natAdd r (finProdFinEquiv (b₀,i)))) ≤ ((r+K*n : ℕ) : ℝ) / K := by
  have hblock : 0 < K*n := Nat.mul_pos (by omega) hn
  have hN : 0 < r+K*n := Nat.add_pos_right r hblock
  let S := offsetBlockConstraint K R C
  have hS : S.Nonempty := offsetBlockConstraint_nonempty R hR C hC
  let F := fun b : Fin K => cavityProjectionSiteTest (depth := depth) J (Fin.natAdd r (finProdFinEquiv (b,i)))
  let a := fun b => restrictedCavityFullDisorderTest S hS μ T eig I u (F b)
  have he (b : Fin K) : a b = a b₀ := by
    obtain ⟨p,hp,hpb⟩ := even_block_permutation hK b b₀
    have ht := restricted_full_disorder_site_symmetry hN S hS μ T eig I u hu
      (offsetBlockSitePermutation (n := n) p) (offsetBlockConstraint_permutation hblock R C p hp)
      (F b) (measurable_cavityProjectionSiteTest J _) (Nat.cast_nonneg (r+K*n))
      (cavityProjectionSiteTest_bound J _)
    change a b = restrictedCavityFullDisorderTest S hS μ T eig I u _ at ht
    have hf : (fun U σ => F b (U * (spectralPermutation hN (offsetBlockSitePermutation p))⁻¹)
        (fun k => (cavitySignedSpinPermutation (offsetBlockSitePermutation p)
          (cavityPermutationFlip hN (offsetBlockSitePermutation p)) (σ k).1, (σ k).2))) = F b₀ := by
      funext U σ
      simp only [F, cavityProjectionSiteTest, cavitySpectralProjection_permutation_sq,
        offsetBlockSitePermutation_block, consecutiveBlockSitePermutation_apply, hpb]
    rw [hf] at ht
    exact ht
  have hsum : |restrictedCavityFullDisorderTest S hS μ T eig I u
      (fun U σ => ∑ b, F b U σ)| ≤ ((r+K*n : ℕ) : ℝ) := by
    apply restrictedCavityFullDisorderTest_abs_le S hS μ T eig I u _
      (Finset.measurable_sum _ fun b _ => measurable_cavityProjectionSiteTest J _)
      (Nat.cast_nonneg (r+K*n))
    intro U σ
    have hinj : Function.Injective (fun b : Fin K => Fin.natAdd r (finProdFinEquiv (b,i))) := by
      intro b c hbc
      exact congrArg Prod.fst (finProdFinEquiv.injective (Fin.ext (by simpa only [Fin.val_natAdd, Nat.add_left_cancel_iff] using congrArg Fin.val hbc)))
    have hpart : (∑ b, F b U σ) ≤ ∑ j : Fin (r+K*n),
        (cavitySpectralProjection (specialRotation U) J (spinVector (σ 0).1) j)^2 := by
      let f := fun j : Fin (r+K*n) =>
        (cavitySpectralProjection (specialRotation U) J (spinVector (σ 0).1) j)^2
      have hsumimage : (∑ j ∈ Finset.univ.image (fun b : Fin K => Fin.natAdd r (finProdFinEquiv (b,i))), f j) =
          ∑ b : Fin K, f (Fin.natAdd r (finProdFinEquiv (b,i))) := by
        rw [Finset.sum_image]
        exact fun b _ c _ hbc => hinj hbc
      change (∑ b : Fin K, f (Fin.natAdd r (finProdFinEquiv (b,i)))) ≤ ∑ j, f j
      rw [← hsumimage]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => sq_nonneg _)
    rw [abs_of_nonneg (Finset.sum_nonneg (fun b _ => sq_nonneg _))]
    exact hpart.trans (by
      rw [← EuclideanSpace.real_norm_sq_eq]
      exact (cavitySpectralProjection_norm_sq_le _ J _).trans_eq (spinVector_norm_sq _))
  rw [restrictedCavityFullDisorderTest_sum S hS μ T eig I u F
    (fun b => measurable_cavityProjectionSiteTest J _) (Nat.cast_nonneg (r+K*n))
    (fun b => cavityProjectionSiteTest_bound J _)] at hsum
  simp only [Nat.cast_add, Nat.cast_mul] at hsum
  change |∑ b, a b| ≤ r+K*n at hsum
  simp_rw [he] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hkpos : (0 : ℝ) < K := Nat.cast_pos.mpr (by omega)
  have hle := (le_abs_self ((K : ℝ) * a b₀)).trans hsum
  change a b₀ ≤ ((r+K*n : ℕ) : ℝ) / K
  apply (le_div_iff₀ hkpos).mpr
  simp only [Nat.cast_add, Nat.cast_mul]
  nlinarith

end InvariantIsing

end

end OAI
