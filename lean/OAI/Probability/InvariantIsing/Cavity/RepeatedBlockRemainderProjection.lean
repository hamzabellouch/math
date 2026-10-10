import OAI.Probability.InvariantIsing.Cavity.RepeatedBlockRemainderPrior
import OAI.Probability.InvariantIsing.Magnetic.RestrictedDisorderTest
import OAI.Probability.InvariantIsing.Cavity.CavityFullProjectionMoment

namespace OAI

/-! A fixed position in repeated constrained blocks has a projection
moment bounded by the block size, uniformly in the number of blocks. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

theorem repeated_block_remainder_projection_mean_le {n K r m depth : ℕ}
    (hn : 0 < n) (hK : 3 ≤ K) (C : Finset (Spin n)) (hC : C.Nonempty) (R : Finset (Spin r)) (hR : R.Nonempty)
    (μ : Measure (SpecialOrthogonal (n*K+r))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin (n*K+r) → ℝ)
    (I : Fin m → Finset (Fin (n*K+r))) (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 2)
    (J : Finset (Fin (n*K+r))) (i : Fin n) (b₀ : Fin K) :
    restrictedCavityFullDisorderTest (cavityProductSlice (spinBlockConstraint n K C) R)
      (cavityProductSlice_nonempty _ (spinBlockConstraint_nonempty C hC) R hR)
      μ T eig I u (cavityProjectionSiteTest J (Fin.castAdd r (finProdFinEquiv (i,b₀)))) ≤ ((n*K+r : ℕ) : ℝ) / K := by
  have hblock : 0 < n*K := Nat.mul_pos hn (by omega)
  have hN : 0 < n*K+r := Nat.add_pos_left hblock r
  let S := cavityProductSlice (spinBlockConstraint n K C) R
  have hS : S.Nonempty := cavityProductSlice_nonempty _ (spinBlockConstraint_nonempty C hC) R hR
  let F := fun b : Fin K => cavityProjectionSiteTest (depth := depth) J (Fin.castAdd r (finProdFinEquiv (i,b)))
  let a := fun b => restrictedCavityFullDisorderTest S hS μ T eig I u (F b)
  have he (b : Fin K) : a b = a b₀ := by
    obtain ⟨p,hp,hpb⟩ := even_block_permutation hK b b₀
    have ht := restricted_full_disorder_site_symmetry hN S hS μ T eig I u hu
      (blockRemainderSitePermutation (n := n) p) (block_remainder_constraint_permutation hblock C R p hp)
      (F b) (measurable_cavityProjectionSiteTest J _) (Nat.cast_nonneg (n*K+r))
      (cavityProjectionSiteTest_bound J _)
    change a b = restrictedCavityFullDisorderTest S hS μ T eig I u _ at ht
    have hf : (fun U σ => F b (U * (spectralPermutation hN (blockRemainderSitePermutation p))⁻¹)
        (fun k => (cavitySignedSpinPermutation (blockRemainderSitePermutation p)
          (cavityPermutationFlip hN (blockRemainderSitePermutation p)) (σ k).1, (σ k).2))) = F b₀ := by
      funext U σ
      simp only [F, cavityProjectionSiteTest, cavitySpectralProjection_permutation_sq,
        blockRemainderSitePermutation_left, spinBlockSitePermutation_apply, hpb]
    rw [hf] at ht
    exact ht
  have hsum : |restrictedCavityFullDisorderTest S hS μ T eig I u
      (fun U σ => ∑ b, F b U σ)| ≤ ((n*K+r : ℕ) : ℝ) := by
    apply restrictedCavityFullDisorderTest_abs_le S hS μ T eig I u _
      (Finset.measurable_sum _ fun b _ => measurable_cavityProjectionSiteTest J _)
      (Nat.cast_nonneg (n*K+r))
    intro U σ
    have hinj : Function.Injective (fun b : Fin K => Fin.castAdd r (finProdFinEquiv (i,b))) := by
      intro b c hbc
      exact congrArg Prod.snd (finProdFinEquiv.injective (Fin.castAdd_inj.mp hbc))
    have hpart : (∑ b, F b U σ) ≤ ∑ j : Fin (n*K+r),
        (cavitySpectralProjection (specialRotation U) J (spinVector (σ 0).1) j)^2 := by
      let f := fun j : Fin (n*K+r) =>
        (cavitySpectralProjection (specialRotation U) J (spinVector (σ 0).1) j)^2
      have hsumimage : (∑ j ∈ Finset.univ.image (fun b : Fin K => Fin.castAdd r (finProdFinEquiv (i,b))), f j) =
          ∑ b : Fin K, f (Fin.castAdd r (finProdFinEquiv (i,b))) := by
        rw [Finset.sum_image]
        exact fun b _ c _ hbc => hinj hbc
      change (∑ b : Fin K, f (Fin.castAdd r (finProdFinEquiv (i,b)))) ≤ ∑ j, f j
      rw [← hsumimage]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => sq_nonneg _)
    rw [abs_of_nonneg (Finset.sum_nonneg (fun b _ => sq_nonneg _))]
    exact hpart.trans (by
      rw [← EuclideanSpace.real_norm_sq_eq]
      exact (cavitySpectralProjection_norm_sq_le _ J _).trans_eq (spinVector_norm_sq _))
  rw [restrictedCavityFullDisorderTest_sum S hS μ T eig I u F
    (fun b => measurable_cavityProjectionSiteTest J _) (Nat.cast_nonneg (n*K+r))
    (fun b => cavityProjectionSiteTest_bound J _)] at hsum
  simp only [Nat.cast_add, Nat.cast_mul] at hsum
  change |∑ b, a b| ≤ n*K+r at hsum
  simp_rw [he] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hkpos : (0 : ℝ) < K := Nat.cast_pos.mpr (by omega)
  have hle := (le_abs_self ((K : ℝ) * a b₀)).trans hsum
  change a b₀ ≤ ((n*K+r : ℕ) : ℝ) / K
  apply (le_div_iff₀ hkpos).mpr
  simp only [Nat.cast_add, Nat.cast_mul]
  nlinarith

end InvariantIsing

end

end OAI
