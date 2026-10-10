import OAI.Probability.InvariantIsing.Cavity.ConsecutiveProductPrior
import OAI.Probability.InvariantIsing.Cavity.RepeatedBlockSpinIdentity

namespace OAI

/-! The last constrained block has exactly the full overlap average. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

theorem consecutive_product_spin_identity {n K m depth : ℕ} (hn : 0 < n) (hK : 2 ≤ K)
    (C : Finset (Spin n)) (hC : C.Nonempty)
    (μ : Measure (SpecialOrthogonal (K*n+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin (K*n+n) → ℝ)
    (I : Fin m → Finset (Fin (K*n+n))) (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 2)
    (Φ : ℝ →ᵇ ℝ) (b₀ : Fin (K+1)) :
    restrictedCavityFullDisorderTest (cavityProductSlice (consecutiveBlockConstraint n K C) C) (cavityProductSlice_nonempty _ (consecutiveBlockConstraint_nonempty C hC) C hC)
      μ T eig I u (fun _ σ => Φ (cavityReplicaOverlap σ) *
        ((n : ℝ)⁻¹ * ∑ i : Fin n, spinValue ((σ 0).1 (consecutiveProductSite n K b₀ i)) *
          spinValue ((σ 1).1 (consecutiveProductSite n K b₀ i)))) =
      restrictedCavityFullDisorderTest (cavityProductSlice (consecutiveBlockConstraint n K C) C) (cavityProductSlice_nonempty _ (consecutiveBlockConstraint_nonempty C hC) C hC)
        μ T eig I u (fun _ σ => Φ (cavityReplicaOverlap σ) * cavityReplicaOverlap σ) := by
  have hN : 0 < K*n+n := by omega
  let S := cavityProductSlice (consecutiveBlockConstraint n K C) C
  have hS : S.Nonempty := cavityProductSlice_nonempty _ (consecutiveBlockConstraint_nonempty C hC) C hC
  let F := fun (i : Fin n) (b : Fin (K+1)) (_ : SpecialOrthogonal (K*n+n))
      (σ : Fin 2 → Spin (K*n+n) × LabeledLeaf depth) =>
    Φ (cavityReplicaOverlap σ) * spinValue ((σ 0).1 (consecutiveProductSite n K b i)) *
      spinValue ((σ 1).1 (consecutiveProductSite n K b i))
  let a := fun i b => restrictedCavityFullDisorderTest S hS μ T eig I u (F i b)
  have hF (i : Fin n) (b : Fin (K+1)) (U) (σ) : |F i b U σ| ≤ ‖Φ‖ := by
    simpa only [F, abs_mul, abs_spinValue, mul_one, Real.norm_eq_abs] using
      Φ.norm_coe_le_norm (cavityReplicaOverlap σ)
  have hm (i : Fin n) (b : Fin (K+1)) : Measurable (Function.uncurry (F i b)) :=
    (measurable_of_countable _).comp measurable_snd
  have he (i : Fin n) (b : Fin (K+1)) : a i b = a i b₀ := by
    obtain ⟨p,hp,hpb⟩ := even_block_permutation (by omega : 3 ≤ K+1) b b₀
    have ht := restricted_full_disorder_site_symmetry hN S hS μ T eig I u hu
      (consecutiveProductSitePermutation (n := n) p) (consecutiveProduct_permutation hN C p hp)
      (F i b) (hm i b) (norm_nonneg _) (hF i b)
    change a i b = restrictedCavityFullDisorderTest S hS μ T eig I u _ at ht
    have hf : (fun U σ => F i b (U * (spectralPermutation hN (consecutiveProductSitePermutation p))⁻¹)
        (fun k => (cavitySignedSpinPermutation (consecutiveProductSitePermutation p)
          (cavityPermutationFlip hN (consecutiveProductSitePermutation p)) (σ k).1, (σ k).2))) = F i b₀ := by
      funext U σ
      dsimp only [F]
      rw [cavityReplicaOverlap_signed, mul_assoc, cavitySignedSpinPermutation_pair,
        consecutiveProductSitePermutation_apply, hpb]
      ring
    rw [hf] at ht
    exact ht
  have hblock : (fun (_ : SpecialOrthogonal (K*n+n)) (σ : Fin 2 → Spin (K*n+n) × LabeledLeaf depth) =>
      Φ (cavityReplicaOverlap σ) * ((n : ℝ)⁻¹ * ∑ i : Fin n,
        spinValue ((σ 0).1 (consecutiveProductSite n K b₀ i)) * spinValue ((σ 1).1 (consecutiveProductSite n K b₀ i)))) =
      (fun U σ => (n : ℝ)⁻¹ * ∑ i, F i b₀ U σ) := by
    funext U σ
    simp only [F, mul_assoc, ← Finset.mul_sum]
    ring
  have htotal : (fun (_ : SpecialOrthogonal (K*n+n)) (σ : Fin 2 → Spin (K*n+n) × LabeledLeaf depth) =>
      Φ (cavityReplicaOverlap σ) * cavityReplicaOverlap σ) =
      (fun U σ => ((K*n+n : ℕ) : ℝ)⁻¹ * ∑ i : Fin n, ∑ b : Fin (K+1), F i b U σ) := by
    funext U σ
    have hs : (∑ i : Fin n, ∑ b : Fin (K+1),
        spinValue ((σ 0).1 (consecutiveProductSite n K b i)) * spinValue ((σ 1).1 (consecutiveProductSite n K b i))) =
        ∑ j : Fin (K*n+n), spinValue ((σ 0).1 j) * spinValue ((σ 1).1 j) := by
      let E : Fin (K+1) × Fin n ≃ Fin (K*n+n) :=
        finProdFinEquiv.trans (finCongr (Nat.succ_mul K n))
      calc
        _ = ∑ b : Fin (K+1), ∑ i : Fin n,
            spinValue ((σ 0).1 (consecutiveProductSite n K b i)) *
              spinValue ((σ 1).1 (consecutiveProductSite n K b i)) := Finset.sum_comm
        _ = ∑ x : Fin (K+1) × Fin n,
            spinValue ((σ 0).1 (E x)) * spinValue ((σ 1).1 (E x)) :=
          by
          change (∑ b : Fin (K+1), ∑ i : Fin n,
            spinValue ((σ 0).1 (E (b,i))) * spinValue ((σ 1).1 (E (b,i)))) = _
          exact (Fintype.sum_prod_type (fun x : Fin (K+1) × Fin n =>
            spinValue ((σ 0).1 (E x)) * spinValue ((σ 1).1 (E x)))).symm
        _ = _ := E.sum_comp (fun j : Fin (K*n+n) =>
          spinValue ((σ 0).1 j) * spinValue ((σ 1).1 j))
    simp only [F, mul_assoc, ← Finset.mul_sum]
    rw [hs]
    unfold cavityReplicaOverlap cavityTotalSpinOverlap
    ring
  rw [hblock, htotal, restrictedCavityFullDisorderTest_const_mul,
    restrictedCavityFullDisorderTest_const_mul,
    restrictedCavityFullDisorderTest_sum S hS μ T eig I u (fun i => F i b₀)
      (fun i => hm i b₀) (norm_nonneg _) (fun i => hF i b₀)]
  have hsum (i : Fin n) : restrictedCavityFullDisorderTest S hS μ T eig I u
      (fun U σ => ∑ b, F i b U σ) = ((K+1 : ℕ) : ℝ) * a i b₀ := by
    rw [restrictedCavityFullDisorderTest_sum S hS μ T eig I u (F i) (hm i)
      (norm_nonneg _) (hF i)]
    change (∑ b, a i b) = _
    simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsumBound (i : Fin n) (U) (σ) : |∑ b, F i b U σ| ≤ ((K+1 : ℕ) : ℝ) * ‖Φ‖ := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans (by
      simpa using Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin (K+1)))) => hF i b U σ))
  rw [restrictedCavityFullDisorderTest_sum S hS μ T eig I u (fun i U σ => ∑ b, F i b U σ)
    (fun i => Finset.measurable_sum _ (fun b _ => hm i b))
    (mul_nonneg (Nat.cast_nonneg (K+1)) (norm_nonneg Φ)) hsumBound]
  simp_rw [hsum]
  change (n : ℝ)⁻¹ * (∑ i, a i b₀) = ((K*n+n : ℕ) : ℝ)⁻¹ * ∑ i, ((K+1 : ℕ) : ℝ) * a i b₀
  rw [← Finset.mul_sum]
  push_cast
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hk0 : ((K+1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

end InvariantIsing

end

end OAI
