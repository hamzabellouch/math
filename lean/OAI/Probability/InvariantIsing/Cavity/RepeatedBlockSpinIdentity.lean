import OAI.Probability.InvariantIsing.Cavity.RepeatedBlockPrior
import OAI.Probability.InvariantIsing.Magnetic.RestrictedDisorderTest
import OAI.Probability.InvariantIsing.Cavity.CavityFullSiteIdentity

namespace OAI

/-! Averaging the two-spin test over one constrained block equals its
average over every site, and hence the total-overlap test. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma restrictedCavityFullDisorderTest_const_mul {N m depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (μ : Measure (SpecialOrthogonal N))
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ) (c : ℝ) :
    restrictedCavityFullDisorderTest S hS μ T eig I u (fun U σ => c * F U σ) =
      c * restrictedCavityFullDisorderTest S hS μ T eig I u F := by
  simp only [restrictedCavityFullDisorderTest, referenceReplicaMean_const_mul, integral_const_mul]

theorem repeated_block_spin_identity {n K m depth : ℕ} (hn : 0 < n) (hK : 3 ≤ K)
    (C : Finset (Spin n)) (hC : C.Nonempty)
    (μ : Measure (SpecialOrthogonal (n*K))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin (n*K) → ℝ)
    (I : Fin m → Finset (Fin (n*K))) (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 2)
    (Φ : ℝ →ᵇ ℝ) (b₀ : Fin K) :
    restrictedCavityFullDisorderTest (spinBlockConstraint n K C) (spinBlockConstraint_nonempty C hC)
      μ T eig I u (fun _ σ => Φ (cavityReplicaOverlap σ) *
        ((n : ℝ)⁻¹ * ∑ i : Fin n, spinValue ((σ 0).1 (finProdFinEquiv (i,b₀))) *
          spinValue ((σ 1).1 (finProdFinEquiv (i,b₀))))) =
      restrictedCavityFullDisorderTest (spinBlockConstraint n K C) (spinBlockConstraint_nonempty C hC)
        μ T eig I u (fun _ σ => Φ (cavityReplicaOverlap σ) * cavityReplicaOverlap σ) := by
  have hN : 0 < n*K := Nat.mul_pos hn (by omega)
  let S := spinBlockConstraint n K C
  have hS : S.Nonempty := spinBlockConstraint_nonempty C hC
  let F := fun (i : Fin n) (b : Fin K) (_ : SpecialOrthogonal (n*K))
      (σ : Fin 2 → Spin (n*K) × LabeledLeaf depth) =>
    Φ (cavityReplicaOverlap σ) * spinValue ((σ 0).1 (finProdFinEquiv (i,b))) *
      spinValue ((σ 1).1 (finProdFinEquiv (i,b)))
  let a := fun i b => restrictedCavityFullDisorderTest S hS μ T eig I u (F i b)
  have hF (i : Fin n) (b : Fin K) (U) (σ) : |F i b U σ| ≤ ‖Φ‖ := by
    simpa only [F, abs_mul, abs_spinValue, mul_one, Real.norm_eq_abs] using
      Φ.norm_coe_le_norm (cavityReplicaOverlap σ)
  have hm (i : Fin n) (b : Fin K) : Measurable (Function.uncurry (F i b)) :=
    (measurable_of_countable _).comp measurable_snd
  have he (i : Fin n) (b : Fin K) : a i b = a i b₀ := by
    obtain ⟨p,hp,hpb⟩ := even_block_permutation hK b b₀
    have ht := restricted_full_disorder_site_symmetry hN S hS μ T eig I u hu
      (spinBlockSitePermutation (n := n) p) (spinBlockConstraint_permutation hN C p hp)
      (F i b) (hm i b) (norm_nonneg _) (hF i b)
    change a i b = restrictedCavityFullDisorderTest S hS μ T eig I u _ at ht
    have hf : (fun U σ => F i b (U * (spectralPermutation hN (spinBlockSitePermutation p))⁻¹)
        (fun k => (cavitySignedSpinPermutation (spinBlockSitePermutation p)
          (cavityPermutationFlip hN (spinBlockSitePermutation p)) (σ k).1, (σ k).2))) = F i b₀ := by
      funext U σ
      dsimp only [F]
      rw [cavityReplicaOverlap_signed, mul_assoc, cavitySignedSpinPermutation_pair,
        spinBlockSitePermutation_apply, hpb]
      ring
    rw [hf] at ht
    exact ht
  have hblock : (fun (_ : SpecialOrthogonal (n*K)) (σ : Fin 2 → Spin (n*K) × LabeledLeaf depth) =>
      Φ (cavityReplicaOverlap σ) * ((n : ℝ)⁻¹ * ∑ i : Fin n,
        spinValue ((σ 0).1 (finProdFinEquiv (i,b₀))) * spinValue ((σ 1).1 (finProdFinEquiv (i,b₀))))) =
      (fun U σ => (n : ℝ)⁻¹ * ∑ i, F i b₀ U σ) := by
    funext U σ
    simp only [F, mul_assoc, ← Finset.mul_sum]
    ring
  have htotal : (fun (_ : SpecialOrthogonal (n*K)) (σ : Fin 2 → Spin (n*K) × LabeledLeaf depth) =>
      Φ (cavityReplicaOverlap σ) * cavityReplicaOverlap σ) =
      (fun U σ => ((n*K : ℕ) : ℝ)⁻¹ * ∑ i : Fin n, ∑ b : Fin K, F i b U σ) := by
    funext U σ
    have hs : (∑ i : Fin n, ∑ b : Fin K,
        spinValue ((σ 0).1 (finProdFinEquiv (i,b))) * spinValue ((σ 1).1 (finProdFinEquiv (i,b)))) =
        ∑ j : Fin (n*K), spinValue ((σ 0).1 j) * spinValue ((σ 1).1 j) := by
      have hh := Fintype.sum_prod_type (fun p : Fin n × Fin K =>
        spinValue ((σ 0).1 (finProdFinEquiv p)) * spinValue ((σ 1).1 (finProdFinEquiv p)))
      exact hh.symm.trans (finProdFinEquiv.sum_comp (fun j : Fin (n*K) =>
        spinValue ((σ 0).1 j) * spinValue ((σ 1).1 j)))
    simp only [F, mul_assoc, ← Finset.mul_sum]
    rw [hs]
    unfold cavityReplicaOverlap cavityTotalSpinOverlap
    ring
  rw [hblock, htotal, restrictedCavityFullDisorderTest_const_mul,
    restrictedCavityFullDisorderTest_const_mul,
    restrictedCavityFullDisorderTest_sum S hS μ T eig I u (fun i => F i b₀)
      (fun i => hm i b₀) (norm_nonneg _) (fun i => hF i b₀)]
  have hsum (i : Fin n) : restrictedCavityFullDisorderTest S hS μ T eig I u
      (fun U σ => ∑ b, F i b U σ) = (K : ℝ) * a i b₀ := by
    rw [restrictedCavityFullDisorderTest_sum S hS μ T eig I u (F i) (hm i)
      (norm_nonneg _) (hF i)]
    change (∑ b, a i b) = _
    simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsumBound (i : Fin n) (U) (σ) : |∑ b, F i b U σ| ≤ (K : ℝ) * ‖Φ‖ := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans (by
      simpa using Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin K))) => hF i b U σ))
  rw [restrictedCavityFullDisorderTest_sum S hS μ T eig I u (fun i U σ => ∑ b, F i b U σ)
    (fun i => Finset.measurable_sum _ (fun b _ => hm i b))
    (mul_nonneg (Nat.cast_nonneg K) (norm_nonneg Φ)) hsumBound]
  simp_rw [hsum]
  change (n : ℝ)⁻¹ * (∑ i, a i b₀) = ((n*K : ℕ) : ℝ)⁻¹ * ∑ i, (K : ℝ) * a i b₀
  rw [← Finset.mul_sum, Nat.cast_mul]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hk0 : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

end InvariantIsing

end

end OAI
