import OAI.Probability.InvariantIsing.Cavity.OffsetBlockSymmetry
import OAI.Probability.InvariantIsing.Magnetic.RestrictedFullTail
import OAI.Probability.InvariantIsing.Cavity.CavityPrefixOverlap

namespace OAI

/-! Repeated-block spin averaging with an arbitrary fixed remainder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

def offsetRegularBlockOverlap {n K r depth : ℕ}
    (σ : Fin 2 → Spin (r+K*n) × LabeledLeaf depth) : ℝ :=
  cavityTotalSpinOverlap ((cavitySpinSplit r (K*n) (σ 0).1).2,
    (cavitySpinSplit r (K*n) (σ 1).1).2)

theorem offset_block_spin_identity {n K r m depth : ℕ} (hn : 0 < n) (hK : 3 ≤ K)
    (C : Finset (Spin n)) (hC : C.Nonempty) (R : Finset (Spin r)) (hR : R.Nonempty)
    (μ : Measure (SpecialOrthogonal (r+K*n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin (r+K*n) → ℝ)
    (I : Fin m → Finset (Fin (r+K*n))) (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 2)
    (Φ : ℝ →ᵇ ℝ) (b₀ : Fin K) :
    restrictedCavityFullDisorderTest (offsetBlockConstraint K R C)
      (offsetBlockConstraint_nonempty R hR C hC)
      μ T eig I u (fun _ σ => Φ (cavityReplicaOverlap σ) *
        ((n : ℝ)⁻¹ * ∑ i : Fin n, spinValue ((σ 0).1 (Fin.natAdd r (finProdFinEquiv (b₀,i)))) *
          spinValue ((σ 1).1 (Fin.natAdd r (finProdFinEquiv (b₀,i)))))) =
      restrictedCavityFullDisorderTest (offsetBlockConstraint K R C)
      (offsetBlockConstraint_nonempty R hR C hC)
        μ T eig I u (fun _ σ => Φ (cavityReplicaOverlap σ) * offsetRegularBlockOverlap σ) := by
  have hblock : 0 < K*n := Nat.mul_pos (by omega) hn
  have hN : 0 < r+K*n := Nat.add_pos_right r hblock
  let S := offsetBlockConstraint K R C
  have hS : S.Nonempty := offsetBlockConstraint_nonempty R hR C hC
  let F := fun (i : Fin n) (b : Fin K) (_ : SpecialOrthogonal (r+K*n))
      (σ : Fin 2 → Spin (r+K*n) × LabeledLeaf depth) =>
    Φ (cavityReplicaOverlap σ) * spinValue ((σ 0).1 (Fin.natAdd r (finProdFinEquiv (b,i)))) *
      spinValue ((σ 1).1 (Fin.natAdd r (finProdFinEquiv (b,i))))
  let a := fun i b => restrictedCavityFullDisorderTest S hS μ T eig I u (F i b)
  have hF (i : Fin n) (b : Fin K) (U) (σ) : |F i b U σ| ≤ ‖Φ‖ := by
    simpa only [F, abs_mul, abs_spinValue, mul_one, Real.norm_eq_abs] using
      Φ.norm_coe_le_norm (cavityReplicaOverlap σ)
  have hm (i : Fin n) (b : Fin K) : Measurable (Function.uncurry (F i b)) :=
    (measurable_of_countable _).comp measurable_snd
  have he (i : Fin n) (b : Fin K) : a i b = a i b₀ := by
    obtain ⟨p,hp,hpb⟩ := even_block_permutation hK b b₀
    have ht := restricted_full_disorder_site_symmetry hN S hS μ T eig I u hu
      (offsetBlockSitePermutation (n := n) p) (offsetBlockConstraint_permutation hblock R C p hp)
      (F i b) (hm i b) (norm_nonneg _) (hF i b)
    change a i b = restrictedCavityFullDisorderTest S hS μ T eig I u _ at ht
    have hf : (fun U σ => F i b (U * (spectralPermutation hN (offsetBlockSitePermutation p))⁻¹)
        (fun k => (cavitySignedSpinPermutation (offsetBlockSitePermutation p)
          (cavityPermutationFlip hN (offsetBlockSitePermutation p)) (σ k).1, (σ k).2))) = F i b₀ := by
      funext U σ
      dsimp only [F]
      rw [cavityReplicaOverlap_signed, mul_assoc, cavitySignedSpinPermutation_pair,
        offsetBlockSitePermutation_block, consecutiveBlockSitePermutation_apply, hpb]
      ring
    rw [hf] at ht
    exact ht
  have hblock : (fun (_ : SpecialOrthogonal (r+K*n)) (σ : Fin 2 → Spin (r+K*n) × LabeledLeaf depth) =>
      Φ (cavityReplicaOverlap σ) * ((n : ℝ)⁻¹ * ∑ i : Fin n,
        spinValue ((σ 0).1 (Fin.natAdd r (finProdFinEquiv (b₀,i)))) * spinValue ((σ 1).1 (Fin.natAdd r (finProdFinEquiv (b₀,i)))))) =
      (fun U σ => (n : ℝ)⁻¹ * ∑ i, F i b₀ U σ) := by
    funext U σ
    simp only [F, mul_assoc, ← Finset.mul_sum]
    ring
  have htotal : (fun (_ : SpecialOrthogonal (r+K*n)) (σ : Fin 2 → Spin (r+K*n) × LabeledLeaf depth) =>
      Φ (cavityReplicaOverlap σ) * offsetRegularBlockOverlap σ) =
      (fun U σ => ((K*n : ℕ) : ℝ)⁻¹ * ∑ i : Fin n, ∑ b : Fin K, F i b U σ) := by
    funext U σ
    have hs : (∑ i : Fin n, ∑ b : Fin K,
        spinValue ((σ 0).1 (Fin.natAdd r (finProdFinEquiv (b,i)))) * spinValue ((σ 1).1 (Fin.natAdd r (finProdFinEquiv (b,i))))) =
        ∑ j : Fin (K*n), spinValue ((σ 0).1 (Fin.natAdd r j)) * spinValue ((σ 1).1 (Fin.natAdd r j)) := by
      rw [Finset.sum_comm]
      exact (Fintype.sum_prod_type (fun p : Fin K × Fin n =>
        spinValue ((σ 0).1 (Fin.natAdd r (finProdFinEquiv p))) *
        spinValue ((σ 1).1 (Fin.natAdd r (finProdFinEquiv p))))).symm.trans
          (finProdFinEquiv.sum_comp (fun j : Fin (K*n) =>
            spinValue ((σ 0).1 (Fin.natAdd r j)) * spinValue ((σ 1).1 (Fin.natAdd r j))))
    simp only [F, mul_assoc, ← Finset.mul_sum]
    rw [hs]
    unfold offsetRegularBlockOverlap cavityTotalSpinOverlap
    simp only [cavitySpinSplit_right]
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
  change (n : ℝ)⁻¹ * (∑ i, a i b₀) = ((K*n : ℕ) : ℝ)⁻¹ * ∑ i, (K : ℝ) * a i b₀
  rw [← Finset.mul_sum, Nat.cast_mul]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hk0 : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp


lemma abs_offsetRegularBlockOverlap_le {n K r depth : ℕ}
    (σ : Fin 2 → Spin (r+K*n) × LabeledLeaf depth) :
    |offsetRegularBlockOverlap σ| ≤ 1 := abs_cavityTotalSpinOverlap_le _

lemma offsetRegularBlockOverlap_error {n K r depth : ℕ} (hN : 0 < K*n)
    (σ : Fin 2 → Spin (r+K*n) × LabeledLeaf depth) :
    |offsetRegularBlockOverlap σ - cavityReplicaOverlap σ| ≤ 2*(r:ℝ)/(r+K*n) := by
  simpa only [offsetRegularBlockOverlap, cavityReplicaOverlap, abs_sub_comm, Nat.cast_mul] using
    cavity_spin_split_right_overlap_error hN (σ 0).1 (σ 1).1

theorem offset_block_spin_error {n K r m depth : ℕ}
    (hn : 0 < n) (hK : 3 ≤ K) (C : Finset (Spin n)) (hC : C.Nonempty)
    (R : Finset (Spin r)) (hR : R.Nonempty)
    (μ : Measure (SpecialOrthogonal (r+K*n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin (r+K*n) → ℝ)
    (I : Fin m → Finset (Fin (r+K*n))) (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 2)
    (Φ : ℝ →ᵇ ℝ) (b₀ : Fin K) :
    |restrictedCavityFullDisorderTest (offsetBlockConstraint K R C)
        (offsetBlockConstraint_nonempty R hR C hC)
        μ T eig I u (fun _ σ => Φ (cavityReplicaOverlap σ) *
          ((n:ℝ)⁻¹ * ∑ i : Fin n,
            spinValue ((σ 0).1 (Fin.natAdd r (finProdFinEquiv (b₀,i)))) *
            spinValue ((σ 1).1 (Fin.natAdd r (finProdFinEquiv (b₀,i)))))) -
      restrictedCavityFullDisorderTest (offsetBlockConstraint K R C)
        (offsetBlockConstraint_nonempty R hR C hC)
        μ T eig I u (fun _ σ => Φ (cavityReplicaOverlap σ) * cavityReplicaOverlap σ)| ≤
      ‖Φ‖ * (2*(r:ℝ)/(r+K*n)) := by
  rw [offset_block_spin_identity hn hK C hC R hR μ T eig I u hu Φ b₀]
  let S := offsetBlockConstraint K R C
  have hS : S.Nonempty := offsetBlockConstraint_nonempty R hR C hC
  let F := fun (_ : SpecialOrthogonal (r+K*n)) (σ : Fin 2 → Spin (r+K*n) × LabeledLeaf depth) =>
    Φ (cavityReplicaOverlap σ) * offsetRegularBlockOverlap σ
  let G := fun (_ : SpecialOrthogonal (r+K*n)) (σ : Fin 2 → Spin (r+K*n) × LabeledLeaf depth) =>
    Φ (cavityReplicaOverlap σ) * cavityReplicaOverlap σ
  have hmF : Measurable (Function.uncurry F) := (measurable_of_countable _).comp measurable_snd
  have hmG : Measurable (Function.uncurry G) := (measurable_of_countable _).comp measurable_snd
  have hF : ∀ U σ, |F U σ| ≤ ‖Φ‖ := by
    intro U σ
    rw [abs_mul]
    exact (mul_le_mul (by simpa only [Real.norm_eq_abs] using Φ.norm_coe_le_norm (cavityReplicaOverlap σ))
      (abs_offsetRegularBlockOverlap_le σ) (abs_nonneg _) (norm_nonneg _)).trans_eq (mul_one _)
  have hG : ∀ U σ, |G U σ| ≤ ‖Φ‖ := by
    intro U σ
    rw [abs_mul]
    exact (mul_le_mul (by simpa only [Real.norm_eq_abs] using Φ.norm_coe_le_norm (cavityReplicaOverlap σ))
      (abs_cavityTotalSpinOverlap_le _) (abs_nonneg _) (norm_nonneg _)).trans_eq (mul_one _)
  change |restrictedCavityFullDisorderTest S hS μ T eig I u F -
    restrictedCavityFullDisorderTest S hS μ T eig I u G| ≤ _
  rw [← restrictedCavityFullDisorderTest_sub S hS μ T eig I u F G hmF hmG (norm_nonneg _) hF hG]
  apply restrictedCavityFullDisorderTest_abs_le S hS μ T eig I u (fun U σ => F U σ - G U σ) (hmF.sub hmG)
    (mul_nonneg (norm_nonneg _) (by positivity))
  intro U σ
  change |Φ (cavityReplicaOverlap σ) * offsetRegularBlockOverlap σ -
    Φ (cavityReplicaOverlap σ) * cavityReplicaOverlap σ| ≤ _
  rw [← mul_sub, abs_mul]
  exact mul_le_mul (by simpa only [Real.norm_eq_abs] using Φ.norm_coe_le_norm (cavityReplicaOverlap σ))
    (offsetRegularBlockOverlap_error (Nat.mul_pos (by omega) hn) σ) (abs_nonneg _) (norm_nonneg _)

end InvariantIsing

end

end OAI
