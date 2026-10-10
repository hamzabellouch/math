import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingEstimates

namespace OAI

open scoped BigOperators

namespace InvariantRotation.SamplingMomentBounds

theorem abs_prod_le_pow_card {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {M : ℝ} (_hM : 0 ≤ M) (hf : ∀ i ∈ s, |f i| ≤ M) :
    |∏ i ∈ s, f i| ≤ M ^ s.card := by
  rw [Finset.abs_prod]
  calc
    ∏ i ∈ s, |f i| ≤ ∏ _i ∈ s, M :=
      Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) hf
    _ = M ^ s.card := by simp

theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hf : ∀ i ∈ s, |f i| ≤ M) (hg : ∀ i ∈ s, |g i| ≤ M)
    (hfg : ∀ i ∈ s, |f i - g i| ≤ ε) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤
      (s.card : ℝ) * ε * M ^ (s.card - 1) := by
  exact Invariant233.ProductSampling.abs_prod_sub_prod_le s f g hM hε hf hg hfg

theorem product_perturbation_bound {ι : Type*} (s : Finset ι) (A e : ι → ℝ)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hA : ∀ i ∈ s, 0 ≤ A i) (hAB : ∀ i ∈ s, A i ≤ B)
    (he : ∀ i ∈ s, |e i| ≤ ε) :
    |(∏ i ∈ s, (A i + e i)) - ∏ i ∈ s, A i| ≤
      (s.card : ℝ) * ε * (B + ε) ^ (s.card - 1) := by
  exact Invariant233.ProductSampling.abs_prod_add_error_sub_prod_le s A e hB hε
    (fun i hi => ⟨hA i hi, hAB i hi⟩) he

theorem product_perturbation_bound_exp {ι : Type*} (s : Finset ι) (A e : ι → ℝ)
    {β ε C : ℝ} (hβ : 0 ≤ β) (hε : 0 ≤ ε)
    (hA : ∀ i ∈ s, 0 ≤ A i) (hAB : ∀ i ∈ s, A i ≤ 1 + β)
    (he : ∀ i ∈ s, |e i| ≤ ε) (hC : (s.card : ℝ) * (β + ε) ≤ C) :
    |(∏ i ∈ s, (A i + e i)) - ∏ i ∈ s, A i| ≤
      (s.card : ℝ) * ε * Real.exp C := by
  have h := product_perturbation_bound s A e (by positivity : 0 ≤ 1 + β) hε hA hAB he
  have hbase : 1 + β + ε ≤ Real.exp (β + ε) := by
    simpa only [add_assoc, add_comm, add_left_comm] using Real.add_one_le_exp (β + ε)
  have hpow : (1 + β + ε) ^ (s.card - 1) ≤ Real.exp C := by
    calc
      (1 + β + ε) ^ (s.card - 1) ≤ (Real.exp (β + ε)) ^ (s.card - 1) :=
        pow_le_pow_left₀ (by positivity) hbase _
      _ = Real.exp ((s.card - 1 : ℕ) * (β + ε)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp C := by
        apply Real.exp_le_exp.mpr
        refine le_trans ?_ hC
        apply mul_le_mul_of_nonneg_right _ (add_nonneg hβ hε)
        exact_mod_cast Nat.sub_le s.card 1
  exact h.trans (mul_le_mul_of_nonneg_left hpow (by positivity))

theorem averaged_moment_bound {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (Q : ι → ι → ℝ) (C : ι → ℝ) {A D ε : ℝ}
    (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hdiag : ∀ i ∈ s, Q i i ≤ D)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Q i j ≤ A + ε)
    (hcross : ∀ i ∈ s, A - ε ≤ C i) :
    ((s.card : ℝ)⁻¹) ^ 2 * (∑ i ∈ s, ∑ j ∈ s, Q i j) -
        2 * (s.card : ℝ)⁻¹ * (∑ i ∈ s, C i) + A ≤
      D / (s.card : ℝ) + 3 * ε := by
  classical
  let P : ℝ := s.card
  have hn : 0 < s.card := Finset.card_pos.mpr hs
  have hP : 0 < P := by
    dsimp [P]
    exact_mod_cast hn
  have hP0 : P ≠ 0 := ne_of_gt hP
  have hrow (i : ι) (hi : i ∈ s) :
      (∑ j ∈ s, Q i j) ≤ D + (P - 1) * (A + ε) := by
    calc
      (∑ j ∈ s, Q i j) = Q i i + ∑ j ∈ s.erase i, Q i j := by
        rw [← Finset.sum_erase_add s (Q i) hi, add_comm]
      _ ≤ D + ∑ _j ∈ s.erase i, (A + ε) := by
        apply add_le_add (hdiag i hi)
        apply Finset.sum_le_sum
        intro j hj
        exact hoff i hi j (Finset.mem_of_mem_erase hj)
          (Ne.symm (Finset.ne_of_mem_erase hj))
      _ = D + (P - 1) * (A + ε) := by
        simp [P, Finset.card_erase_of_mem hi, Nat.cast_sub (Nat.succ_le_of_lt hn)]
        ring
  have hsum : (∑ i ∈ s, ∑ j ∈ s, Q i j) ≤
      P * D + P * (P - 1) * (A + ε) := by
    calc
      (∑ i ∈ s, ∑ j ∈ s, Q i j) ≤ ∑ _i ∈ s, (D + (P - 1) * (A + ε)) :=
        Finset.sum_le_sum hrow
      _ = P * D + P * (P - 1) * (A + ε) := by simp [P]; ring
  have hc : P * (A - ε) ≤ ∑ i ∈ s, C i := by
    calc
      P * (A - ε) = ∑ _i ∈ s, (A - ε) := by simp [P]; ring
      _ ≤ ∑ i ∈ s, C i := Finset.sum_le_sum hcross
  change (P⁻¹) ^ 2 * (∑ i ∈ s, ∑ j ∈ s, Q i j) -
    2 * P⁻¹ * (∑ i ∈ s, C i) + A ≤ D / P + 3 * ε
  calc
    _ ≤ (P⁻¹) ^ 2 * (P * D + P * (P - 1) * (A + ε)) -
        2 * P⁻¹ * (P * (A - ε)) + A := by
      have h1 := mul_le_mul_of_nonneg_left hsum (sq_nonneg (P⁻¹))
      have h2 := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2 * P⁻¹ by positivity)
      linarith
    _ = D / P + 3 * ε - (A + ε) / P := by field_simp; ring
    _ ≤ D / P + 3 * ε := sub_le_self _ (div_nonneg (add_nonneg hA hε) hP.le)

theorem norm_average_sub_sq_le {ι E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] (s : Finset ι) (hs : s.Nonempty)
    (v : ι → E) (z : E) {D ε : ℝ} (hε : 0 ≤ ε)
    (hdiag : ∀ i ∈ s, ‖v i‖ ^ 2 ≤ D)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℝ (v i) (v j) ≤ ‖z‖ ^ 2 + ε)
    (hcross : ∀ i ∈ s, ‖z‖ ^ 2 - ε ≤ inner ℝ (v i) z) :
    ‖(s.card : ℝ)⁻¹ • (∑ i ∈ s, v i) - z‖ ^ 2 ≤
      D / (s.card : ℝ) + 3 * ε := by
  have h := averaged_moment_bound s hs (fun i j => inner ℝ (v i) (v j))
    (fun i => inner ℝ (v i) z) (sq_nonneg ‖z‖) hε
    (by simpa only [real_inner_self_eq_norm_sq] using hdiag) hoff hcross
  have hn : ‖(s.card : ℝ)⁻¹ • (∑ i ∈ s, v i)‖ ^ 2 =
      ((s.card : ℝ)⁻¹) ^ 2 * (∑ i ∈ s, ∑ j ∈ s, inner ℝ (v i) (v j)) := by
    rw [← real_inner_self_eq_norm_sq]
    simp_rw [real_inner_smul_left, real_inner_smul_right, sum_inner, inner_sum]
    ring
  rw [norm_sub_sq_real, hn, real_inner_smul_left, sum_inner]
  nlinarith [h]

open MeasureTheory

theorem l2_norm_sq_eq_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (f : Lp ℝ 2 μ) : ‖f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp [pow_two]

theorem l2_coe_finset_sum {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (s : Finset ι) (v : ι → Lp ℝ 2 μ) :
    (fun x => (∑ i ∈ s, v i) x) =ᵐ[μ] (fun x => ∑ i ∈ s, v i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
    simpa using hx
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (v a) (∑ i ∈ s, v i), ih] with x hx hx'
    simpa only [Pi.add_apply, hx'] using hx

theorem integral_average_sub_sq_le {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (s : Finset ι) (hs : s.Nonempty)
    (v : ι → Lp ℝ 2 μ) (z : Lp ℝ 2 μ) {D ε : ℝ} (hε : 0 ≤ ε)
    (hdiag : ∀ i ∈ s, (∫ x, (v i x) ^ 2 ∂μ) ≤ D)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (∫ x, v i x * v j x ∂μ) ≤ (∫ x, (z x) ^ 2 ∂μ) + ε)
    (hcross : ∀ i ∈ s, (∫ x, (z x) ^ 2 ∂μ) - ε ≤ ∫ x, v i x * z x ∂μ) :
    (∫ x, ((s.card : ℝ)⁻¹ * (∑ i ∈ s, v i x) - z x) ^ 2 ∂μ) ≤
      D / (s.card : ℝ) + 3 * ε := by
  have h := norm_average_sub_sq_le s hs v z hε
    (by simpa only [l2_norm_sq_eq_integral_sq] using hdiag)
    (by simpa only [L2.inner_def, RCLike.inner_apply, starRingEnd_apply,
      star_trivial, mul_comm, l2_norm_sq_eq_integral_sq] using hoff)
    (by simpa only [L2.inner_def, RCLike.inner_apply, starRingEnd_apply,
      star_trivial, mul_comm, l2_norm_sq_eq_integral_sq] using hcross)
  rw [l2_norm_sq_eq_integral_sq] at h
  have heq : (fun x => ((s.card : ℝ)⁻¹ • (∑ i ∈ s, v i) - z) x ^ 2) =ᵐ[μ]
      (fun x => ((s.card : ℝ)⁻¹ * (∑ i ∈ s, v i x) - z x) ^ 2) := by
    filter_upwards [Lp.coeFn_sub ((s.card : ℝ)⁻¹ • (∑ i ∈ s, v i)) z,
      Lp.coeFn_smul (s.card : ℝ)⁻¹ (∑ i ∈ s, v i), l2_coe_finset_sum s v]
      with x hsub hsmul hsum
    simp only [Pi.sub_apply] at hsub
    simp only [Pi.smul_apply, smul_eq_mul] at hsmul
    rw [hsub, hsmul, hsum]
  rwa [integral_congr_ae heq] at h

theorem integral_average_sub_sq_le_of_memLp {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (s : Finset ι) (hs : s.Nonempty)
    (v : ι → Ω → ℝ) (z : Ω → ℝ)
    (hv : ∀ i, MemLp (v i) 2 μ) (hz : MemLp z 2 μ)
    {D ε : ℝ} (hε : 0 ≤ ε)
    (hdiag : ∀ i ∈ s, (∫ x, (v i x) ^ 2 ∂μ) ≤ D)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (∫ x, v i x * v j x ∂μ) ≤ (∫ x, (z x) ^ 2 ∂μ) + ε)
    (hcross : ∀ i ∈ s, (∫ x, (z x) ^ 2 ∂μ) - ε ≤ ∫ x, v i x * z x ∂μ) :
    (∫ x, ((s.card : ℝ)⁻¹ * (∑ i ∈ s, v i x) - z x) ^ 2 ∂μ) ≤
      D / (s.card : ℝ) + 3 * ε := by
  let V : ι → Lp ℝ 2 μ := fun i => (hv i).toLp (v i)
  let Z : Lp ℝ 2 μ := hz.toLp z
  have hV (i : ι) : (fun x => V i x) =ᵐ[μ] v i := (hv i).coeFn_toLp
  have hZ : (fun x => Z x) =ᵐ[μ] z := hz.coeFn_toLp
  have hVsq (i : ι) : (∫ x, (V i x) ^ 2 ∂μ) = ∫ x, (v i x) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hV i] with x hx using congrArg (fun t : ℝ => t ^ 2) hx
  have hZsq : (∫ x, (Z x) ^ 2 ∂μ) = ∫ x, (z x) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hZ] with x hx using congrArg (fun t : ℝ => t ^ 2) hx
  have hVV (i j : ι) : (∫ x, V i x * V j x ∂μ) = ∫ x, v i x * v j x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hV i, hV j] with x hi hj
    rw [hi, hj]
  have hVZ (i : ι) : (∫ x, V i x * Z x ∂μ) = ∫ x, v i x * z x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hV i, hZ] with x hi hz'
    rw [hi, hz']
  have h := integral_average_sub_sq_le s hs V Z hε
    (by simpa only [hVsq] using hdiag)
    (by simpa only [hVV, hZsq] using hoff)
    (by simpa only [hVZ, hZsq] using hcross)
  have hall : ∀ᵐ x ∂μ, ∀ i ∈ s, V i x = v i x :=
    (Finset.eventually_all s).2 (fun i _ => hV i)
  have heq : (fun x => ((s.card : ℝ)⁻¹ * (∑ i ∈ s, V i x) - Z x) ^ 2) =ᵐ[μ]
      (fun x => ((s.card : ℝ)⁻¹ * (∑ i ∈ s, v i x) - z x) ^ 2) := by
    filter_upwards [hall, hZ] with x hx hz'
    rw [Finset.sum_congr rfl hx, hz']
  rwa [integral_congr_ae heq] at h

end InvariantRotation.SamplingMomentBounds

end OAI
