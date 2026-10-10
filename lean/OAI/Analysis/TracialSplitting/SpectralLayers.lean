import OAI.Analysis.TracialSplitting.ProjectionSampling

namespace OAI

universe uD uI


section

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

lemma scalar_inv_sqrt_near_one {t : ℝ} (ht : (1 / 2 : ℝ) ≤ t) :
    |t ^ (-(1 / 2) : ℝ) - 1| ≤ 2 * |t - 1| := by
  have ht0 : 0 ≤ t := by linarith
  have hs : (1 / 2 : ℝ) ≤ Real.sqrt t :=
    Real.le_sqrt_of_sq_le (by linarith)
  have hs0 : 0 < Real.sqrt t := by linarith
  have hsq := Real.sq_sqrt ht0
  have hfactor : t - 1 = (Real.sqrt t - 1) * (Real.sqrt t + 1) := by nlinarith
  have hsbound : |Real.sqrt t - 1| ≤ |t - 1| := by
    rw [hfactor, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt t + 1)]
    nlinarith [abs_nonneg (Real.sqrt t - 1), Real.sqrt_nonneg t]
  rw [Real.rpow_neg ht0, ← Real.sqrt_eq_rpow]
  have hinv : (Real.sqrt t)⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀ hs0).mpr (by nlinarith)
  calc
    |(Real.sqrt t)⁻¹ - 1| = |Real.sqrt t - 1| * (Real.sqrt t)⁻¹ := by
      have he : (Real.sqrt t)⁻¹ - 1 = -(Real.sqrt t - 1) * (Real.sqrt t)⁻¹ := by
        field_simp
        ring
      rw [he, abs_mul, abs_neg, abs_of_pos (inv_pos.mpr hs0)]
    _ ≤ |t - 1| * 2 := mul_le_mul hsbound hinv (by positivity) (abs_nonneg _)
    _ = _ := mul_comm _ _

section

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

omit [PartialOrder D] [StarOrderedRing D] in
lemma selfAdjoint_spectrum_near_one {a : D} (ha : IsSelfAdjoint a)
    {δ : ℝ} (hδ : ‖a - 1‖ ≤ δ) {t : ℝ} (ht : t ∈ spectrum ℝ a) :
    |t - 1| ≤ δ := by
  have hf : ContinuousOn (fun x : ℝ => x - 1) (spectrum ℝ a) := by fun_prop
  have h := norm_apply_le_norm_cfc (fun x : ℝ => x - 1) a ht hf ha
  rw [cfc_sub _ _ a, cfc_id' ℝ a ha] at h
  change ‖t - 1‖ ≤ ‖a - cfc (1 : ℝ → ℝ) a‖ at h
  rw [cfc_one ℝ a ha] at h
  exact h.trans hδ

lemma inv_sqrt_near_one {a : D} (ha : 0 ≤ a)
    {δ : ℝ} (hδ : ‖a - 1‖ ≤ δ) (hδhalf : δ ≤ 1 / 2) :
    IsStrictlyPositive a ∧ ‖CFC.rpow a (-(1 / 2) : ℝ) - 1‖ ≤ 2 * δ := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hsa : IsSelfAdjoint a := .of_nonneg ha
  have hs (t : ℝ) (ht : t ∈ spectrum ℝ a) : 1 / 2 ≤ t := by
    have h := selfAdjoint_spectrum_near_one hsa hδ ht
    have := (abs_le.mp h).1
    linarith
  have hsp : IsStrictlyPositive a :=
    CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mpr
      ⟨hsa, fun t ht => lt_of_lt_of_le (by norm_num) (hs t ht)⟩
  have hf : ContinuousOn (fun t : ℝ => t ^ (-(1 / 2) : ℝ)) (spectrum ℝ a) := by
    apply ContinuousOn.rpow_const continuousOn_id
    intro t ht
    left
    change t ≠ 0
    linarith [hs t ht]
  refine ⟨hsp, ?_⟩
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real ha, ← cfc_one ℝ a hsa]
  change ‖cfc (fun t : ℝ => t ^ (-(1 / 2) : ℝ)) a - cfc (fun _ : ℝ => 1) a‖ ≤ 2 * δ
  rw [← cfc_sub _ _ a hf continuousOn_const]
  apply norm_cfc_le (by positivity)
  intro t ht
  exact (scalar_inv_sqrt_near_one (hs t ht)).trans
    (mul_le_mul_of_nonneg_left (selfAdjoint_spectrum_near_one hsa hδ ht) (by norm_num))

lemma normalize_near_isometry {a : D} {δ : ℝ}
    (hδ : ‖star a * a - 1‖ ≤ δ) (hδhalf : δ ≤ 1 / 2) :
    ∃ u : D, star u * u = 1 ∧ ‖u - a‖ ≤ 2 * ‖a‖ * δ := by
  obtain ⟨hpos, hn⟩ := inv_sqrt_near_one (star_mul_self_nonneg a) hδ hδhalf
  let b := CFC.rpow (star a * a) (-(1 / 2) : ℝ)
  have hb : star b = b := (CFC.rpow_nonneg (a := star a * a)).isSelfAdjoint
  refine ⟨a * b, ?_, ?_⟩
  · rw [star_mul, hb]
    simpa only [b, CFC.rpow_eq_pow, mul_assoc] using CFC.conjugate_rpow_neg_one_half (star a * a) hpos
  · calc
      ‖a * b - a‖ = ‖a * (b - 1)‖ := by rw [mul_sub, mul_one]
      _ ≤ ‖a‖ * ‖b - 1‖ := norm_mul_le _ _
      _ ≤ ‖a‖ * (2 * δ) := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
      _ = _ := by ring

end

section SpectralEnergy

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable {I : Type uI} [Fintype I]

lemma traceTwoNorm_sq_real_smul (τ : TracialState D) (c : ℝ) (a : D) :
    traceTwoNorm τ (c • a) ^ 2 = c ^ 2 * traceTwoNorm τ a ^ 2 := by
  simp only [traceTwoNorm_sq, star_smul, star_trivial, smul_mul_assoc, mul_smul_comm,
    τ.functional.map_smul_of_tower, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma traceTwoNorm_sq_partition_left (τ : TracialState D) (e : I → D)
    (he : ∀ i, IsStarProjection (e i)) (hs : ∑ i, e i = 1) (a : D) :
    ∑ i, traceTwoNorm τ (e i * a) ^ 2 = traceTwoNorm τ a ^ 2 := by
  simp only [traceTwoNorm_sq, star_mul, fun i => (he i).isSelfAdjoint.star_eq]
  simp only [mul_assoc, ← mul_assoc (e _) (e _) a, fun i => (he i).isIdempotentElem.eq]
  rw [← Complex.re_sum, ← map_sum, ← Finset.mul_sum, ← Finset.sum_mul, hs, one_mul]

lemma traceTwoNorm_sq_partition_right (τ : TracialState D) (e : I → D)
    (he : ∀ i, IsStarProjection (e i)) (hs : ∑ i, e i = 1) (a : D) :
    ∑ i, traceTwoNorm τ (a * e i) ^ 2 = traceTwoNorm τ a ^ 2 := by
  calc
    _ = ∑ i, traceTwoNorm τ (e i * star a) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← traceTwoNorm_star τ (a * e i), star_mul, (he i).isSelfAdjoint.star_eq]
    _ = traceTwoNorm τ (star a) ^ 2 := traceTwoNorm_sq_partition_left τ e he hs (star a)
    _ = _ := by rw [traceTwoNorm_star]

lemma traceTwoNorm_sq_partition (τ : TracialState D) (e : I → D)
    (he : ∀ i, IsStarProjection (e i)) (hs : ∑ i, e i = 1) (a : D) :
    ∑ i, ∑ j, traceTwoNorm τ (e i * a * e j) ^ 2 = traceTwoNorm τ a ^ 2 := by
  simp only [traceTwoNorm_sq_partition_right τ e he hs]
  exact traceTwoNorm_sq_partition_left τ e he hs a

lemma spectral_commutator_energy (τ : TracialState D) (e : I → D)
    (he : ∀ i, IsStarProjection (e i)) (hs : ∑ i, e i = 1)
    (a : D) (c : I → ℝ) (hl : ∀ i, e i * a = c i • e i)
    (hr : ∀ i, a * e i = c i • e i) (x : D) :
    traceTwoNorm τ (x * a - a * x) ^ 2 =
      ∑ i, ∑ j, (c i - c j) ^ 2 * traceTwoNorm τ (e i * x * e j) ^ 2 := by
  rw [← traceTwoNorm_sq_partition τ e he hs (x * a - a * x)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h : e i * (x * a - a * x) * e j = (c j - c i) • (e i * x * e j) := by
    calc
      _ = e i * x * (a * e j) - (e i * a) * x * e j := by noncomm_ring
      _ = _ := by rw [hr j, hl i]; simp only [mul_smul_comm, smul_mul_assoc, sub_smul]
  rw [h, traceTwoNorm_sq_real_smul, sub_sq_comm]

lemma traceTwoNorm_sq_unitary_mul (τ : TracialState D) (x : unitary D) (a : D) :
    traceTwoNorm τ ((x : D) * a) ^ 2 = traceTwoNorm τ a ^ 2 := by
  rw [traceTwoNorm_sq, traceTwoNorm_sq, star_mul]
  simp only [mul_assoc, ← mul_assoc (star (x : D)) (x : D), x.property.1, one_mul]

lemma traceTwoNorm_sq_mul_unitary (τ : TracialState D) (x : unitary D) (a : D) :
    traceTwoNorm τ (a * (x : D)) ^ 2 = traceTwoNorm τ a ^ 2 := by
  rw [← traceTwoNorm_star τ (a * (x : D)), star_mul]
  change traceTwoNorm τ (((star x : unitary D) : D) * star a) ^ 2 = _
  rw [traceTwoNorm_sq_unitary_mul, traceTwoNorm_star]

lemma traceTwoNorm_sq_projection (τ : TracialState D) {p : D} (hp : IsStarProjection p) :
    traceTwoNorm τ p ^ 2 = (τ.functional p).re := by
  rw [traceTwoNorm_sq, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]

end SpectralEnergy

section SpectralRoot

variable {D : Type uD} [CStarAlgebra D]

variable {I : Type uI} [Fintype I]

lemma projection_combination_mul (e : I → D) (he : ∀ i, IsStarProjection (e i))
    (ho : Pairwise (fun i j => e i * e j = 0)) (c : I → ℝ) (j : I) :
    (∑ i, c i • e i) * e j = c j • e j := by
  classical
  rw [Finset.sum_mul]
  rw [Finset.sum_eq_single j]
  · rw [smul_mul_assoc, (he j).isIdempotentElem.eq]
  · intro i _ hij
    rw [smul_mul_assoc, ho hij, smul_zero]
  · simp

lemma projection_mul_combination (e : I → D) (he : ∀ i, IsStarProjection (e i))
    (ho : Pairwise (fun i j => e i * e j = 0)) (c : I → ℝ) (j : I) :
    e j * (∑ i, c i • e i) = c j • e j := by
  simpa only [star_mul, star_sum, star_smul, star_trivial,
    fun i => (he i).isSelfAdjoint.star_eq] using
      congrArg star (projection_combination_mul e he ho c j)

variable [PartialOrder D] [StarOrderedRing D]

lemma projection_combination_nonneg (e : I → D) (he : ∀ i, IsStarProjection (e i))
    (c : I → ℝ) (hc : ∀ i, 0 ≤ c i) : 0 ≤ ∑ i, c i • e i :=
  Finset.sum_nonneg (fun i _ => smul_nonneg (hc i) (he i).nonneg)

lemma sqrt_projection_combination (e : I → D) (he : ∀ i, IsStarProjection (e i))
    (ho : Pairwise (fun i j => e i * e j = 0)) (c : I → ℝ) (hc : ∀ i, 0 ≤ c i) :
    CFC.sqrt (∑ i, c i • e i) = ∑ i, Real.sqrt (c i) • e i := by
  apply (CFC.sqrt_eq_iff _ _ (projection_combination_nonneg e he c hc)
    (projection_combination_nonneg e he _ (fun i => Real.sqrt_nonneg _))).mpr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_smul_comm, projection_combination_mul e he ho, smul_smul,
    ← sq, Real.sq_sqrt (hc j)]

end SpectralRoot

lemma weighted_spectral_cauchy {I : Type uI} [Fintype I]
    (c : I → ℝ) (hc : ∀ i, 0 ≤ c i) (w : I → I → ℝ) (hw : ∀ i j, 0 ≤ w i j) :
    (∑ i, ∑ j, |c i - c j| * w i j) ^ 2 ≤
      (∑ i, ∑ j, (Real.sqrt (c i) - Real.sqrt (c j)) ^ 2 * w i j) *
      (∑ i, ∑ j, (Real.sqrt (c i) + Real.sqrt (c j)) ^ 2 * w i j) := by
  classical
  simp only [← Fintype.sum_prod_type']
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i _; exact mul_nonneg (sq_nonneg _) (hw i.1 i.2)
  · intro i _; exact mul_nonneg (sq_nonneg _) (hw i.1 i.2)
  · intro i _
    rw [mul_pow, sq_abs]
    have he : c i.1 - c i.2 =
        (Real.sqrt (c i.1) - Real.sqrt (c i.2)) *
          (Real.sqrt (c i.1) + Real.sqrt (c i.2)) := by
      nlinarith [Real.sq_sqrt (hc i.1), Real.sq_sqrt (hc i.2)]
    rw [he]
    ring_nf
    exact le_rfl

section SpectralEstimate

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable {I : Type uI} [Fintype I]

lemma traceTwoNorm_sq_partition_unitary_row (τ : TracialState D) (e : I → D)
    (he : ∀ i, IsStarProjection (e i)) (hs : ∑ i, e i = 1) (x : unitary D) (i : I) :
    ∑ j, traceTwoNorm τ (e i * (x : D) * e j) ^ 2 = (τ.functional (e i)).re := by
  rw [traceTwoNorm_sq_partition_right τ e he hs, traceTwoNorm_sq_mul_unitary,
    traceTwoNorm_sq_projection τ (he i)]

lemma traceTwoNorm_sq_partition_unitary_col (τ : TracialState D) (e : I → D)
    (he : ∀ i, IsStarProjection (e i)) (hs : ∑ i, e i = 1) (x : unitary D) (j : I) :
    ∑ i, traceTwoNorm τ (e i * (x : D) * e j) ^ 2 = (τ.functional (e j)).re := by
  simp only [mul_assoc]
  rw [traceTwoNorm_sq_partition_left τ e he hs, traceTwoNorm_sq_unitary_mul,
    traceTwoNorm_sq_projection τ (he j)]

omit [StarOrderedRing D] in
lemma trace_projection_combination (τ : TracialState D) (e : I → D) (c : I → ℝ) :
    (τ.functional (∑ i, c i • e i)).re = ∑ i, c i * (τ.functional (e i)).re := by
  simp only [map_sum, τ.functional.map_smul_of_tower, Complex.re_sum,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

lemma spectral_root_sum_le (τ : TracialState D) (e : I → D)
    (he : ∀ i, IsStarProjection (e i)) (hs : ∑ i, e i = 1)
    (c : I → ℝ) (hc : ∀ i, 0 ≤ c i) (x : unitary D) :
    (∑ i, ∑ j, (Real.sqrt (c i) + Real.sqrt (c j)) ^ 2 *
      traceTwoNorm τ (e i * (x : D) * e j) ^ 2) ≤
        4 * (τ.functional (∑ i, c i • e i)).re := by
  calc
    _ ≤ ∑ i, ∑ j, (2 * c i + 2 * c j) *
        traceTwoNorm τ (e i * (x : D) * e j) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      nlinarith [Real.sq_sqrt (hc i), Real.sq_sqrt (hc j),
        sq_nonneg (Real.sqrt (c i) - Real.sqrt (c j))]
    _ = 4 * (τ.functional (∑ i, c i • e i)).re := by
      simp only [add_mul, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => 2 * c j *
        traceTwoNorm τ (e i * (x : D) * e j) ^ 2)]
      simp only [← Finset.mul_sum, traceTwoNorm_sq_partition_unitary_row τ e he hs,
        traceTwoNorm_sq_partition_unitary_col τ e he hs]
      rw [trace_projection_combination]
      simp only [mul_assoc, ← Finset.mul_sum]
      ring

lemma sqrt_unitary_conjugate {b : D} (hb : 0 ≤ b) (x : unitary D) :
    CFC.sqrt ((x : D) * b * star (x : D)) =
      (x : D) * CFC.sqrt b * star (x : D) := by
  apply CFC.sqrt_unique (hb := star_right_conjugate_nonneg (CFC.sqrt_nonneg b) _)
  calc
    _ = (x : D) * (CFC.sqrt b * CFC.sqrt b) * star (x : D) := by
      simp only [mul_assoc, ← mul_assoc (star (x : D)) (x : D), x.property.1, one_mul]
    _ = _ := by rw [CFC.sqrt_mul_sqrt_self b hb]

lemma root_commutator_sq_le (τ : TracialState D) {b : D} (hb : 0 ≤ b) (x : unitary D) :
    traceTwoNorm τ ((x : D) * CFC.sqrt b - CFC.sqrt b * (x : D)) ^ 2 ≤
      traceOneNorm τ (b - (x : D) * b * star (x : D)) := by
  have hpos : 0 ≤ (x : D) * b * star (x : D) := star_right_conjugate_nonneg hb _
  have h := powers_stormer τ hb hpos
  rw [sqrt_unitary_conjugate hb x] at h
  calc
    _ = traceTwoNorm τ ((CFC.sqrt b - (x : D) * CFC.sqrt b * star (x : D)) *
        (x : D)) ^ 2 := by
      have he : (CFC.sqrt b - (x : D) * CFC.sqrt b * star (x : D)) * (x : D) =
          -((x : D) * CFC.sqrt b - CFC.sqrt b * (x : D)) := by
        simp only [sub_mul, mul_assoc, x.property.1, mul_one, neg_sub]
      rw [he]
      simp only [traceTwoNorm_eq_gns, map_neg, norm_neg]
    _ = _ := traceTwoNorm_sq_mul_unitary τ x _
    _ ≤ _ := h

theorem finite_spectral_energy (τ : TracialState D) (e : I → D)
    (he : ∀ i, IsStarProjection (e i)) (hs : ∑ i, e i = 1)
    (ho : Pairwise (fun i j => e i * e j = 0))
    (c : I → ℝ) (hc : ∀ i, 0 ≤ c i) (x : unitary D) :
    (∑ i, ∑ j, |c i - c j| * traceTwoNorm τ (e i * (x : D) * e j) ^ 2) ≤
      2 * Real.sqrt ((τ.functional (∑ i, c i • e i)).re *
        traceOneNorm τ ((∑ i, c i • e i) -
          (x : D) * (∑ i, c i • e i) * star (x : D))) := by
  let b := ∑ i, c i • e i
  have hb : 0 ≤ b := projection_combination_nonneg e he c hc
  have hm : 0 ≤ (τ.functional b).re := (τ.functional.map_nonneg hb).1
  have hcs := weighted_spectral_cauchy c hc
    (fun i j => traceTwoNorm τ (e i * (x : D) * e j) ^ 2) (fun i j => sq_nonneg _)
  have hroot : (∑ i, ∑ j, (Real.sqrt (c i) - Real.sqrt (c j)) ^ 2 *
      traceTwoNorm τ (e i * (x : D) * e j) ^ 2) =
      traceTwoNorm τ ((x : D) * CFC.sqrt b - CFC.sqrt b * (x : D)) ^ 2 := by
    dsimp only [b]
    rw [sqrt_projection_combination e he ho c hc]
    exact (spectral_commutator_energy τ e he hs _ _
      (projection_mul_combination e he ho _) (projection_combination_mul e he ho _) _).symm
  rw [hroot] at hcs
  have hsum := spectral_root_sum_le τ e he hs c hc x
  have hsquare := hcs.trans (mul_le_mul_of_nonneg_left hsum (sq_nonneg _))
  have hpow := root_commutator_sq_le τ hb x
  have hfinal := hsquare.trans (mul_le_mul_of_nonneg_right hpow (mul_nonneg (by norm_num) hm))
  have hnonneg : 0 ≤ (τ.functional b).re * traceOneNorm τ (b - (x : D) * b * star (x : D)) :=
    mul_nonneg hm (traceOneNorm_nonneg τ _)
  have hsqrt := Real.sq_sqrt hnonneg
  have hsqrt0 := Real.sqrt_nonneg ((τ.functional b).re *
    traceOneNorm τ (b - (x : D) * b * star (x : D)))
  change _ ≤ 2 * Real.sqrt ((τ.functional b).re *
    traceOneNorm τ (b - (x : D) * b * star (x : D)))
  nlinarith

end SpectralEstimate

section LayerCake

variable {I : Type uI} [Fintype I] [LinearOrder I]

def cutCoefficient (j i : I) : ℝ := if j ≤ i then 1 else 0

omit [Fintype I] in
lemma cutCoefficient_nonneg (j i : I) : 0 ≤ cutCoefficient j i := by
  unfold cutCoefficient
  split <;> norm_num

omit [Fintype I] in
lemma cutCoefficient_mono (j : I) : Monotone (cutCoefficient j) := by
  intro i k hik
  unfold cutCoefficient
  split_ifs with hji hjk
  · exact le_rfl
  · exact (hjk (hji.trans hik)).elim
  · norm_num
  · exact le_rfl

def layerCoefficient (w : I → ℝ) (i : I) : ℝ := ∑ j, w j * cutCoefficient j i

lemma layerCoefficient_nonneg (w : I → ℝ) (hw : ∀ j, 0 ≤ w j) (i : I) :
    0 ≤ layerCoefficient w i :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (hw j) (cutCoefficient_nonneg j i))

lemma layerCoefficient_mono (w : I → ℝ) (hw : ∀ j, 0 ≤ w j) :
    Monotone (layerCoefficient w) := by
  intro i k hik
  exact Finset.sum_le_sum (fun j _ =>
    mul_le_mul_of_nonneg_left (cutCoefficient_mono j hik) (hw j))

lemma cut_difference_sum_of_le (w : I → ℝ) (i k : I) (hik : i ≤ k) :
    (∑ j, w j * (cutCoefficient j i - cutCoefficient j k) ^ 2) =
      layerCoefficient w k - layerCoefficient w i := by
  rw [layerCoefficient, layerCoefficient, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold cutCoefficient
  split_ifs with hji hjk
  · ring
  · exact (hjk (hji.trans hik)).elim
  · ring
  · ring

lemma cut_difference_sum (w : I → ℝ) (hw : ∀ j, 0 ≤ w j) (i k : I) :
    (∑ j, w j * (cutCoefficient j i - cutCoefficient j k) ^ 2) =
      |layerCoefficient w i - layerCoefficient w k| := by
  rcases le_total i k with hik | hki
  · rw [cut_difference_sum_of_le w i k hik,
      abs_of_nonpos (sub_nonpos.mpr (layerCoefficient_mono w hw hik))]
    ring
  · simp only [sub_sq_comm (cutCoefficient _ i) (cutCoefficient _ k)]
    rw [cut_difference_sum_of_le w k i hki,
      abs_of_nonneg (sub_nonneg.mpr (layerCoefficient_mono w hw hki))]

variable {D : Type uD} [CStarAlgebra D]

def upperLayerCut (e : I → D) (j : I) : D := ∑ i, cutCoefficient j i • e i

lemma upperLayerCut_projection (e : I → D) (he : ∀ i, IsStarProjection (e i))
    (ho : Pairwise (fun i j => e i * e j = 0)) (j : I) :
    IsStarProjection (upperLayerCut e j) := by
  classical
  have h := orthogonal_projection_sum (Finset.univ.filter (j ≤ ·)) e
    (fun i _ => he i) (fun i _ k _ hik => ho hik)
  simpa only [Finset.sum_filter, upperLayerCut, cutCoefficient, ite_smul,
    one_smul, zero_smul] using h

lemma layer_decomposition (e : I → D) (w : I → ℝ) :
    (∑ j, w j • upperLayerCut e j) = ∑ i, layerCoefficient w i • e i := by
  simp only [upperLayerCut, Finset.smul_sum, smul_smul, layerCoefficient, Finset.sum_smul]
  exact Finset.sum_comm

variable [PartialOrder D] [StarOrderedRing D]

theorem layer_energy (τ : TracialState D) (e : I → D)
    (he : ∀ i, IsStarProjection (e i)) (hs : ∑ i, e i = 1)
    (ho : Pairwise (fun i j => e i * e j = 0))
    (w : I → ℝ) (hw : ∀ j, 0 ≤ w j) (x : D) :
    (∑ j, w j * traceTwoNorm τ (x * upperLayerCut e j - upperLayerCut e j * x) ^ 2) =
    ∑ i, ∑ k, |layerCoefficient w i - layerCoefficient w k| *
      traceTwoNorm τ (e i * x * e k) ^ 2 := by
  simp_rw [upperLayerCut, spectral_commutator_energy τ e he hs _ _
    (projection_mul_combination e he ho _) (projection_combination_mul e he ho _) x]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [← mul_assoc, ← Finset.sum_mul, cut_difference_sum w hw]

theorem layer_energy_le (τ : TracialState D) (e : I → D)
    (he : ∀ i, IsStarProjection (e i)) (hs : ∑ i, e i = 1)
    (ho : Pairwise (fun i j => e i * e j = 0))
    (w : I → ℝ) (hw : ∀ j, 0 ≤ w j) (x : unitary D) :
    (∑ j, w j * traceTwoNorm τ ((x : D) * upperLayerCut e j -
      upperLayerCut e j * (x : D)) ^ 2) ≤
      2 * Real.sqrt ((τ.functional (∑ j, w j • upperLayerCut e j)).re *
        traceOneNorm τ ((∑ j, w j • upperLayerCut e j) -
          (x : D) * (∑ j, w j • upperLayerCut e j) * star (x : D))) := by
  rw [layer_energy τ e he hs ho w hw, layer_decomposition e w]
  exact finite_spectral_energy τ e he hs ho _ (layerCoefficient_nonneg w hw) x

end LayerCake

section LayerWeights

def orderedLayerWeights {n : ℕ} (c : Fin n → ℝ) (j : Fin n) : ℝ :=
  Fin.cons (α := fun _ => ℝ) 0 c j.succ - Fin.cons (α := fun _ => ℝ) 0 c j.castSucc

lemma orderedLayerValues_mono {n : ℕ} (c : Fin n → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hm : Monotone c) : Monotone (Fin.cons (α := fun _ => ℝ) 0 c) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact le_rfl
    | succ j => exact hc j
  | succ i =>
    cases j using Fin.cases with
    | zero => simp at hij
    | succ j => exact hm (Fin.succ_le_succ_iff.mp hij)

lemma orderedLayerWeights_nonneg {n : ℕ} (c : Fin n → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hm : Monotone c) (j : Fin n) :
    0 ≤ orderedLayerWeights c j := by
  dsimp only [orderedLayerWeights]
  apply sub_nonneg.mpr
  exact orderedLayerValues_mono c hc hm (Fin.castSucc_le_succ j)

lemma orderedLayerWeights_le {n : ℕ} (c : Fin n → ℝ)
    (hc : ∀ i, 0 ≤ c i) (j : Fin n) : orderedLayerWeights c j ≤ c j := by
  have h : 0 ≤ Fin.cons (α := fun _ => ℝ) 0 c j.castSucc := by
    cases he : j.castSucc using Fin.cases with
    | zero => simp
    | succ k => simpa using hc k
  simpa only [orderedLayerWeights, Fin.cons_succ, sub_le_self_iff] using h

lemma layerCoefficient_orderedLayerWeights {n : ℕ} (c : Fin n → ℝ) (i : Fin n) :
    layerCoefficient (orderedLayerWeights c) i = c i := by
  classical
  have h := Fin.sum_Iic_sub i (Fin.cons (α := fun _ => ℝ) 0 c)
  simp only [Fin.cons_succ, Fin.cons_zero, sub_zero] at h
  convert h using 1
  simp only [layerCoefficient, cutCoefficient, orderedLayerWeights, mul_ite, mul_one,
    mul_zero, ← Finset.sum_filter]
  congr 1
  ext j
  simp

end LayerWeights

section LayerComplete

variable {D : Type uD} [CStarAlgebra D] {n : ℕ}

lemma projection_sum_mul_atom (e : Fin n → D) (he : ∀ i, IsStarProjection (e i))
    (ho : Pairwise (fun i j => e i * e j = 0)) (j : Fin n) :
    (∑ i, e i) * e j = e j := by
  simpa using projection_combination_mul e he ho (fun _ => 1) j

lemma projection_atom_mul_sum (e : Fin n → D) (he : ∀ i, IsStarProjection (e i))
    (ho : Pairwise (fun i j => e i * e j = 0)) (j : Fin n) :
    e j * (∑ i, e i) = e j := by
  simpa using projection_mul_combination e he ho (fun _ => 1) j

def completeResolution (e : Fin n → D) : Fin (n + 1) → D :=
  Fin.cons (α := fun _ => D) (1 - ∑ i, e i) e

lemma completeResolution_projection (e : Fin n → D)
    (he : ∀ i, IsStarProjection (e i))
    (ho : Pairwise (fun i j => e i * e j = 0)) (i : Fin (n + 1)) :
    IsStarProjection (completeResolution e i) := by
  cases i using Fin.cases with
  | zero =>
    exact (orthogonal_projection_sum Finset.univ e (fun i _ => he i)
      (fun i _ j _ hij => ho hij)).one_sub
  | succ i => exact he i

lemma completeResolution_orthogonal (e : Fin n → D)
    (he : ∀ i, IsStarProjection (e i))
    (ho : Pairwise (fun i j => e i * e j = 0)) :
    Pairwise (fun i j => completeResolution e i * completeResolution e j = 0) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact (hij rfl).elim
    | succ j =>
      change (1 - ∑ i, e i) * e j = 0
      rw [sub_mul, one_mul, projection_sum_mul_atom e he ho, sub_self]
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      change e i * (1 - ∑ j, e j) = 0
      rw [mul_sub, mul_one, projection_atom_mul_sum e he ho, sub_self]
    | succ j => exact ho (fun h => hij (congrArg Fin.succ h))

lemma completeResolution_sum (e : Fin n → D) : ∑ i, completeResolution e i = 1 := by
  rw [Fin.sum_univ_succ]
  simp [completeResolution]

lemma upperLayerCut_completeResolution_succ (e : Fin n → D) (j : Fin n) :
    upperLayerCut (completeResolution e) j.succ = upperLayerCut e j := by
  simp only [upperLayerCut, Fin.sum_univ_succ, completeResolution, Fin.cons_zero,
    Fin.cons_succ, cutCoefficient, Fin.succ_le_succ_iff]
  simp

variable [PartialOrder D] [StarOrderedRing D]

theorem layer_energy_le_of_orthogonal (τ : TracialState D) (e : Fin n → D)
    (he : ∀ i, IsStarProjection (e i))
    (ho : Pairwise (fun i j => e i * e j = 0))
    (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (x : unitary D) :
    (∑ j, w j * traceTwoNorm τ ((x : D) * upperLayerCut e j -
      upperLayerCut e j * (x : D)) ^ 2) ≤
      2 * Real.sqrt ((τ.functional (∑ j, w j • upperLayerCut e j)).re *
        traceOneNorm τ ((∑ j, w j • upperLayerCut e j) -
          (x : D) * (∑ j, w j • upperLayerCut e j) * star (x : D))) := by
  have hpos : ∀ j, 0 ≤ Fin.cons (α := fun _ => ℝ) 0 w j := by
    intro j
    cases j using Fin.cases with
    | zero => exact le_rfl
    | succ j => exact hw j
  have h := layer_energy_le τ (completeResolution e) (completeResolution_projection e he ho)
    (completeResolution_sum e) (completeResolution_orthogonal e he ho)
    (Fin.cons (α := fun _ => ℝ) 0 w) hpos x
  simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, zero_mul, zero_smul,
    zero_add, upperLayerCut_completeResolution_succ] using h

end LayerComplete

section CornerPolar

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma normalize_near_partial_isometry {p a : D} (hp : IsStarProjection p)
    (hap : a * p = a) {δ : ℝ} (hδ : ‖star a * a - p‖ ≤ δ)
    (hδhalf : δ ≤ 1 / 2) :
    ∃ u : D, star u * u = p ∧ ‖u - a‖ ≤ 2 * ‖a‖ * δ := by
  have hpa : p * star a = star a := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hap
  let b : ProjectionCorner hp := ⟨star a * a,
    by simp only [← mul_assoc, hpa], by simp only [mul_assoc, hap]⟩
  have hb : 0 ≤ b := star_mul_self_nonneg a
  have hbn : ‖b - 1‖ ≤ δ := hδ
  obtain ⟨hbpos, hn⟩ := inv_sqrt_near_one hb hbn hδhalf
  let z := CFC.rpow b (-(1 / 2) : ℝ)
  have hz : IsSelfAdjoint z := .of_nonneg CFC.rpow_nonneg
  have heq : z * b * z = 1 := CFC.conjugate_rpow_neg_one_half b hbpos
  refine ⟨a * (z : D), ?_, ?_⟩
  · rw [star_mul, (ProjectionCorner.isSelfAdjoint_coe hp hz).star_eq]
    have h := congrArg (fun t : ProjectionCorner hp => (t : D)) heq
    change (z : D) * (star a * a) * (z : D) = p at h
    simpa only [mul_assoc] using h
  · calc
      ‖a * (z : D) - a‖ = ‖a * ((z : D) - p)‖ := by rw [mul_sub, hap]
      _ ≤ ‖a‖ * ‖(z : D) - p‖ := norm_mul_le _ _
      _ ≤ ‖a‖ * (2 * δ) := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
      _ = _ := by ring

end CornerPolar

end CurrentMain

end

end

end OAI
