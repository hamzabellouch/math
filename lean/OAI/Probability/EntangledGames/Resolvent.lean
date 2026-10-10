import OAI.Probability.EntangledGames.Basic

namespace OAI

universe u_n u_J

open scoped BigOperators ComplexOrder

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

namespace ThresholdParallelRepetition.Resolvent

variable {n : Type u_n} [Fintype n] [DecidableEq n]

omit [Fintype n] in

lemma shift_posDef {A : Matrix n n ℂ} (hA : A.PosSemidef) {s : ℝ} (hs : 0 < s) :
    (A + s • (1 : Matrix n n ℂ)).PosDef := by
  simpa only [add_comm] using ((Matrix.PosDef.one : (1 : Matrix n n ℂ).PosDef).smul hs).add_posSemidef hA

lemma second_resolvent_identity (A B : Matrix n n ℂ) (hA : IsUnit A) (hB : IsUnit B) :
    A⁻¹ = B⁻¹ - B⁻¹ * (A - B) * B⁻¹ +
      B⁻¹ * (A - B) * A⁻¹ * (A - B) * B⁻¹ := by
  have h₁ : B⁻¹ - A⁻¹ = B⁻¹ * (A - B) * A⁻¹ :=
    Matrix.inv_sub_inv (by simp [hA, hB])
  have h₂ : A⁻¹ - B⁻¹ = -(A⁻¹ * (A - B) * B⁻¹) := by
    rw [Matrix.inv_sub_inv (by simp [hA, hB]), ← neg_sub A B, mul_neg, neg_mul]
  rw [← h₁]
  calc
    A⁻¹ = B⁻¹ - A⁻¹ * (A - B) * B⁻¹ := by
      apply sub_eq_iff_eq_add.mp at h₂
      simpa only [sub_eq_add_neg, add_comm] using h₂
    _ = B⁻¹ - B⁻¹ * (A - B) * B⁻¹ +
        (B⁻¹ - A⁻¹) * (A - B) * B⁻¹ := by noncomm_ring

def resolvent (A : Matrix n n ℂ) (s : ℝ) : Matrix n n ℂ :=
  (A + s • (1 : Matrix n n ℂ))⁻¹

def purificationKernel (A : Matrix n n ℂ) (s : ℝ) : Matrix n n ℂ :=
  A * resolvent A s

lemma resolvent_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) : (resolvent A s).PosSemidef :=
  (shift_posDef hA hs).posSemidef.inv

lemma resolvent_mul_shift {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) : resolvent A s * (A + s • 1) = 1 := by
  exact Matrix.nonsing_inv_mul _ ((shift_posDef hA hs).isUnit.map Matrix.detMonoidHom)

lemma shift_mul_resolvent {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) : (A + s • 1) * resolvent A s = 1 := by
  exact Matrix.mul_nonsing_inv _ ((shift_posDef hA hs).isUnit.map Matrix.detMonoidHom)

lemma purificationKernel_eq {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) : purificationKernel A s = 1 - s • resolvent A s := by
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_mul, smul_mul_assoc, one_mul, purificationKernel] using
    shift_mul_resolvent hA hs

lemma resolvent_mul_eq {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) : resolvent A s * A = 1 - s • resolvent A s := by
  apply eq_sub_iff_add_eq.mpr
  simpa only [mul_add, mul_smul_comm, mul_one] using resolvent_mul_shift hA hs

lemma resolvent_square_le {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    s • (resolvent A s * resolvent A s) ≤ resolvent A s := by
  rw [Matrix.le_iff]
  have hp := hA.conjTranspose_mul_mul_same (resolvent A s)
  rw [(resolvent_posSemidef hA hs).isHermitian.eq, resolvent_mul_eq hA hs,
    sub_mul, one_mul, smul_mul_assoc] at hp
  exact hp

lemma purificationKernel_sub {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {s : ℝ} (hs : 0 < s) :
    purificationKernel A s - purificationKernel B s =
      s • (resolvent A s * (A - B) * resolvent B s) := by
  rw [purificationKernel_eq hA hs, purificationKernel_eq hB hs]
  have h : resolvent A s - resolvent B s =
      -(resolvent A s * (A - B) * resolvent B s) := by
    dsimp only [resolvent]
    rw [Matrix.inv_sub_inv (by simp [(shift_posDef hA hs).isUnit,
      (shift_posDef hB hs).isUnit])]
    rw [add_sub_add_right_eq_sub, ← neg_sub A B, mul_neg, neg_mul]
  calc
    _ = -(s • (resolvent A s - resolvent B s)) := by module
    _ = _ := by rw [h, smul_neg, neg_neg]

lemma purificationKernel_square_le {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {s : ℝ} (hs : 0 < s) :
    (purificationKernel A s - purificationKernel B s)ᴴ *
      (purificationKernel A s - purificationKernel B s) ≤
      s • (resolvent B s * (A - B) * resolvent A s * (A - B) * resolvent B s) := by
  have hRA := (resolvent_posSemidef hA hs).isHermitian.eq
  have hRB := (resolvent_posSemidef hB hs).isHermitian.eq
  have hD := (hA.isHermitian.sub hB.isHermitian).eq
  have hp := ((Matrix.le_iff.mp (resolvent_square_le hA hs)).conjTranspose_mul_mul_same
    ((A - B) * resolvent B s)).smul hs.le
  rw [Matrix.le_iff, purificationKernel_sub hA hB hs]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, star_trivial,
    hRA, hRB, hD] at hp ⊢
  simp only [smul_sub, Matrix.mul_sub, Matrix.sub_mul,
    smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc] at hp ⊢
  convert hp using 1
  first | rfl | module

lemma weighted_resolvent_identity {J : Type u_J} [Fintype J]
    (A : J → Matrix n n ℂ) (w : J → ℝ) (B : Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (hB : B.PosSemidef)
    (hw : ∑ j, w j = 1) (hmean : ∑ j, w j • A j = B)
    {s : ℝ} (hs : 0 < s) :
    ∑ j, w j • (resolvent (A j) s - resolvent B s) =
      ∑ j, w j • (resolvent B s * (A j - B) * resolvent (A j) s *
        (A j - B) * resolvent B s) := by
  have hlinear : ∑ j, w j • (A j - B) = 0 := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, hmean, ← Finset.sum_smul, hw, one_smul, sub_self]
  have hzero : ∑ j, w j • (resolvent B s * (A j - B) * resolvent B s) = 0 := by
    calc
      _ = resolvent B s * (∑ j, w j • (A j - B)) * resolvent B s := by
        simp only [Finset.sum_mul, Finset.mul_sum, mul_smul_comm, smul_mul_assoc]
      _ = 0 := by rw [hlinear, mul_zero, zero_mul]
  have hsecond (j : J) : resolvent (A j) s =
      resolvent B s - resolvent B s * (A j - B) * resolvent B s +
        resolvent B s * (A j - B) * resolvent (A j) s * (A j - B) * resolvent B s := by
    simpa only [resolvent, add_sub_add_right_eq_sub] using
      second_resolvent_identity (A j + s • 1) (B + s • 1)
        (shift_posDef (hA j) hs).isUnit (shift_posDef hB hs).isUnit
  have heq (j : J) : resolvent (A j) s - resolvent B s =
      -(resolvent B s * (A j - B) * resolvent B s) +
        resolvent B s * (A j - B) * resolvent (A j) s * (A j - B) * resolvent B s := by
    rw [sub_eq_iff_eq_add]
    calc
      _ = _ := hsecond j
      _ = _ := by abel
  simp_rw [heq, smul_add, smul_neg]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, hzero, neg_zero, zero_add]

lemma weighted_kernel_square_le {J : Type u_J} [Fintype J]
    (A : J → Matrix n n ℂ) (w : J → ℝ) (B : Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (hB : B.PosSemidef)
    (hw0 : ∀ j, 0 ≤ w j) (hw : ∑ j, w j = 1) (hmean : ∑ j, w j • A j = B)
    {s : ℝ} (hs : 0 < s) :
    ∑ j, w j • ((purificationKernel (A j) s - purificationKernel B s)ᴴ *
      (purificationKernel (A j) s - purificationKernel B s)) ≤
    s • ∑ j, w j • (resolvent (A j) s - resolvent B s) := by
  calc
    _ ≤ ∑ j, w j • (s • (resolvent B s * (A j - B) * resolvent (A j) s *
        (A j - B) * resolvent B s)) := by
      exact Finset.sum_le_sum fun j _ => smul_le_smul_of_nonneg_left
        (purificationKernel_square_le (hA j) hB hs) (hw0 j)
    _ = s • ∑ j, w j • (resolvent B s * (A j - B) * resolvent (A j) s *
        (A j - B) * resolvent B s) := by
      simp only [Finset.smul_sum, smul_smul, mul_comm (w _) s]
    _ = _ := by rw [weighted_resolvent_identity A w B hA hB hw hmean hs]

end ThresholdParallelRepetition.Resolvent

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace ThresholdParallelRepetition.Resolvent

lemma scalar_square_integral {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun s : ℝ => t ^ 2 / (t + s) ^ 2) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, t ^ 2 / (t + s) ^ 2) = t := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp
  have hd (s : ℝ) (hs : s ∈ Ici (0 : ℝ)) :
      HasDerivAt (fun u : ℝ => -(t ^ 2) / (t + u)) (t ^ 2 / (t + s) ^ 2) s := by
    convert! (hasDerivAt_const s (-(t ^ 2))).div
      ((hasDerivAt_id s).const_add t) (ne_of_gt (add_pos_of_pos_of_nonneg ht hs)) using 1
    simp only [id_eq]
    ring
  have htop : Tendsto (fun s : ℝ => t + s) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop (b - t)] with s hs
    linarith
  have hl := htop.const_div_atTop (-(t ^ 2))
  have hpos (s : ℝ) (_hs : s ∈ Ioi (0 : ℝ)) : 0 ≤ t ^ 2 / (t + s) ^ 2 := by positivity
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hpos hl, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd hpos hl]
  simp only [add_zero, zero_sub, neg_div, neg_neg]
  field_simp

lemma scalar_entropy_integral {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IntegrableOn (fun s : ℝ => t / (1 + s) - t / (t + s)) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, t / (1 + s) - t / (t + s)) = t * Real.log t := by
  rcases eq_or_lt_of_le ht0 with rfl | ht
  · simp
  have hd (s : ℝ) (hs : s ∈ Ici (0 : ℝ)) :
      HasDerivAt (fun u : ℝ => t * (Real.log (1 + u) - Real.log (t + u)))
        (t / (1 + s) - t / (t + s)) s := by
    have h₁ := ((hasDerivAt_id s).const_add (1 : ℝ)).log
      (ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one hs))
    have h₂ := ((hasDerivAt_id s).const_add t).log
      (ne_of_gt (add_pos_of_pos_of_nonneg ht hs))
    convert! (h₁.sub h₂).const_mul t using 1
    simp only [id_eq]
    ring
  have htop : Tendsto (fun s : ℝ => t + s) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop (b - t)] with s hs
    linarith
  have hratio : Tendsto (fun s : ℝ => (1 + s) / (t + s)) atTop (𝓝 1) := by
    have hh := (htop.const_div_atTop (1 - t)).const_add (1 : ℝ)
    rw [add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    have ht' : t + s ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg ht hs)
    field_simp
    ring
  have hlog : Tendsto (fun s : ℝ => Real.log ((1 + s) / (t + s))) atTop (𝓝 0) := by
    simpa only [Real.log_one, Function.comp_def] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  have hl : Tendsto (fun s : ℝ => t * (Real.log (1 + s) - Real.log (t + s)))
      atTop (𝓝 0) := by
    have hh := hlog.const_mul t
    rw [mul_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    rw [Real.log_div (ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one hs))
      (ne_of_gt (add_pos_of_pos_of_nonneg ht hs))]
  have hneg (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      t / (1 + s) - t / (t + s) ≤ 0 := by
    apply sub_nonpos.mpr
    apply div_le_div_of_nonneg_left ht.le (add_pos ht hs)
    linarith
  refine ⟨integrableOn_Ioi_deriv_of_nonpos' hd hneg hl, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonpos' hd hneg hl]
  simp

end ThresholdParallelRepetition.Resolvent

end
end

end OAI
