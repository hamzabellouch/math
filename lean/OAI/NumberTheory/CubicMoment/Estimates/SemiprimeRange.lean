import OAI.NumberTheory.CubicMoment.Estimates.SemiprimePartition
import OAI.NumberTheory.CubicMoment.Estimates.OverlapScale
import OAI.NumberTheory.CubicMoment.Estimates.FixedScalePowers

namespace OAI

/-! Actual nonzero semiprime pieces lie in the balanced prime range.
The upper bilinear constraint follows from a strict power gap, uniformly
for every fixed logarithmic exponent required by the published inputs. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma semiprimePartitionCoefficient_range {X : ℝ} (hX : 0 < X)
    {j : ℕ} {p : Eisenstein} (hp : semiprimePartitionCoefficient X j p ≠ 0) :
    X^(2/5:ℝ) < norm p ∧ semiprimePartitionScale j ≤ norm p ∧
      norm p ≤ 2*semiprimePartitionScale j := by
  have hA := semiprimePartitionScale_pos j
  rw [semiprimePartitionCoefficient,semiprimeSmoothWeight_at_prime X hA] at hp
  have hr := (mul_ne_zero_iff.mp hp).1
  have hw := (mul_ne_zero_iff.mp hp).2
  refine ⟨lt_of_not_ge (fun hn => hr (semiprimeRoughWeight_zero hX hn)),?_,?_⟩
  · have hh : 1 ≤ norm p/semiprimePartitionScale j :=
      le_of_not_gt (fun hh => hw (normPartitionWeight_low hh))
    simpa only [one_mul] using (le_div_iff₀ hA).mp hh
  · have hh : norm p/semiprimePartitionScale j ≤ 2 :=
      le_of_not_gt (fun hh => hw (normPartitionWeight_high hh))
    exact (div_le_iff₀ hA).mp hh

lemma semiprime_kernel_product_range (ℓ : ℤ) (H T : ℝ)
    {X : ℝ} (hX : 0 < X) {p q : Eisenstein}
    (hk : centeredHeightKernel ℓ primeProductEnvelope H T X X (p*q) ≠ 0) :
    X/2 ≤ norm (p*q) ∧ norm (p*q) ≤ 3*X := by
  have hw : primeProductEnvelope (norm (p*q)/X) ≠ 0 := by
    intro hz
    apply hk
    simp only [centeredHeightKernel,hz,mul_zero,zero_mul]
  constructor
  · apply le_of_not_gt
    intro hh
    apply hw
    exact primeProductEnvelope_zero_lower ((div_le_iff₀ hX).mpr (by linarith))
  · apply le_of_not_gt
    intro hh
    apply hw
    exact primeProductEnvelope_zero ((le_div_iff₀ hX).mpr hh.le)

lemma semiprime_piece_lengths (ℓ : ℤ) (H T : ℝ)
    {X : ℝ} (hX : 0 < X) {i j : ℕ} {p q : Eisenstein}
    (hp : semiprimePartitionCoefficient X i p ≠ 0)
    (hq : semiprimePartitionCoefficient X j q ≠ 0)
    (hk : centeredHeightKernel ℓ primeProductEnvelope H T X X (p*q) ≠ 0) :
    X/8 ≤ semiprimePartitionScale i*semiprimePartitionScale j ∧
      semiprimePartitionScale i*semiprimePartitionScale j ≤ 3*X ∧
      X^(2/5:ℝ)/2 ≤ semiprimePartitionScale i ∧
      X^(2/5:ℝ)/2 ≤ semiprimePartitionScale j := by
  obtain ⟨hpr,hpl,hpu⟩ := semiprimePartitionCoefficient_range hX hp
  obtain ⟨hqr,hql,hqu⟩ := semiprimePartitionCoefficient_range hX hq
  obtain ⟨hl,hu⟩ := semiprime_kernel_product_range ℓ H T hX hk
  rw [norm_mul_eq] at hl hu
  have ha := (semiprimePartitionScale_pos i).le
  have hb := (semiprimePartitionScale_pos j).le
  have hlow := mul_le_mul hpl hql hb (norm_nonneg p)
  have hhigh := mul_le_mul hpu hqu (norm_nonneg q) (by positivity : 0 ≤ 2*semiprimePartitionScale i)
  exact ⟨by nlinarith,hlow.trans hu,by linarith,by linarith⟩

theorem eventually_semiprime_upper_range (G : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ A B : ℝ, X^(39/100:ℝ) ≤ B → A*B ≤ 3*X →
      A ≤ B^2/(1+Real.log B)^G := by
  obtain ⟨B₀,hB₀⟩ := eventually_atTop.mp
    (overlap_power_log_saving (by norm_num : (0:ℝ) < 1/10) G 0)
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 39/100)).eventually_ge_atTop B₀,
    eventually_const_mul_rpow_le (by norm_num : (1:ℝ) < 1131/1000) 3]
    with X hX hXB hgap
  intro A B hB hAB
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hB1 : 1 ≤ B := (Real.one_le_rpow hX (by norm_num : (0:ℝ) ≤ 39/100)).trans hB
  have hBp : 0 < B := zero_lt_one.trans_le hB1
  have hL : 0 < 1+Real.log B := by linarith [Real.log_nonneg hB1]
  have hlog : (1+Real.log B)^G ≤ B^(1/10:ℝ) := by
    have hh := hB₀ B (hXB.trans hB)
    simpa only [Nat.mul_zero,pow_zero,div_one,one_mul] using
      (div_le_iff₀ (Real.rpow_pos_of_pos hBp (1/10:ℝ))).mp hh
  have hpow : X^(1131/1000:ℝ) ≤ B^(29/10:ℝ) := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hXp.le (39/100:ℝ)) hB
      (by norm_num : (0:ℝ) ≤ 29/10)
    rw [← Real.rpow_mul hXp.le] at hh
    norm_num at hh ⊢
    exact hh
  have hsize : 3*X ≤ B^(29/10:ℝ) := by
    have hh : 3*X ≤ X^(1131/1000:ℝ) := by simpa only [Real.rpow_one] using hgap
    exact hh.trans hpow
  have hm : (A*B)*(1+Real.log B)^G ≤ B^3 := by
    calc
      _ ≤ (3*X)*(1+Real.log B)^G := mul_le_mul_of_nonneg_right hAB (pow_nonneg hL.le _)
      _ ≤ (3*X)*B^(1/10:ℝ) := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ B^(29/10:ℝ)*B^(1/10:ℝ) := mul_le_mul_of_nonneg_right hsize (by positivity)
      _ = B^3 := by rw [← Real.rpow_add hBp]; norm_num
  apply (le_div_iff₀ (pow_pos hL G)).mpr
  apply (mul_le_mul_iff_right₀ hBp).mp
  convert hm using 1 <;> ring

lemma semiprimePartitionPiece_symm (ℓ : ℤ) (H T X : ℝ) (i j : ℕ) :
    semiprimePartitionPiece ℓ H T X i j = semiprimePartitionPiece ℓ H T X j i := by
  unfold semiprimePartitionPiece
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [mul_comm q p]
  ring

lemma semiprimePartitionPiece_nonzero_lengths (ℓ : ℤ) (H T : ℝ)
    {X : ℝ} (hX : 0 < X) {i j : ℕ}
    (hne : semiprimePartitionPiece ℓ H T X i j ≠ 0) :
    X/8 ≤ semiprimePartitionScale i*semiprimePartitionScale j ∧
      semiprimePartitionScale i*semiprimePartitionScale j ≤ 3*X ∧
      X^(2/5:ℝ)/2 ≤ semiprimePartitionScale i ∧
      X^(2/5:ℝ)/2 ≤ semiprimePartitionScale j := by
  have hex : ∃ p ∈ primeCutoff (3*X), ∃ q ∈ primeCutoff (3*X),
      semiprimePartitionCoefficient X i p*semiprimePartitionCoefficient X j q*
        centeredHeightKernel ℓ primeProductEnvelope H T X X (p*q) ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hne (Finset.sum_eq_zero (fun p hp => Finset.sum_eq_zero (fun q hq => hn p hp q hq)))
  obtain ⟨p,_,q,_,hpq⟩ := hex
  exact semiprime_piece_lengths ℓ H T hX
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hpq).1).1
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hpq).1).2 (mul_ne_zero_iff.mp hpq).2

theorem eventually_semiprime_admissible {η : ℝ} (hη : 0 < η) (G : ℕ) (B₀ : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ (ℓ : ℤ) (H T : ℝ) (i j : ℕ),
      semiprimePartitionScale j ≤ semiprimePartitionScale i →
      semiprimePartitionPiece ℓ H T X i j ≠ 0 →
      B₀ ≤ semiprimePartitionScale j ∧
      (2*semiprimePartitionScale j)^(1/2:ℝ) < semiprimePartitionScale j ∧
      (semiprimePartitionScale j)^(1-η/16) ≤ semiprimePartitionScale i ∧
      semiprimePartitionScale i ≤
        (semiprimePartitionScale j)^2/(1+Real.log (semiprimePartitionScale j))^G := by
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_semiprime_upper_range G,
    eventually_const_mul_rpow_le (by norm_num : (39/100:ℝ) < 2/5) 2,
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 39/100)).eventually_ge_atTop (max B₀ 4)]
    with X hX hupper hlower hlarge
  intro ℓ H T i j hji hne
  have hXp : 0 < X := zero_lt_one.trans_le hX
  obtain ⟨_,hprod,_,hrough⟩ := semiprimePartitionPiece_nonzero_lengths ℓ H T hXp hne
  have hB : X^(39/100:ℝ) ≤ semiprimePartitionScale j := by linarith
  have hB4 : 4 ≤ semiprimePartitionScale j :=
    (le_max_right B₀ 4).trans (hlarge.trans hB)
  have hBp := semiprimePartitionScale_pos j
  refine ⟨(le_max_left B₀ 4).trans (hlarge.trans hB),?_,?_,hupper _ _ hB hprod⟩
  · have hh := Real.rpow_lt_rpow (by positivity : (0:ℝ) ≤ 2*semiprimePartitionScale j)
      (by nlinarith : 2*semiprimePartitionScale j < (semiprimePartitionScale j)^2)
      (by norm_num : (0:ℝ) < 1/2)
    have he : ((semiprimePartitionScale j)^2)^(1/2:ℝ) = semiprimePartitionScale j := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hBp.le]
      norm_num
    rwa [he] at hh
  · apply (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ semiprimePartitionScale j)
      (by linarith : 1-η/16 ≤ (1:ℝ))).trans
    simpa only [Real.rpow_one] using hji

lemma semiprime_log_comparison {X B : ℝ} (hX : 1 ≤ X)
    (hB : X^(39/100:ℝ) ≤ B) :
    (39/100:ℝ)*(1+Real.log X) ≤ 1+Real.log B := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hh := Real.log_le_log (Real.rpow_pos_of_pos hXp (39/100:ℝ)) hB
  rw [Real.log_rpow hXp] at hh
  linarith

lemma eventually_semiprime_height_comparison (U : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ B : ℝ, X^(39/100:ℝ) ≤ B →
      (1+Real.log X)^U ≤ (1+Real.log B)^(U+1) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop ((100/39:ℝ)^(U+1))] with X hX hlarge
  intro B hB
  have hB1 : 1 ≤ B := (Real.one_le_rpow hX (by norm_num : (0:ℝ) ≤ 39/100)).trans hB
  have hL := semiprime_log_comparison hX hB
  have hLX : 0 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hLB : 0 ≤ 1+Real.log B := by linarith [Real.log_nonneg hB1]
  have hinv : 1+Real.log X ≤ (100/39:ℝ)*(1+Real.log B) := by linarith
  have hbig : (100/39:ℝ)^U ≤ 1+Real.log B := by
    have he : (100/39:ℝ)^U = (39/100:ℝ)*(100/39:ℝ)^(U+1) := by
      rw [pow_succ]
      ring
    rw [he]
    nlinarith
  calc
    _ ≤ ((100/39:ℝ)*(1+Real.log B))^U := pow_le_pow_left₀ hLX hinv U
    _ = (100/39:ℝ)^U*(1+Real.log B)^U := mul_pow _ _ _
    _ ≤ (1+Real.log B)*(1+Real.log B)^U :=
      mul_le_mul_of_nonneg_right hbig (pow_nonneg hLB _)
    _ = _ := by rw [pow_succ]; ring

lemma semiprime_bilinear_scale {X A B K : ℝ} (hX : 1 ≤ X)
    (hA : 0 ≤ A) (hB : X^(39/100:ℝ) ≤ B) (hK : 0 ≤ K)
    (hAB : A*B ≤ 3*X) (k : ℕ) :
    K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k ≤
      (K*3^(5/6:ℝ)/(39/100:ℝ)^k)*X^(5/6:ℝ)/(1+Real.log X)^k := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hB1 : 1 ≤ B := (Real.one_le_rpow hX (by norm_num : (0:ℝ) ≤ 39/100)).trans hB
  have hL := semiprime_log_comparison hX hB
  have hLX : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hLB : 0 < 1+Real.log B := by linarith [Real.log_nonneg hB1]
  have hp := Real.rpow_le_rpow (mul_nonneg hA (zero_le_one.trans hB1)) hAB
    (by norm_num : (0:ℝ) ≤ 5/6)
  rw [Real.mul_rpow hA (zero_le_one.trans hB1),Real.mul_rpow (by norm_num) hXp.le] at hp
  calc
    _ ≤ K*(3^(5/6:ℝ)*X^(5/6:ℝ))/(1+Real.log B)^k := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hLB.le _)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hK
    _ ≤ K*(3^(5/6:ℝ)*X^(5/6:ℝ))/((39/100:ℝ)*(1+Real.log X))^k :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos (by positivity) _)
        (pow_le_pow_left₀ (by positivity) hL k)
    _ = _ := by rw [mul_pow]; field_simp

end CubicFirstMoment

end

end OAI
