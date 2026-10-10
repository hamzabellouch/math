import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.FejerTest

lemma sum_fin_val (n : ℕ) :
    (∑ i : Fin n, (i.val : ℝ)) = (n : ℝ) * ((n : ℝ)-1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.cast_add, Nat.cast_one]
    ring

lemma hankel_average (N : ℕ) (hN : 0 < N) :
    (N : ℝ)⁻¹ * ∑ j : Fin N, ∑ k : Fin N,
      (((2*N : ℝ) - j.val - k.val - 1) / (2*N : ℝ)^2) = 1/4 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simp only [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sum_fin_val]
  simp only [← Finset.mul_sum, sum_fin_val]
  field_simp [hn]
  ring

lemma triangular_count (m l : ℕ) :
    (∑ j ∈ Finset.range m, ∑ i ∈ Finset.range m,
      if i = j+l then (1 : ℂ) else 0) = ((m-l : ℕ) : ℂ) := by
  have hs (j : ℕ) : (∑ i ∈ Finset.range m, if i = j+l then (1 : ℂ) else 0) =
      if j+l < m then 1 else 0 := by simp [Finset.mem_range]
  simp only [hs]
  have he : ∀ j : ℕ, j+l < m ↔ j < m-l := by omega
  simp only [he]
  rw [← Finset.sum_filter]
  have hf : (Finset.range m).filter (fun j => j < m-l) = Finset.range (m-l) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  simp [hf]

variable {A : Type*} [CStarAlgebra A]

def powerAverage (w : A) (m : ℕ) : A :=
  ((m : ℂ)⁻¹) • ∑ i ∈ Finset.range m, w^i

def testPolynomial (w : A) (m : ℕ) : A :=
  star (powerAverage w m) * powerAverage w m - ((m : ℂ)⁻¹) • (1 : A)

lemma norm_powerAverage_le (w : A) (m : ℕ) (hm : 0 < m) (hw : ‖w‖ ≤ 1) :
    ‖powerAverage w m‖ ≤ 1 := by
  nontriviality A
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  unfold powerAverage
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (m : ℝ)⁻¹ * ∑ _i ∈ Finset.range m, (1 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt hm'))
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      cases i with
      | zero => simp
      | succ i =>
        exact (norm_pow_le' w (Nat.succ_pos i)).trans
          ((pow_le_pow_left₀ (norm_nonneg _) hw _).trans_eq (one_pow _))
    _ = 1 := by simp [ne_of_gt hm']

lemma testPolynomial_selfAdjoint (w : A) (m : ℕ) :
    IsSelfAdjoint (testPolynomial w m) := by
  unfold testPolynomial
  exact (IsSelfAdjoint.star_mul_self _).sub
    (IsSelfAdjoint.smul (by simp [IsSelfAdjoint]) (IsSelfAdjoint.one A))

lemma norm_testPolynomial_le (w : A) (m : ℕ) (hm : 0 < m) (hw : ‖w‖ ≤ 1) :
    ‖testPolynomial w m‖ ≤ 2 := by
  nontriviality A
  have hq := norm_powerAverage_le w m hm hw
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  calc
    _ ≤ ‖star (powerAverage w m) * powerAverage w m‖ + ‖((m : ℂ)⁻¹) • (1 : A)‖ :=
      norm_sub_le _ _
    _ ≤ 1+1 := by
      apply add_le_add
      · apply (norm_mul_le _ _).trans
        simpa only [norm_star, mul_one] using
          (mul_le_mul hq hq (norm_nonneg _) zero_le_one)
      · rw [norm_smul, norm_inv, Complex.norm_natCast]
        exact (mul_le_mul_of_nonneg_left (le_of_eq (norm_one (α := A))) (by positivity)).trans
          (by simpa using (inv_le_one₀ (by positivity : (0 : ℝ) < m)).mpr hm')
    _ = 2 := by norm_num

variable [PartialOrder A] [StarOrderedRing A]

variable (φ : A →ₚ[ℂ] ℂ) (w : A)

def HaarMoments : Prop :=
  ∀ i j : ℕ, φ (star (w^i) * w^j) = if i=j then 1 else 0

variable (hhaar : HaarMoments φ w)

include hhaar

omit [StarOrderedRing A] in
lemma moment_power (l : ℕ) : φ (w^l) = if l=0 then 1 else 0 := by
  simpa [eq_comm] using hhaar 0 l

omit [StarOrderedRing A] in
lemma moment_square_shift (m l : ℕ) :
    φ (star (powerAverage w m) * powerAverage w m * w^l) =
      (m : ℂ)⁻¹ * (m : ℂ)⁻¹ * ((m-l : ℕ) : ℂ) := by
  change ∀ i j : ℕ, φ (star (w^i) * w^j) = if i=j then 1 else 0 at hhaar
  have hs : star ((m : ℂ)⁻¹) = (m : ℂ)⁻¹ := by simp
  simp only [powerAverage, star_smul, hs, star_sum,
    smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum, map_smul,
    map_sum, smul_eq_mul, mul_assoc, ← pow_add, hhaar]
  simp only [← Finset.mul_sum, ← mul_assoc]
  rw [triangular_count]

omit [StarOrderedRing A] in
lemma moment_square (m : ℕ) (hm : 0 < m) :
    φ (star (powerAverage w m) * powerAverage w m) = (m : ℂ)⁻¹ := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simpa [hm'] using moment_square_shift φ w hhaar m 0

omit [StarOrderedRing A] in
lemma moment_testPolynomial (h1 : φ 1 = 1) (m : ℕ) (hm : 0 < m) :
    φ (testPolynomial w m) = 0 := by
  simp [testPolynomial, moment_square φ w hhaar m hm, h1]

omit [StarOrderedRing A] in
lemma positive_coefficient (m l : ℕ) (hm : 0 < m)
    (hl : 0 < l) (hlm : l < m) :
    φ (testPolynomial w m * w^l) = ((m : ℂ) - (l : ℂ)) / (m : ℂ)^2 := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [testPolynomial, sub_mul, smul_mul_assoc, one_mul, map_sub, map_smul,
    moment_square_shift φ w hhaar, moment_power φ w hhaar,
    ite_eq_right (Nat.ne_of_gt hl), smul_zero, sub_zero]
  rw [Nat.cast_sub (Nat.le_of_lt hlm)]
  field_simp

omit hhaar in
lemma preGNS_mul_norm_le (a b : A) :
    ‖φ.toPreGNS (a*b)‖ ≤ ‖a‖ * ‖φ.toPreGNS b‖ := by
  have hn : ‖φ.leftMulMapPreGNS a‖ ≤ ‖a‖ :=
    LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
  exact ((φ.leftMulMapPreGNS a).le_opNorm (φ.toPreGNS b)).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

omit hhaar in
lemma norm_preGNS_one (h1 : φ 1 = 1) : ‖φ.toPreGNS 1‖ = 1 := by
  simp [PositiveLinearMap.preGNS_norm_def, h1]

lemma norm_preGNS_powerAverage (m : ℕ) (hm : 0 < m) :
    ‖φ.toPreGNS (powerAverage w m)‖ = Real.sqrt ((m : ℝ)⁻¹) := by
  rw [PositiveLinearMap.preGNS_norm_def]
  change Real.sqrt (φ (star (powerAverage w m) * powerAverage w m)).re = _
  rw [moment_square φ w hhaar m hm]
  congr 1
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]

lemma norm_preGNS_testPolynomial (h1 : φ 1 = 1) (m : ℕ) (hm : 0 < m)
    (hw : ‖w‖ ≤ 1) :
    ‖φ.toPreGNS (testPolynomial w m)‖ ≤ 2 * Real.sqrt ((m : ℝ)⁻¹) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs := norm_preGNS_powerAverage φ w hhaar m hm
  have hq := norm_powerAverage_le w m hm hw
  have hi : (m : ℝ)⁻¹ ≤ Real.sqrt ((m : ℝ)⁻¹) := by
    have hp : 0 ≤ (m : ℝ)⁻¹ := by positivity
    have hu : (m : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr hm'
    have hh := Real.sq_sqrt hp
    have := Real.sqrt_nonneg ((m : ℝ)⁻¹)
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hu)]
  calc
    _ ≤ ‖φ.toPreGNS (star (powerAverage w m) * powerAverage w m)‖ +
        ‖φ.toPreGNS (((m : ℂ)⁻¹) • (1 : A))‖ := by
      simpa only [testPolynomial, map_sub] using
        norm_sub_le (φ.toPreGNS (star (powerAverage w m) * powerAverage w m))
          (φ.toPreGNS (((m : ℂ)⁻¹) • (1 : A)))
    _ ≤ Real.sqrt ((m : ℝ)⁻¹) + (m : ℝ)⁻¹ := by
      apply add_le_add
      · apply (preGNS_mul_norm_le φ _ _).trans
        rw [norm_star, hs]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hq (Real.sqrt_nonneg _)
      · simp only [map_smul, norm_smul, norm_inv, Complex.norm_natCast,
          norm_preGNS_one φ h1, mul_one, le_refl]
    _ ≤ _ := by linarith

end Kadison.FejerTest

end

end
end

end OAI
