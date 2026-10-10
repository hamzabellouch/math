import OAI.NumberTheory.Ostmann.Construction.PhaseGiantTest

namespace OAI

/-! # The positive uniform-support mean of the Fourier-phase giant -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem densityFourier_reflect {p : ℕ} [NeZero p] (g : ZMod p → ℂ) (x : ZMod p) :
    densityFourier (fun b => g (-b)) x = densityFourier g (-x) := by
  simp only [densityFourier, additiveFourier_reflect]

theorem densityFourier_twice {p : ℕ} [NeZero p] (g : ZMod p → ℂ) (x : ZMod p) :
    densityFourier (densityFourier g) x = g (-x) := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hs : (Real.sqrt (p : ℝ) : ℂ) * (Real.sqrt (p : ℝ) : ℂ) = p := by
    exact_mod_cast (by simpa only [pow_two] using Real.sq_sqrt (Nat.cast_nonneg p))
  unfold densityFourier
  rw [additiveFourier_const_mul, additiveFourier_twice]
  calc
    _ = ((Real.sqrt (p : ℝ) : ℂ) * (Real.sqrt (p : ℝ) : ℂ)) * (p : ℂ)⁻¹ * g (-x) := by ring
    _ = _ := by rw [hs, mul_inv_cancel₀ hp, one_mul]

theorem densityFourier_inverse {p : ℕ} [NeZero p] (g : ZMod p → ℂ) (x : ZMod p) :
    densityFourier (densityFourierInverse g) x = g x := by
  change densityFourier (fun b => densityFourier g (-b)) x = g x
  rw [densityFourier_reflect, densityFourier_twice, neg_neg]

/-- The giant's Fourier transform is exactly the bounded phase specified in
Section 7.1, not merely an energy majorant. -/
theorem phaseGiantPhysical_transform {p : ℕ} [NeZero p] (g : ZMod p → ℂ) (b : ZMod p) :
    densityFourier (phaseGiantPhysical g) b = complexUnitPhase (g b) :=
  densityFourier_inverse _ _

theorem densityFourierInverse_sum {p : ℕ} [NeZero p] (g : ZMod p → ℂ) :
    (∑ x, densityFourierInverse g x) = (Real.sqrt (p : ℝ) : ℂ) * g 0 := by
  have hi := additiveFourier_inversion g 0
  simp only [mul_zero, AddChar.map_zero_eq_one, mul_one] at hi
  unfold densityFourierInverse densityFourier
  have hn : (∑ x, additiveFourier g (-x)) = ∑ x, additiveFourier g x := by
    simpa only [Equiv.neg_apply] using
      (Equiv.neg (ZMod p)).bijective.sum_comp (additiveFourier g)
  rw [← Finset.mul_sum, hn, ← hi]

theorem phaseGiantPhysical_sum_zero {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) (hg : g 0 = 0) : (∑ x, phaseGiantPhysical g x) = 0 := by
  rw [phaseGiantPhysical, densityFourierInverse_sum, hg, complexUnitPhase_zero, mul_zero]

/-- Exact support sum before converting it to a uniform mean. -/
theorem phaseGiantPhysical_support_sum {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) :
    (∑ x ∈ S, phaseGiantPhysical (normalizedResidueTransform S) x) =
      (Real.sqrt (residueVariance S) : ℂ) *
        ((∑ b, ‖normalizedResidueTransform S b‖ : ℝ) : ℂ) := by
  let T := phaseGiantPhysical (normalizedResidueTransform S)
  have hs : (Real.sqrt (residueVariance S) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (residueVariance_pos S hS hSp)).ne'
  have hp := phaseGiantPhysical_pairing (normalizedResidueIndicator S)
    (normalizedResidueTransform_neg S)
  change (∑ x, normalizedResidueIndicator S x * T x) =
    ((∑ b, ‖normalizedResidueTransform S b‖ : ℝ) : ℂ) at hp
  have hzero : ∑ x, T x = 0 :=
    phaseGiantPhysical_sum_zero _ (normalizedResidueTransform_zero S)
  have he (x : ZMod p) : normalizedResidueIndicator S x * T x =
      ((if x ∈ S then T x else 0) - (residueDensity S : ℂ) * T x) /
        (Real.sqrt (residueVariance S) : ℂ) := by
    unfold normalizedResidueIndicator centeredDensity residueDensity
    split_ifs <;> push_cast <;> ring
  simp_rw [he] at hp
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hzero, mul_zero, sub_zero] at hp
  have hsum : (∑ x : ZMod p, if x ∈ S then T x else 0) = ∑ x ∈ S, T x := by simp
  rw [hsum] at hp
  exact ((div_eq_iff hs).mp hp).trans (mul_comm _ _)

/-- A fixed positive fraction of the Fourier L1 mean survives on the actual
residue support. The relaxed constant one half is sufficient downstream. -/
theorem phaseGiantPhysical_uniform_mean_lower {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p)
    (hσ : residueDensity S ≤ 2 / 3) :
    (1 / 2 : ℝ) * ((p : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform S b‖) ≤
      (S.card : ℝ)⁻¹ * ∑ x ∈ S, (phaseGiantPhysical (normalizedResidueTransform S) x).re := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hσpos : 0 < residueDensity S := div_pos hc hp
  have hvar := residueVariance_pos S hS hSp
  have hroot : residueDensity S / 2 ≤ Real.sqrt (residueVariance S) := by
    have hs := Real.sq_sqrt hvar.le
    dsimp only [residueVariance] at hs ⊢
    have hnn := Real.sqrt_nonneg (residueDensity S * (1 - residueDensity S))
    nlinarith
  have hσp : residueDensity S * p = S.card := by
    unfold residueDensity
    exact div_mul_cancel₀ _ hp.ne'
  have hcoeff : (1 / 2 : ℝ) * (p : ℝ)⁻¹ ≤ (S.card : ℝ)⁻¹ * Real.sqrt (residueVariance S) := by
    apply (mul_le_mul_iff_of_pos_right (mul_pos hp hc)).mp
    field_simp
    nlinarith [mul_le_mul_of_nonneg_right hroot hp.le]
  have he := congrArg Complex.re (phaseGiantPhysical_support_sum S hS hSp)
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at he
  rw [he]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoeff
    (Finset.sum_nonneg (s := Finset.univ) fun b _ => norm_nonneg (normalizedResidueTransform S b))

end Ostmann

end OAI
