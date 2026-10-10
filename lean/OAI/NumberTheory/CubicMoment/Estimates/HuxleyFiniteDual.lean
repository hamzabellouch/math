import OAI.NumberTheory.CubicMoment.Estimates.HuxleyGaussianEnergy

namespace OAI

/-! Removing the Gaussian weight on the finite norm ball and applying duality. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def huxleyAdditiveConstant : ℝ :=
  Real.exp 1*huxleyGaussianConstant*(2*Real.pi+3/(2*Real.pi))

lemma huxleyAdditiveConstant_pos : 0 < huxleyAdditiveConstant := by
  have hG := huxleyGaussianConstant_pos
  have hπ := Real.pi_pos
  unfold huxleyAdditiveConstant
  positivity

lemma huxley_coordinate_majorant {Z : ℝ} (hZ : 0 < Z) (n : ℤ × ℤ)
    (hn : norm (ofCoords n.1 n.2) ≤ Z) :
    1 ≤ Real.exp 1*huxleyCoordinateWeight (1/(2*Real.pi*Z)) n := by
  have hE := (huxley_coordinate_energy n.1 n.2).trans (mul_le_mul_of_nonneg_left hn (by norm_num : (0:ℝ) ≤ 2))
  have hm := mul_le_mul_of_nonneg_left hE
    (show 0 ≤ Real.pi*(1/(2*Real.pi*Z)) by positivity)
  have hc : Real.pi*(1/(2*Real.pi*Z))*(2*Z) = 1 := by
    field_simp
  rw [hc] at hm
  unfold huxleyCoordinateWeight
  rw [← Real.exp_add]
  exact Real.one_le_exp_iff.mpr (by nlinarith)

lemma huxley_gaussian_constant_bound {Q Z : ℝ} (hZ : 0 < Z) :
    Real.exp 1*((1/(1/(2*Real.pi*Z)))*huxleyGaussianConstant*
      (1+Q^2/((2/3:ℝ)*(Real.pi/(1/(2*Real.pi*Z)))))) ≤
      huxleyAdditiveConstant*(Q^2+Z) := by
  have hπ := Real.pi_pos
  have hπ0 := Real.pi_ne_zero
  have hZ0 := ne_of_gt hZ
  have he : (1/(1/(2*Real.pi*Z)))*
      (1+Q^2/((2/3:ℝ)*(Real.pi/(1/(2*Real.pi*Z))))) =
      2*Real.pi*Z+(3/(2*Real.pi))*Q^2 := by
    field_simp
  have hscale : 2*Real.pi*Z+(3/(2*Real.pi))*Q^2 ≤
      (2*Real.pi+3/(2*Real.pi))*(Q^2+Z) := by
    have h1 : 0 ≤ (2*Real.pi)*Q^2 := by positivity
    have h2 : 0 ≤ (3/(2*Real.pi))*Z := by positivity
    nlinarith
  calc
    _ = (Real.exp 1*huxleyGaussianConstant)*
        ((1/(1/(2*Real.pi*Z)))*(1+Q^2/((2/3:ℝ)*(Real.pi/(1/(2*Real.pi*Z)))))) := by ring
    _ ≤ (Real.exp 1*huxleyGaussianConstant)*((2*Real.pi+3/(2*Real.pi))*(Q^2+Z)) := by
      rw [he]
      exact mul_le_mul_of_nonneg_left hscale (mul_nonneg (Real.exp_pos _).le huxleyGaussianConstant_pos.le)
    _ = _ := by unfold huxleyAdditiveConstant; ring

lemma huxley_finite_dual_bound (Q Z : ℝ) (hQ : 0 < Q) (hZ : 0 < Z)
    (P : Finset HuxleyLift) (hred : ∀ p ∈ P, p.reduced Q)
    (hzero : ∀ p ∈ P, p.shift = 0)
    (N : Finset Eisenstein) (hN : ∀ n ∈ N, norm n ≤ Z) (v : HuxleyLift → ℂ) :
    (∑ n ∈ N, ‖∑ p ∈ P, v p*huxleyFrequencyPhase p.frequency n‖^2) ≤
      huxleyAdditiveConstant*(Q^2+Z)*∑ p ∈ P, ‖v p‖^2 := by
  classical
  let T := N.image huxleyCoordinateEquiv.symm
  let a := 1/(2*Real.pi*Z)
  have ha : 0 < a := by dsimp [a]; positivity
  have hsum := huxleyGaussianEnergy_summable ha P v
  have hmajor (n : ℤ × ℤ) (hn : n ∈ T) :
      1 ≤ Real.exp 1*huxleyCoordinateWeight a n := by
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hn
    apply huxley_coordinate_majorant hZ
    exact (show norm (huxleyCoordinateEquiv (huxleyCoordinateEquiv.symm k)) ≤ Z by
      simpa only [Equiv.apply_symm_apply] using hN k hk)
  have hweight : (∑ n ∈ T, ‖huxleyDualPolynomial P v n‖^2) ≤
      Real.exp 1*∑ n ∈ T, huxleyCoordinateWeight a n*‖huxleyDualPolynomial P v n‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have h := mul_le_mul_of_nonneg_right (hmajor n hn) (sq_nonneg ‖huxleyDualPolynomial P v n‖)
    simpa only [one_mul,mul_assoc] using h
  have hfinite : (∑ n ∈ T, huxleyCoordinateWeight a n*‖huxleyDualPolynomial P v n‖^2) ≤
      ∑' n, huxleyCoordinateWeight a n*‖huxleyDualPolynomial P v n‖^2 :=
    hsum.sum_le_tsum T (fun n hn => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  calc
    _ = ∑ n ∈ T, ‖huxleyDualPolynomial P v n‖^2 := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro n hn
        have he : ofCoords (huxleyCoordinateEquiv.symm n).1 (huxleyCoordinateEquiv.symm n).2 = n :=
          huxleyCoordinateEquiv.apply_symm_apply n
        simp only [huxleyDualPolynomial,he]
      · exact fun _ _ _ _ h => huxleyCoordinateEquiv.symm.injective h
    _ ≤ Real.exp 1*(∑' n, huxleyCoordinateWeight a n*‖huxleyDualPolynomial P v n‖^2) :=
      hweight.trans (mul_le_mul_of_nonneg_left hfinite (Real.exp_pos _).le)
    _ ≤ Real.exp 1*(((1/a)*huxleyGaussianConstant*(1+Q^2/((2/3:ℝ)*(Real.pi/a))))*
        ∑ p ∈ P, ‖v p‖^2) :=
      mul_le_mul_of_nonneg_left (huxleyGaussianEnergy_bound ha Q hQ P hred hzero v) (Real.exp_pos _).le
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (huxley_gaussian_constant_bound hZ)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma huxley_finite_primal_bound (Q Z : ℝ) (hQ : 0 < Q) (hZ : 0 < Z)
    (P : Finset HuxleyLift) (hred : ∀ p ∈ P, p.reduced Q)
    (hzero : ∀ p ∈ P, p.shift = 0)
    (N : Finset Eisenstein) (hN : ∀ n ∈ N, norm n ≤ Z) (v : Eisenstein → ℂ) :
    (∑ p ∈ P, ‖∑ n ∈ N, v n*huxleyFrequencyPhase p.frequency n‖^2) ≤
      huxleyAdditiveConstant*(Q^2+Z)*∑ n ∈ N, ‖v n‖^2 :=
  finite_additive_sieve_duality P N _
    (mul_nonneg huxleyAdditiveConstant_pos.le (by positivity))
    (huxley_finite_dual_bound Q Z hQ hZ P hred hzero N hN) v

end CubicFirstMoment

end

end OAI
