import OAI.InformationTheory.BooleanNoise.Rearrangement
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

def noiseFlow (F : Cube n → ℝ) (t : ℝ) : Cube n → ℝ :=
  noiseOperator (Real.exp (-t)) F

private theorem noiseKernel_flip_derivative_term (u : ℝ)
    (x y : Cube n) (i : Fin n) :
    (∏ j ∈ Finset.univ.erase i,
      if x j = y j then (1 + u) / 2 else (1 - u) / 2) *
      (if x i = y i then -u / 2 else u / 2) =
        -((noiseKernel u x y - noiseKernel u (flip i x) y) / 2) := by
  have hrest : (∏ j ∈ Finset.univ.erase i,
      if (flip i x) j = y j then (1 + u) / 2 else (1 - u) / 2) =
      ∏ j ∈ Finset.univ.erase i,
        if x j = y j then (1 + u) / 2 else (1 - u) / 2 := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    simp only [flip, LeanBlast.GotsmanLinial.flip, Function.update_of_ne hji]
  rw [noiseKernel_split_coord u x y i, noiseKernel_split_coord u (flip i x) y i, hrest]
  cases hx : x i <;> cases hy : y i <;>
    simp [flip, LeanBlast.GotsmanLinial.flip, hx] <;> ring

private theorem hasDerivAt_noise_factor (x y : Cube n) (i : Fin n) (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
      if x i = y i then (1 + Real.exp (-s)) / 2 else (1 - Real.exp (-s)) / 2)
      (if x i = y i then -Real.exp (-t) / 2 else Real.exp (-t) / 2) t := by
  have hu : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_id t).neg.exp
  by_cases hxy : x i = y i
  · simp only [ite_eq_left hxy]
    exact (hu.const_add 1).div_const 2
  · simp only [ite_eq_right hxy]
    simpa using (hu.const_sub 1).div_const 2

theorem hasDerivAt_noiseKernel_flow (x y : Cube n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => noiseKernel (Real.exp (-s)) x y)
      (-(∑ i : Fin n,
        (noiseKernel (Real.exp (-t)) x y -
          noiseKernel (Real.exp (-t)) (flip i x) y) / 2)) t := by
  have h := HasDerivAt.fun_finsetProd
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hasDerivAt_noise_factor x y i t)
  convert! h using 1
  simp only [smul_eq_mul, noiseKernel_flip_derivative_term, Finset.sum_neg_distrib]

theorem cubeDerivative_noiseOperator (u : ℝ) (F : Cube n → ℝ)
    (i : Fin n) (x : Cube n) :
    cubeDerivative i (noiseOperator u F) x =
      ∑ y, ((noiseKernel u x y - noiseKernel u (flip i x) y) / 2) * F y := by
  simp [cubeDerivative, noiseOperator, sub_div, sub_mul,
    div_mul_eq_mul_div, Finset.sum_sub_distrib, Finset.sum_div]

theorem hasDerivAt_noiseFlow (F : Cube n → ℝ) (t : ℝ) (x : Cube n) :
    HasDerivAt (fun s : ℝ => noiseFlow F s x)
      (-(∑ i : Fin n, cubeDerivative i (noiseFlow F t) x)) t := by
  have h := HasDerivAt.fun_sum
    (fun y (_ : y ∈ (Finset.univ : Finset (Cube n))) =>
      (hasDerivAt_noiseKernel_flow x y t).mul_const (F y))
  convert! h using 1
  simp only [noiseFlow, cubeDerivative_noiseOperator, neg_mul,
    Finset.sum_mul, Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_comm

theorem continuous_noiseFlow (F : Cube n → ℝ) (x : Cube n) :
    Continuous (fun t : ℝ => noiseFlow F t x) := by
  exact continuous_iff_continuousAt.mpr fun t => (hasDerivAt_noiseFlow F t x).continuousAt

@[simp]
theorem noiseFlow_zero (F : Cube n → ℝ) : noiseFlow F 0 = F := by
  funext x
  simp [noiseFlow]

theorem cubeAverage_noiseFlow (F : Cube n → ℝ) (t : ℝ) :
    cubeAverage (noiseFlow F t) = cubeAverage F :=
  cubeAverage_noiseOperator _ _

theorem meanVariance_noiseFlow (F : Cube n → ℝ) (t : ℝ) :
    meanVariance (noiseFlow F t) = meanVariance F := by
  simp only [meanVariance, cubeAverage_noiseFlow]

theorem isInterior_noiseFlow (F : Cube n → ℝ) (hF : IsSignValued F)
    (hnc : ∃ x y, F x ≠ F y) {t : ℝ} (ht : 0 < t) :
    IsInterior (noiseFlow F t) := by
  apply noiseOperator_isInterior (Real.exp_pos _).le _ hF hnc
  rw [Real.exp_lt_one_iff]
  linarith

theorem isIncreasing_noiseFlow (F : Cube n → ℝ) (hF : IsIncreasing F)
    {t : ℝ} (ht : 0 ≤ t) : IsIncreasing (noiseFlow F t) := by
  apply isIncreasing_noiseOperator ⟨(Real.exp_pos _).le, ?_⟩ hF
  rw [Real.exp_le_one_iff]
  linarith

theorem hasDerivAt_entropyAverage_noiseFlow_of_isInterior
    (F : Cube n → ℝ) (t : ℝ) (hinterior : IsInterior (noiseFlow F t)) :
    HasDerivAt (fun s : ℝ => entropyAverage (noiseFlow F s))
      (dissipation (noiseFlow F t)) t := by
  have h := (HasDerivAt.fun_sum
    (fun x (_ : x ∈ (Finset.univ : Finset (Cube n))) =>
      (hasDerivAt_entropy (hinterior x)).comp t (hasDerivAt_noiseFlow F t x))).div_const
      ((2 : ℝ) ^ n)
  convert! h using 1
  simp only [dissipation, cubeAverage, neg_mul_neg, Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_comm

theorem hasDerivAt_entropyAverage_noiseFlow
    (F : Cube n → ℝ) (hF : IsSignValued F) (hnc : ∃ x y, F x ≠ F y)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => entropyAverage (noiseFlow F s))
      (dissipation (noiseFlow F t)) t :=
  hasDerivAt_entropyAverage_noiseFlow_of_isInterior F t (isInterior_noiseFlow F hF hnc ht)

theorem hasDerivAt_informationDeficit_noiseFlow_of_isInterior
    (F : Cube n → ℝ) (t : ℝ) (hinterior : IsInterior (noiseFlow F t)) :
    HasDerivAt (fun s : ℝ => informationDeficit (noiseFlow F s))
      (-dissipation (noiseFlow F t)) t := by
  simpa only [informationDeficit, cubeAverage_noiseFlow] using
    (hasDerivAt_entropyAverage_noiseFlow_of_isInterior F t hinterior).const_sub
      (entropy (cubeAverage F))

theorem hasDerivAt_informationDeficit_noiseFlow
    (F : Cube n → ℝ) (hF : IsSignValued F) (hnc : ∃ x y, F x ≠ F y)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => informationDeficit (noiseFlow F s))
      (-dissipation (noiseFlow F t)) t :=
  hasDerivAt_informationDeficit_noiseFlow_of_isInterior F t (isInterior_noiseFlow F hF hnc ht)

theorem continuous_entropyAverage_noiseFlow (F : Cube n → ℝ) :
    Continuous (fun t : ℝ => entropyAverage (noiseFlow F t)) := by
  apply Continuous.div_const
  exact continuous_finsetSum _ fun x _ => continuous_entropy.comp (continuous_noiseFlow F x)

theorem continuous_informationDeficit_noiseFlow (F : Cube n → ℝ) :
    Continuous (fun t : ℝ => informationDeficit (noiseFlow F t)) := by
  simp only [informationDeficit, cubeAverage_noiseFlow]
  exact continuous_const.sub (continuous_entropyAverage_noiseFlow F)

theorem entropyAverage_eq_zero_of_signValued (F : Cube n → ℝ) (hF : IsSignValued F) :
    entropyAverage F = 0 := by
  have hzero : ∀ x, entropy (F x) = 0 := by
    intro x
    rcases hF x with h | h <;> rw [h] <;> simp
  simp only [entropyAverage, cubeAverage, hzero, Finset.sum_const_zero, zero_div]

theorem tendsto_entropyAverage_noiseFlow_zero
    (F : Cube n → ℝ) (hF : IsSignValued F) :
    Tendsto (fun t : ℝ => entropyAverage (noiseFlow F t)) (𝓝 0) (𝓝 0) := by
  simpa only [noiseFlow_zero, entropyAverage_eq_zero_of_signValued F hF] using
    (continuous_entropyAverage_noiseFlow F).continuousAt.tendsto (x := 0)

theorem tendsto_entropyAverage_noiseFlow_zero_right
    (F : Cube n → ℝ) (hF : IsSignValued F) :
    Tendsto (fun t : ℝ => entropyAverage (noiseFlow F t)) (𝓝[>] 0) (𝓝 0) :=
  (tendsto_entropyAverage_noiseFlow_zero F hF).mono_left nhdsWithin_le_nhds

theorem entropyAverage_noiseFlow_pos
    (F : Cube n → ℝ) (hF : IsSignValued F) (hnc : ∃ x y, F x ≠ F y)
    {t : ℝ} (ht : 0 < t) : 0 < entropyAverage (noiseFlow F t) := by
  apply div_pos _ (cube_denominator_pos n)
  exact Finset.sum_pos
    (fun x _ => entropy_pos (isInterior_noiseFlow F hF hnc ht x)) Finset.univ_nonempty

theorem meanVariance_noiseFlow_pos
    (F : Cube n → ℝ) (hF : IsSignValued F) (hnc : ∃ x y, F x ≠ F y) (t : ℝ) :
    0 < meanVariance (noiseFlow F t) := by
  rw [meanVariance_noiseFlow]
  exact meanVariance_pos_of_signValued_nonconstant hF hnc

end LeanBlast.CourtadeKumar

end

end OAI
