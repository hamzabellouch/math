import OAI.Geometry.RCD.Harmonic.QuadraticUniformBounds

namespace OAI

/-! # The actual radial derivative is close to a coordinate value -/

open Set MeasureTheory
open scoped NNReal ENNReal BigOperators

noncomputable section
namespace RegularPointCoordinates

private theorem gram_action_sq {n : ℕ} (u g : Fin n → ℝ) (j : Fin n)
    {C M : ℝ} (hC : 0 ≤ C)
    (hu : ∀ i, |u i| ≤ C) (hg : ∀ i, |g i| ≤ M ^ 2) :
    ((∑ i, u i * g i) - u j) ^ 2 ≤
      ((n : ℝ) * C ^ 2 * (M ^ 2 + 1)) * ∑ i, |g i - if i = j then 1 else 0| := by
  let e : Fin n → ℝ := fun i => g i - if i = j then 1 else 0
  have he : (∑ i, u i * g i) - u j = ∑ i, u i * e i := by
    simp only [e, mul_sub, Finset.sum_sub_distrib]
    simp [mul_ite]
  have hv : (∑ i, (u i) ^ 2) ≤ (n : ℝ) * C ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin n, C ^ 2 := Finset.sum_le_sum fun i _ => by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (hu i)
      _ = _ := by simp
  have heabs (i : Fin n) : |e i| ≤ M ^ 2 + 1 := by
    exact (abs_sub (g i) (if i = j then 1 else 0)).trans
      (add_le_add (hg i) (by split_ifs <;> norm_num))
  have hesq : (∑ i, (e i) ^ 2) ≤ (M ^ 2 + 1) * ∑ i, |e i| := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have ht := mul_le_mul_of_nonneg_right (heabs i) (abs_nonneg (e i))
    nlinarith [sq_abs (e i)]
  rw [he]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u e
  calc
    _ ≤ (∑ i, (u i) ^ 2) * ∑ i, (e i) ^ 2 := hcs
    _ ≤ ((n : ℝ) * C ^ 2) * ((M ^ 2 + 1) * ∑ i, |e i|) :=
      mul_le_mul hv hesq (Finset.sum_nonneg fun i _ => sq_nonneg _) (by positivity)
    _ = _ := by dsimp only [e]; ring

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Near-orthonormal coordinate gradients identify the gradient of the
quadratic model with the corresponding coordinate values in L2. Together
with the value-to-gradient estimate this proves the raw radial convergence. -/
theorem coordinateQuadratic_raw_error {n : ℕ} {Ω : Set X} (hfin : μ Ω ≠ ∞)
    (u : Fin n → SobolevSpace μ hQ) (C : ℝ≥0) (q : SobolevSpace μ hQ)
    (hub : ∀ j, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (u j) x| ≤ C)
    {M : ℝ} (hM : 0 ≤ M)
    (hgrad : ∀ j, ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ (u j) (u j) x ≤ M ^ 2)
    (j : Fin n) :
    let H := coordinateQuadratic μ hQ u C
    (∫ x in Ω, (localGamma μ hQ q (u j) x - SobolevSpace.toLp μ hQ (u j) x) ^ 2 ∂μ) ≤
      2 * M ^ 2 * (∫ x in Ω, localGamma μ hQ (q - H) (q - H) x ∂μ) +
      2 * ((n : ℝ) * (C : ℝ) ^ 2 * (M ^ 2 + 1)) *
        ∫ x in Ω, ∑ i, |localGamma μ hQ (u i) (u j) x - if i = j then 1 else 0| ∂μ := by
  dsimp only
  let H := coordinateQuadratic μ hQ u C
  let G : X → ℝ := fun x => ∑ i, |localGamma μ hQ (u i) (u j) x - if i = j then 1 else 0|
  have hG : Integrable G (μ.restrict Ω) :=
    integrable_finsetSum Finset.univ fun i _ =>
      ((localGamma_memL1 μ hQ (u i) (u j)).integrableOn.sub (integrableOn_const hfin)).abs
  have herr := ((localGamma_memLp_two_of_bound μ hQ Ω q (u j) (hgrad j)).sub
    ((Lp.memLp (SobolevSpace.toLp μ hQ (u j))).restrict Ω)).integrable_sq
  have he := (localGamma_memL1 μ hQ (q - H) (q - H)).integrableOn (s := Ω)
  have hg := (Filter.eventually_all_finset (Finset.univ : Finset (Fin n))).mpr
    (fun i _ => gamma_abs_le_of_bounds μ hQ (u i) (u j) hM hM (hgrad i) (hgrad j))
  have hb := (Filter.eventually_all_finset (Finset.univ : Finset (Fin n))).mpr (fun i _ => hub i)
  have hpoint : ∀ᵐ x ∂μ.restrict Ω,
      (localGamma μ hQ q (u j) x - SobolevSpace.toLp μ hQ (u j) x) ^ 2 ≤
        (2 * M ^ 2) * localGamma μ hQ (q - H) (q - H) x +
        (2 * ((n : ℝ) * (C : ℝ) ^ 2 * (M ^ 2 + 1))) * G x := by
    filter_upwards [hg, ae_restrict_of_ae hb,
      ae_restrict_of_ae (coordinateQuadratic_gradient μ hQ u C (u j) hub),
      ae_restrict_of_ae (localGamma_sub_left μ hQ q H (u j)),
      ae_restrict_of_ae (localGamma_sq_le μ hQ (q - H) (u j)),
      ae_restrict_of_ae (localGamma_self μ hQ (q - H)), hgrad j]
      with x hgx hbx hHx hsub hcs hself hj
    have hmodel := gram_action_sq (fun i => SobolevSpace.toLp μ hQ (u i) x)
      (fun i => localGamma μ hQ (u i) (u j) x) j C.coe_nonneg
      (fun i => hbx i (Finset.mem_univ i)) (fun i => by
        simpa only [pow_two] using hgx i (Finset.mem_univ i))
    rw [← hHx] at hmodel
    change (localGamma μ hQ H (u j) x - SobolevSpace.toLp μ hQ (u j) x) ^ 2 ≤
      ((n : ℝ) * (C : ℝ) ^ 2 * (M ^ 2 + 1)) * G x at hmodel
    have hraw := hcs.trans (mul_le_mul_of_nonneg_left hj (by rw [hself]; positivity))
    rw [hsub] at hraw
    have hsplit : (localGamma μ hQ q (u j) x - SobolevSpace.toLp μ hQ (u j) x) ^ 2 ≤
        2 * (localGamma μ hQ q (u j) x - localGamma μ hQ H (u j) x) ^ 2 +
        2 * (localGamma μ hQ H (u j) x - SobolevSpace.toLp μ hQ (u j) x) ^ 2 := by
      nlinarith only [sq_nonneg (localGamma μ hQ q (u j) x -
        2 * localGamma μ hQ H (u j) x + SobolevSpace.toLp μ hQ (u j) x)]
    nlinarith only [hsplit, hraw, hmodel]
  have hi := integral_mono_ae herr ((he.const_mul _).add (hG.const_mul _)) hpoint
  simp only [Pi.sub_apply, Pi.add_apply] at hi
  have hsum := integral_add (he.const_mul (2 * M ^ 2))
    (hG.const_mul (2 * ((n : ℝ) * (C : ℝ) ^ 2 * (M ^ 2 + 1))))
  rw [hsum, integral_const_mul, integral_const_mul] at hi
  exact hi

end RegularPointCoordinates

end

end OAI
