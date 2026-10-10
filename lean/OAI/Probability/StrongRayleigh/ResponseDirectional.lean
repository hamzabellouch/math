import OAI.Probability.StrongRayleigh.TiltPartition

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Problem336AdditiveD139

theorem hasDerivAt_tilt_weighted_sum
    {F : Type u_1} [Fintype F] [DecidableEq F] (μ : ProbabilityMeasure (F → Bool))
    (h v : F → ℝ) (f : (F → Bool) → ℝ) (t : ℝ) :
    HasDerivAt
      (fun r : ℝ => ∑ x : F → Bool,
        Real.exp (∑ k : F, (h k + r * v k) * boolReal (x k)) *
        ((μ : Measure (F → Bool)) {x}).toReal * f x)
      (∑ k : F, (∑ x : F → Bool,
        Real.exp (∑ j : F, (h j + t * v j) * boolReal (x j)) *
        ((μ : Measure (F → Bool)) {x}).toReal * f x * boolReal (x k)) * v k) t := by
  classical
  have hlin (x : F → Bool) :
      HasDerivAt (fun r : ℝ => ∑ k : F, (h k + r * v k) * boolReal (x k))
        (∑ k : F, v k * boolReal (x k)) t := by
    apply HasDerivAt.fun_sum
    intro k hk
    simpa using (((hasDerivAt_id t).mul_const (v k)).const_add (h k)).mul_const
      (boolReal (x k))
  have hw (x : F → Bool) :=
    (((hlin x).exp).mul_const (((μ : Measure (F → Bool)) {x}).toReal)).mul_const (f x)
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun x _ => hw x)
  convert hs using 1
  try rfl
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro x hx
  ring

private theorem quotient_covariance_sum
    {F : Type u_2} [Fintype F] (Z A : ℝ) (B C v : F → ℝ) (hZ : Z ≠ 0) :
    ((∑ k : F, C k * v k) * Z - A * (∑ k : F, B k * v k)) / Z ^ 2 =
      ∑ k : F, (C k / Z - A / Z * (B k / Z)) * v k := by
  classical
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  field_simp

theorem tiltMean_hasDerivAt_affine_of_ne_zero
    {F : Type u_3} [Fintype F] (μ : ProbabilityMeasure (F → Bool))
    (h v : F → ℝ) (i : F) (t : ℝ)
    (hZ : tiltPartition μ (fun k => h k + t * v k) ≠ 0) :
    HasDerivAt (fun r : ℝ => tiltMean μ (fun k => h k + r * v k) i)
      (∑ k : F, tiltCovariance μ (fun j => h j + t * v j) i k * v k) t := by
  classical
  have hnum := hasDerivAt_tilt_weighted_sum μ h v (fun x => boolReal (x i)) t
  have hden := hasDerivAt_tilt_weighted_sum μ h v (fun _ => 1) t
  simp only [mul_one] at hden
  have hZ' : (∑ x : F → Bool,
      Real.exp (∑ k : F, (h k + t * v k) * boolReal (x k)) *
        ((μ : Measure (F → Bool)) {x}).toReal) ≠ 0 := hZ
  have hquot := hnum.div hden hZ'
  convert hquot using 1 <;> try rfl
  simp only [tiltCovariance, tiltSecondMoment, tiltMean, tiltPartition]
  symm
  exact quotient_covariance_sum _ _ _ _ _ hZ'

theorem tiltMean_hasDerivAt_affine
    {F : Type u_4} [Fintype F] (μ : ProbabilityMeasure (F → Bool))
    (h v : F → ℝ) (i : F) (t : ℝ) :
    HasDerivAt (fun r : ℝ => tiltMean μ (fun k => h k + r * v k) i)
      (∑ k : F, tiltCovariance μ (fun j => h j + t * v j) i k * v k) t :=
  tiltMean_hasDerivAt_affine_of_ne_zero μ h v i t (tiltPartition_ne_zero μ _)

end Problem336AdditiveD139

end

end OAI
