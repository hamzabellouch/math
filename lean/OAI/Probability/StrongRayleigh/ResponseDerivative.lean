import OAI.Probability.StrongRayleigh.TiltPartition

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Topology ComplexConjugate
namespace Problem336AdditiveD139

lemma response_exponent_coordinate {F : Type u_1} [Fintype F]
    (h : F → ℝ) (j : F) (r : ℝ) (x : F → Bool) :
    (∑ k : F, coordinatePerturb h j r k * boolReal (x k)) =
      (∑ k : F, h k * boolReal (x k)) + r * boolReal (x j) := by
  classical
  simp [coordinatePerturb, add_mul, Finset.sum_add_distrib, ite_mul]

lemma hasDerivAt_tiltSum_coordinate {F : Type u_2} [Fintype F] [DecidableEq F]
    (h : F → ℝ) (j : F) (q : (F → Bool) → ℝ) :
    HasDerivAt
      (fun r : ℝ => ∑ x : F → Bool,
        Real.exp (∑ k : F, coordinatePerturb h j r k * boolReal (x k)) * q x)
      (∑ x : F → Bool,
        Real.exp (∑ k : F, h k * boolReal (x k)) * q x * boolReal (x j)) 0 := by
  classical
  simp_rw [response_exponent_coordinate]
  have hd : ∀ x ∈ (Finset.univ : Finset (F → Bool)),
      HasDerivAt (fun r : ℝ =>
        Real.exp ((∑ k : F, h k * boolReal (x k)) + r * boolReal (x j)) * q x)
        (Real.exp (∑ k : F, h k * boolReal (x k)) * q x * boolReal (x j)) 0 := by
    intro x hx
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (((hasDerivAt_id (0 : ℝ)).mul_const (boolReal (x j))).const_add
        (∑ k : F, h k * boolReal (x k))) |>.exp.mul_const (q x)
  exact HasDerivAt.fun_sum hd

lemma tiltMean_hasDerivAt_coordinate_of_pos {F : Type u_3} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i j : F)
    (hpos : 0 < tiltPartition μ h) :
    HasDerivAt (fun r : ℝ => tiltMean μ (coordinatePerturb h j r) i)
      (tiltCovariance μ h i j) 0 := by
  classical
  let m : (F → Bool) → ℝ := fun x => ((μ : Measure (F → Bool)) {x}).toReal
  have hnum := hasDerivAt_tiltSum_coordinate h j (fun x => m x * boolReal (x i))
  have hden := hasDerivAt_tiltSum_coordinate h j m
  have hz : (∑ x : F → Bool,
      Real.exp (∑ k : F, coordinatePerturb h j 0 k * boolReal (x k)) * m x) ≠ 0 := by
    simpa [coordinatePerturb, tiltPartition, m] using ne_of_gt hpos
  have hd := hnum.div hden hz
  apply HasDerivAt.congr_of_eventuallyEq (f := fun r =>
      (∑ x : F → Bool, Real.exp (∑ k : F, coordinatePerturb h j r k * boolReal (x k)) *
         (m x * boolReal (x i))) /
      (∑ x : F → Bool, Real.exp (∑ k : F, coordinatePerturb h j r k * boolReal (x k)) * m x))
  · apply hd.congr_deriv
    simp only [tiltMean, tiltPartition, tiltCovariance, tiltSecondMoment,
      coordinatePerturb, ite_self, add_zero, m, mul_assoc]
    have hne : (∑ x : F → Bool,
      Real.exp (∑ k : F, h k * boolReal (x k)) * ((μ : Measure (F → Bool)) {x}).toReal) ≠ 0 :=
      ne_of_gt hpos
    field_simp [hne]
  · filter_upwards [] with r
    simp [tiltMean, tiltPartition, m, mul_assoc]

lemma tiltMean_hasDerivAt_coordinate {F : Type u_4} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i j : F) :
    HasDerivAt (fun r : ℝ => tiltMean μ (coordinatePerturb h j r) i)
      (tiltCovariance μ h i j) 0 :=
  tiltMean_hasDerivAt_coordinate_of_pos μ h i j (tiltPartition_pos μ h)

end Problem336AdditiveD139

end

end OAI
