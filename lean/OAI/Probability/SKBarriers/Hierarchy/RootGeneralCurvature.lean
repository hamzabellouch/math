import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.RootHessianIdentity

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem rootGradient_gaussianStep (n : ℕ) {f : ParameterSpace (n+1) → ℝ}
    (hf : BoundedDerivs f) (m : ℝ) (z : ParameterSpace n) :
    rootGradient n (gaussianStep m f) z=gaussianAverage m f (rootGradient (n+1) f) z :=
  fderiv_gaussianStep_apply hf m z (parameterAxis n)

theorem rootGradient_gaussianStep_bound (n : ℕ) {f : ParameterSpace (n+1) → ℝ}
    (hf : BoundedDerivs f) (m : ℝ) {B : ℝ} (hB : ∀ z, |rootGradient (n+1) f z| ≤ B)
    (z : ParameterSpace n) : |rootGradient n (gaussianStep m f) z| ≤ B := by
  rw [rootGradient_gaussianStep n hf m z]
  simpa only [Real.norm_eq_abs] using gaussianAverage_norm_le hf m (g := rootGradient (n+1) f) (C := B)
    (fun z => by simpa only [Real.norm_eq_abs] using hB z) z

theorem hierarchyAverage_abs_le (n : ℕ) (m : Fin n → ℝ)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (g : ParameterSpace n → ℝ)
    {B : ℝ} (hB : ∀ z, |g z| ≤ B) (x : ℝ) : |hierarchyAverage n m f g x| ≤ B := by
  induction n with
  | zero => exact hB x
  | succ n ih =>
    apply ih (fun i => m i.castSucc) (hf.gaussianStep _) _
    intro z
    simpa only [Real.norm_eq_abs] using gaussianAverage_norm_le hf (m (Fin.last n)) (g := g) (C := B)
      (fun z => by simpa only [Real.norm_eq_abs] using hB z) z

theorem hierarchyPressure_rootGradient (n : ℕ) (m : Fin n → ℝ)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (x : ℝ) :
    rootGradient 0 (hierarchyPressure n m f) x=
      hierarchyAverage n m f (rootGradient n f) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change rootGradient 0 (hierarchyPressure n (fun i => m i.castSucc)
      (gaussianStep (m (Fin.last n)) f)) x= _
    rw [ih (fun i => m i.castSucc) (hf.gaussianStep _)]
    simp only [hierarchyAverage,funext (rootGradient_gaussianStep n hf (m (Fin.last n)))]

theorem hierarchyPressure_rootGradient_bound (n : ℕ) (m : Fin n → ℝ)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) {B : ℝ}
    (hB : ∀ z, |rootGradient n f z| ≤ B) (x : ℝ) :
    |rootGradient 0 (hierarchyPressure n m f) x| ≤ B := by
  rw [hierarchyPressure_rootGradient n m hf x]
  exact hierarchyAverage_abs_le n m hf _ hB x

theorem rootGradient_penalty_bound_general (n : ℕ) (m : Fin n → ℝ)
    {u B : ℝ} (hu : 0 ≤ u) (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ u) (hmono : Monotone m)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f)
    (hB : ∀ z, |rootGradient n f z| ≤ B)
    (z : ParameterSpace n) : |rootGradient n (hierarchyPenalty n m u f) z| ≤ u*B := by
  induction n generalizing u with
  | zero =>
    rw [rootGradient_penalty_zero m u hf,abs_mul,abs_of_nonneg hu]
    exact mul_le_mul_of_nonneg_left (hB z) hu
  | succ n ih =>
    let q := m (Fin.last n)
    have hb := ih (fun i => m i.castSucc) (hm (Fin.last n)) (fun i => hm i.castSucc)
      (fun i => hmono (Fin.le_last _))
      (fun _ _ hij => hmono (Fin.castSucc_le_castSucc_iff.mpr hij))
      (hf.gaussianStep q) (rootGradient_gaussianStep_bound n hf q hB) z.1
    rw [rootGradient_penalty_succ n m u hf]
    calc
      _ ≤ |(u-q)*rootGradient (n+1) f z|+
        |rootGradient n (hierarchyPenalty n (fun i => m i.castSucc) q (gaussianStep q f)) z.1| := abs_add_le _ _
      _ ≤ (u-q)*B+q*B := add_le_add (by
        rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr (hmu _))]
        exact mul_le_mul_of_nonneg_left (hB z) (sub_nonneg.mpr (hmu _))) hb
      _ = u*B := by ring

theorem hierarchyPressure_rootHessian_bound (n : ℕ) (m : Fin n → ℝ)
    {u B C : ℝ} (hu : 0 ≤ u) (hB0 : 0 ≤ B)
    (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ u) (hmono : Monotone m)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f)
    (hB : ∀ z, |rootGradient n f z| ≤ B) (hC : ∀ z, |rootHessian n f z| ≤ C)
    (x : ℝ) : |rootHessian 0 (hierarchyPressure n m f) x| ≤ C+2*u*B^2 := by
  rw [hierarchyPressure_rootHessian n m u hf]
  apply hierarchyAverage_abs_le n m hf
  intro z
  have hP := rootGradient_penalty_bound_general n m hu hm hmu hmono hf hB z
  have hsq : (rootGradient n f z)^2 ≤ B^2 := by
    nlinarith [(abs_le.mp (hB z)).1,(abs_le.mp (hB z)).2,sq_nonneg (B-rootGradient n f z),
      sq_nonneg (B+rootGradient n f z)]
  calc
    |rootResponse n m u f z| ≤ |rootHessian n f z|+|u*(rootGradient n f z)^2|+
        |rootGradient n f z*rootGradient n (hierarchyPenalty n m u f) z| := by
      unfold rootResponse
      exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ C+u*B^2+B*(u*B) := by
      rw [abs_mul u _,abs_of_nonneg hu,abs_of_nonneg (sq_nonneg (rootGradient n f z)),
        abs_mul (rootGradient n f z) _]
      exact add_le_add (add_le_add (hC z) (mul_le_mul_of_nonneg_left hsq hu))
        (mul_le_mul (hB z) hP (abs_nonneg _) hB0)
    _ = C+2*u*B^2 := by ring

end SK.Analytic

end
end

end OAI
