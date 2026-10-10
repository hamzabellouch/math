import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.RootHessianIdentity

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem rootGradient_penalty_bound (n : ℕ) (m : Fin n → ℝ)
    {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1)
    (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ u) (hmono : Monotone m)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (h : RootSpinCurvature n f)
    (z : ParameterSpace n) : |rootGradient n (hierarchyPenalty n m u f) z| ≤ u := by
  induction n generalizing u with
  | zero =>
    rw [rootGradient_penalty_zero m u hf,abs_mul,abs_of_nonneg hu.1]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (h.bounds z).1 hu.1
  | succ n ih =>
    let q := m (Fin.last n)
    have hq : q ∈ Icc (0:ℝ) 1 := ⟨hm _,(hmu _).trans hu.2⟩
    have hb := ih (fun i => m i.castSucc) hq (fun i => hm i.castSucc)
      (fun i => hmono (Fin.le_last _))
      (fun _ _ hij => hmono (Fin.castSucc_le_castSucc_iff.mpr hij))
      (hf.gaussianStep q) (h.gaussianStep hf hq) z.1
    rw [rootGradient_penalty_succ n m u hf]
    calc
      _ ≤ |(u-q)*rootGradient (n+1) f z|+
        |rootGradient n (hierarchyPenalty n (fun i => m i.castSucc) q (gaussianStep q f)) z.1| := abs_add_le _ _
      _ ≤ (u-q)*1+q := add_le_add (by
        rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr (hmu _))]
        exact mul_le_mul_of_nonneg_left (h.bounds z).1 (sub_nonneg.mpr (hmu _))) hb
      _ = u := by ring

theorem rootGradient_penalty_shift_bound (n : ℕ) (m : Fin n → ℝ)
    {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1)
    (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ u) (hmono : Monotone m)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (h : RootSpinCurvature n f)
    (z : ParameterSpace n) (t : ℝ) :
    |rootGradient n (hierarchyPenalty n m u f) (z+t • parameterAxis n)-
      rootGradient n (hierarchyPenalty n m u f) z| ≤ u*|t| := by
  induction n generalizing u with
  | zero =>
    rw [rootGradient_penalty_zero m u hf,rootGradient_penalty_zero m u hf,← mul_sub,
      abs_mul,abs_of_nonneg hu.1]
    exact mul_le_mul_of_nonneg_left (rootShift_gradient_bound 0 hf h z t) hu.1
  | succ n ih =>
    let q := m (Fin.last n)
    have hq : q ∈ Icc (0:ℝ) 1 := ⟨hm _,(hmu _).trans hu.2⟩
    have hb := ih (fun i => m i.castSucc) hq (fun i => hm i.castSucc)
      (fun i => hmono (Fin.le_last _))
      (fun _ _ hij => hmono (Fin.castSucc_le_castSucc_iff.mpr hij))
      (hf.gaussianStep q) (h.gaussianStep hf hq) z.1
    rw [rootGradient_penalty_succ n m u hf,rootGradient_penalty_succ n m u hf]
    change |(u-q)*rootGradient (n+1) f (z+t • parameterAxis (n+1))+
      rootGradient n (hierarchyPenalty n (fun i => m i.castSucc) q (gaussianStep q f))
        (z.1+t • parameterAxis n)-
      ((u-q)*rootGradient (n+1) f z+
      rootGradient n (hierarchyPenalty n (fun i => m i.castSucc) q (gaussianStep q f)) z.1)|≤_
    set a := rootGradient (n+1) f (z+t • parameterAxis (n+1))
    set b := rootGradient (n+1) f z
    set c := rootGradient n (hierarchyPenalty n (fun i => m i.castSucc) q (gaussianStep q f))
      (z.1+t • parameterAxis n)
    set d := rootGradient n (hierarchyPenalty n (fun i => m i.castSucc) q (gaussianStep q f)) z.1
    calc
      _ = |(u-q)*(a-b)+(c-d)| := by congr 1; ring
      _ ≤ |(u-q)*(a-b)|+|c-d| := abs_add_le _ _
      _ ≤ (u-q)*|t|+q*|t| := add_le_add (by
        rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr (hmu _))]
        exact mul_le_mul_of_nonneg_left (rootShift_gradient_bound (n+1) hf h z t)
          (sub_nonneg.mpr (hmu _))) hb
      _ = u*|t| := by ring

end SK.Analytic

end
end

end OAI
