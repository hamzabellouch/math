import Mathlib
import OAI.Probability.SKBarriers.Calculus.HessianConvexity
import OAI.Probability.SKBarriers.SpinGlass.FinitePartition
import OAI.Probability.SKBarriers.Gaussian.GaussianZeroMass
import OAI.Probability.SKBarriers.Scalar.RegularAlgebra

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic

def hierarchyPenalty : (n : ℕ) → (Fin n → ℝ) → ℝ →
    (ParameterSpace n → ℝ) → ParameterSpace n → ℝ
  | 0, _, u, f, z => u*f z
  | n+1, m, u, f, z =>
      (u-m (Fin.last n))*f z +
      hierarchyPenalty n (fun i => m i.castSucc) (m (Fin.last n))
        (gaussianStep (m (Fin.last n)) f) z.1

theorem hierarchyPenalty_regular (n : ℕ) (m : Fin n → ℝ) (u : ℝ)
    (hu : 0 ≤ u) (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ u) (hmono : Monotone m)
    (f : ParameterSpace n → ℝ) (hf : RegularConvex f) :
    RegularConvex (hierarchyPenalty n m u f) := by
  induction n generalizing u with
  | zero => exact hf.const_mul hu
  | succ n ih =>
    have hg := hf.gaussianStep (hm (Fin.last n))
    have hmg : Monotone (fun i : Fin n => m i.castSucc) := by
      intro i j hij
      exact hmono (Fin.castSucc_le_castSucc_iff.mpr hij)
    have hp := ih (fun i => m i.castSucc) (m (Fin.last n)) (hm (Fin.last n))
      (fun i => hm i.castSucc) (fun i => hmono (Fin.le_last _)) hmg
      (gaussianStep (m (Fin.last n)) f) hg
    exact ((hf.const_mul (sub_nonneg.mpr (hmu (Fin.last n)))).add
      (hp.compCLM (ContinuousLinearMap.fst ℝ (ParameterSpace n) ℝ)))

def hierarchyPathWeight : (n : ℕ) → (Fin n → ℝ) →
    (ParameterSpace n → ℝ) → ParameterSpace n → ℝ
  | 0, _, _, _ => 1
  | n+1, m, f, z =>
      Real.exp (m (Fin.last n)*(f z-gaussianStep (m (Fin.last n)) f z.1)) *
      hierarchyPathWeight n (fun i => m i.castSucc)
        (gaussianStep (m (Fin.last n)) f) z.1

theorem hierarchyPathWeight_eq (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (u : ℝ) (z : ParameterSpace n) :
    hierarchyPathWeight n m f z = Real.exp (u*f z-hierarchyPenalty n m u f z) := by
  induction n generalizing u with
  | zero => simp only [hierarchyPathWeight,hierarchyPenalty,sub_self,Real.exp_zero]
  | succ n ih =>
    rw [hierarchyPathWeight, ih (fun i => m i.castSucc) _ (m (Fin.last n)), ← Real.exp_add]
    apply congrArg Real.exp
    simp only [hierarchyPenalty]
    ring

theorem hierarchy_fixed_spin_density (n : ℕ) (m : Fin n → ℝ)
    (f U : ParameterSpace n → ℝ) (z : ParameterSpace n) :
    hierarchyPathWeight n m f z * Real.exp (U z-f z) =
      Real.exp (U z-hierarchyPenalty n m 1 f z) := by
  rw [hierarchyPathWeight_eq n m f 1, ← Real.exp_add]
  apply congrArg Real.exp
  ring

def ParameterInvariant (n : ℕ) (f : ParameterSpace n → ℝ) : Prop :=
  ∀ (z : ParameterSpace n) (t : ℝ), f (z+t • parameterAxis n) = f z

theorem parameterDerivative_zero_of_invariant (n : ℕ) (f : ParameterSpace n → ℝ)
    (hf : Differentiable ℝ f) (hfi : ParameterInvariant n f) :
    ∀ z, parameterDerivative n f z = 0 := by
  intro z
  have hd := hasDerivAt_affine_comp f hf z (parameterAxis n) 0
  have he : (fun t : ℝ => f (z+t • parameterAxis n)) = fun _ => f z := funext (hfi z)
  rw [he] at hd
  simpa only [parameterDerivative,zero_smul,add_zero] using
    hd.unique (hasDerivAt_const 0 (f z))

theorem ParameterInvariant.gaussianStep {n : ℕ} {f : ParameterSpace (n+1) → ℝ}
    (hf : ParameterInvariant (n+1) f) (m : ℝ) :
    ParameterInvariant n (gaussianStep m f) := by
  intro z t
  have he (y : ℝ) : f (z+t • parameterAxis n,y) = f (z,y) := by
    simpa only [parameterAxis,Prod.smul_mk,smul_zero,Prod.mk_add_mk,add_zero] using hf (z,y) t
  unfold SK.Analytic.gaussianStep positiveGaussianLogStep
  simp only [he]

theorem hierarchyPenalty_invariant (n : ℕ) (m : Fin n → ℝ) (u : ℝ)
    (f : ParameterSpace n → ℝ) (hf : ParameterInvariant n f) :
    ParameterInvariant n (hierarchyPenalty n m u f) := by
  induction n generalizing u with
  | zero =>
    intro z t
    simp only [hierarchyPenalty,hf z t]
  | succ n ih =>
    have hp := ih (fun i => m i.castSucc) (m (Fin.last n)) _ (hf.gaussianStep (m (Fin.last n)))
    intro z t
    change (u-m (Fin.last n))*f (z+t • parameterAxis (n+1)) +
      hierarchyPenalty n (fun i => m i.castSucc) (m (Fin.last n))
        (gaussianStep (m (Fin.last n)) f) (z.1+t • parameterAxis n) = _
    rw [hf z t, hp z.1 t]
    rfl

theorem hierarchy_fixed_spin_linear_variance
    {S : Type} [Fintype S] [Nonempty S] (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ 1) (hmono : Monotone m)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (hU : ∀ s, U s (parameterAxis n) = 0) (s : S)
    (L : ParameterSpace n →L[ℝ] ℝ) (hL₀ : L (parameterAxis n) = 0)
    {A : ℝ} (hA : 0 ≤ A) (hL : ∀ z, (L z)^2 ≤ A*coordinateSquare n z) :
    let f := affineLogPartition c U
    let V := fun z => (1/2 : ℝ)*coordinateSquare n z-U s z+hierarchyPenalty n m 1 f z
    let Z := ∫ z, Real.exp (-V z) ∂fiberMeasure n 0
    (∫ z, (L z)^2*Real.exp (-V z) ∂fiberMeasure n 0)/Z -
      ((∫ z, L z*Real.exp (-V z) ∂fiberMeasure n 0)/Z)^2 ≤ A := by
  let f := affineLogPartition c U
  have hf : RegularConvex f := ⟨affineLogPartition_boundedDerivs c U,affineLogPartition_convex c U⟩
  have hfi : ParameterInvariant n f := by
    intro z t
    unfold f affineLogPartition
    simp only [map_add,map_smul,hU,smul_eq_mul,mul_zero,add_zero]
  have hg := hierarchyPenalty_regular n m 1 zero_le_one hm hmu hmono f hf
  exact gaussian_convex_tilt_linear_variance n _ hg.1.1 hg.2
    (parameterDerivative_zero_of_invariant n _ (hg.1.1.differentiable (by norm_num))
      (hierarchyPenalty_invariant n m 1 f hfi)) (U s) L (hU s) hL₀ hA hL

end SK.Analytic

end
end
end
end
end
end

end OAI
