import OAI.Geometry.IsometricImmersion.Taylor.TaylorCauchyData

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem taylorApproximation_initial_time_hasDerivAt
    (g : MetricField) (a x : ℝ) (u0 u1 : ℝ → ℝ) (N : ℕ) :
    HasDerivAt (fun t => taylorApproximation g a u0 u1 N ![x,t]) (u1 x) a := by
  induction N with
  | zero =>
    have h := (((hasDerivAt_id a).sub_const a).const_mul (u1 x)).const_add (u0 x)
    change HasDerivAt (fun t => u0 x+u1 x*(t-a)) (u1 x) a
    simpa only [mul_one, id_eq] using h
  | succ n ih =>
    let C := nextTaylorCoefficient g a (taylorApproximation g a u0 u1 n) n x
    have hc : HasDerivAt (fun t => C*normalizedTimePower a (n+2) t) 0 a := by
      have h := (normalizedTimePower_hasDerivAt a a (n+1)).const_mul C
      simpa only [normalizedTimePower,sub_self,zero_pow (by omega : n+1 ≠ 0),zero_div,mul_zero] using h
    have h := ih.fun_add hc
    change HasDerivAt (fun t => taylorApproximation g a u0 u1 n ![x,t]+
      C*normalizedTimePower a (n+2) t) (u1 x) a
    simpa only [add_zero] using h

theorem taylorApproximation_initial_velocity_of_differentiable
    (g : MetricField) (a x : ℝ) (u0 u1 : ℝ → ℝ) (N : ℕ)
    (hP : DifferentiableAt ℝ (taylorApproximation g a u0 u1 N) ![x,a]) :
    coordPartial 1 (taylorApproximation g a u0 u1 N) ![x,a] = u1 x := by
  have h := hP.hasFDerivAt.comp_hasDerivAt a (verticalPoint_hasDerivAt x a)
  exact h.unique (taylorApproximation_initial_time_hasDerivAt g a x u0 u1 N)

theorem actual_taylor_Cauchy_of_smooth
    (g : MetricField) (z : Coord → ℝ) (a : ℝ) (N : ℕ) {I : Set ℝ}
    (hI : IsOpen I)
    (hP : ContDiffOn ℝ ∞ (taylorApproximation g a (heightCauchyValue z a)
      (heightCauchyVelocity z a) N) (spatialStrip I)) :
    ∀ x ∈ I,
      taylorApproximation g a (heightCauchyValue z a) (heightCauchyVelocity z a) N ![x,a] = z ![x,a] ∧
      coordPartial 1 (taylorApproximation g a (heightCauchyValue z a) (heightCauchyVelocity z a) N) ![x,a] =
        coordPartial 1 z ![x,a] := by
  intro x hx
  refine ⟨taylorApproximation_value g a x _ _ N,?_⟩
  exact taylorApproximation_initial_velocity_of_differentiable g a x _ _ N
    ((hP.contDiffAt ((spatialStrip_isOpen hI).mem_nhds hx)).differentiableAt (by simp))

end SmoothLocal.Taylor

end

end OAI
