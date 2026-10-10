import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Tactic

namespace OAI

/-! # Continuous homomorphisms in smooth exponential coordinates

Only differentiability of multiplication at the identity, its two unit
identities, and the straight-line one-parameter law are needed. The scaling
limit of multiplication proves additivity without an automatic-smoothness
assumption on the homomorphism.
-/

noncomputable section

namespace PolycyclicRecognition

open Filter
open scoped Topology

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The derivative of exponential-coordinate multiplication at the origin
is addition, by differentiating its unit identities along the two axes. -/
theorem hasDerivAt_scaled_product (m : V → V → V)
    (hm : DifferentiableAt ℝ (fun p : V × V => m p.1 p.2) (0, 0))
    (hleft : ∀ x, m 0 x = x) (hright : ∀ x, m x 0 = x) (x y : V) :
    HasDerivAt (fun t : ℝ => m (t • x) (t • y)) (x + y) 0 := by
  let T := fderiv ℝ (fun p : V × V => m p.1 p.2) (0, 0)
  have hd : HasFDerivAt (fun p : V × V => m p.1 p.2) T (0, 0) := hm.hasFDerivAt
  have hx : T (x, 0) = x := by
    have h := hd.comp_hasDerivAt_of_eq 0
      (((hasDerivAt_id (0 : ℝ)).smul_const x).prodMk (hasDerivAt_const 0 (0 : V)))
      (by simp)
    simp only [Function.comp_def, hright] at h
    simpa only [one_smul] using h.unique (by simpa using (hasDerivAt_id (0 : ℝ)).smul_const x)
  have hy : T (0, y) = y := by
    have h := hd.comp_hasDerivAt_of_eq 0
      ((hasDerivAt_const 0 (0 : V)).prodMk ((hasDerivAt_id (0 : ℝ)).smul_const y))
      (by simp)
    simp only [Function.comp_def, hleft] at h
    simpa only [one_smul] using h.unique (by simpa using (hasDerivAt_id (0 : ℝ)).smul_const y)
  have h := hd.comp_hasDerivAt_of_eq 0
    (((hasDerivAt_id (0 : ℝ)).smul_const x).prodMk
      ((hasDerivAt_id (0 : ℝ)).smul_const y)) (by simp)
  have hT : T (x, y) = x + y := by
    rw [show (x, y) = (x, 0) + (0, y) by simp, map_add, hx, hy]
  simpa only [Function.comp_def, id_eq, one_smul, hT] using h

/-- A continuous multiplicative-coordinate map which is linear on each
radial line is additive, hence defines a continuous real-linear map. -/
theorem exists_linearMap_of_coordinate_hom (m : V → V → V)
    (hm : DifferentiableAt ℝ (fun p : V × V => m p.1 p.2) (0, 0))
    (hleft : ∀ x, m 0 x = x) (hright : ∀ x, m x 0 = x)
    (f : V → W) (hf : Continuous f)
    (hmul : ∀ x y, f (m x y) = f x + f y)
    (hsmul : ∀ (t : ℝ) x, f (t • x) = t • f x) :
    ∃ A : V →L[ℝ] W, ∀ x, A x = f x := by
  have hadd (x y : V) : f (x + y) = f x + f y := by
    have hd := hasDerivAt_scaled_product m hm hleft hright x y
    have hlim : Tendsto (fun t : ℝ => t⁻¹ • m (t • x) (t • y))
        (𝓝[≠] 0) (𝓝 (x + y)) := by
      simpa only [zero_add, zero_smul, hleft, sub_zero] using hd.tendsto_slope_zero
    have hfLim := (hf.continuousAt (x := x + y)).tendsto.comp hlim
    have hevent : (fun t : ℝ => f (t⁻¹ • m (t • x) (t • y))) =ᶠ[𝓝[≠] 0]
        (fun _ => f x + f y) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := ht
      rw [hsmul, hmul, hsmul, hsmul, ← smul_add, smul_smul, inv_mul_cancel₀ ht0, one_smul]
    exact tendsto_nhds_unique hfLim (tendsto_const_nhds.congr' hevent.symm)
  exact ⟨{ toLinearMap := { toFun := f, map_add' := hadd, map_smul' := hsmul }
           cont := hf }, fun _ => rfl⟩

end PolycyclicRecognition

end

end OAI
