import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-! # Short-time averaging for the finite-dimensional semigroup

On a finite-dimensional invariant subspace, strong continuity is norm
continuity. An invertible short-time integral then converts the semigroup
identity into a differential equation. These are supporting lemmas for the
actual contour subspace, with no spectral classification premise.
-/

open Set Filter Topology MeasureTheory
open scoped NNReal

namespace DefocusingNLS

section Averaging

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- A continuous operator family starting at the identity has an invertible
integral over some short positive interval. -/
theorem continuous_exists_unit_integral (f : ℝ → A) (hf : Continuous f)
    (hzero : f 0 = 1) :
    ∃ ε : ℝ, 0 < ε ∧ IsUnit (∫ s in (0 : ℝ)..ε, f s) := by
  have hd : HasDerivAt (fun t : ℝ => ∫ s in (0 : ℝ)..t, f s) (1 : A) 0 := by
    simpa only [hzero] using (hf.integral_hasStrictDerivAt 0 0).hasDerivAt
  have hlim : Tendsto (fun t : ℝ => t⁻¹ • ∫ s in (0 : ℝ)..t, f s)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : A)) := by
    simpa only [zero_add, intervalIntegral.integral_same, sub_zero] using
      hd.tendsto_slope_zero_right
  have hu := hlim.eventually
    (Units.isOpen.mem_nhds (show IsUnit (1 : A) from isUnit_one))
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨ε, hε, hunit⟩ := (hpos.and hu).exists
  change 0 < ε at hε
  refine ⟨ε, hε, ?_⟩
  have hscalar : IsUnit (algebraMap ℝ A ε) :=
    (isUnit_iff_ne_zero.mpr hε.ne').map (algebraMap ℝ A)
  have hproduct := hscalar.mul hunit
  simpa only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    smul_smul, mul_inv_cancel₀ hε.ne', one_smul] using hproduct

/-- The integrated semigroup identity. -/
theorem continuous_semigroup_integral_shift (f : ℝ → A) (hf : Continuous f)
    (hmul : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → f (s + t) = f s * f t)
    {ε s : ℝ} (hε : 0 ≤ ε) (hs : 0 ≤ s) :
    f s * (∫ t in (0 : ℝ)..ε, f t) = ∫ t in s..s + ε, f t := by
  have hmap := (ContinuousLinearMap.mul ℝ A (f s)).intervalIntegral_comp_comm
    (hf.intervalIntegrable (μ := volume) 0 ε)
  change (∫ t in (0 : ℝ)..ε, f s * f t) =
    f s * (∫ t in (0 : ℝ)..ε, f t) at hmap
  rw [← hmap]
  calc
    (∫ t in (0 : ℝ)..ε, f s * f t) = ∫ t in (0 : ℝ)..ε, f (s + t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht0 : 0 ≤ t := (Set.uIcc_of_le hε ▸ ht).1
      exact (hmul s t hs ht0).symm
    _ = ∫ t in s..s + ε, f t := by
      simpa only [add_zero] using intervalIntegral.integral_comp_add_left (a := 0) (b := ε) f s

/-- Norm continuity and the semigroup identity produce a bounded generator,
without a differentiability hypothesis on the semigroup. -/
theorem continuous_semigroup_hasRightDerivative (f : ℝ → A) (hf : Continuous f)
    (hzero : f 0 = 1)
    (hmul : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → f (s + t) = f s * f t) :
    ∃ G : A, ∀ s : ℝ, 0 ≤ s →
      HasDerivWithinAt f (f s * G) (Ici s) s := by
  obtain ⟨ε, hε, hunit⟩ := continuous_exists_unit_integral f hf hzero
  let F : ℝ → A := fun t => ∫ u in (0 : ℝ)..t, f u
  let J : A := ∫ u in (0 : ℝ)..ε, f u
  let G : A := (f ε - 1) * Ring.inverse J
  let H : ℝ → A := fun s => (F (s + ε) - F s) * Ring.inverse J
  have hF (s : ℝ) : HasDerivAt F (f s) s :=
    (hf.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hH (s : ℝ) (hs : 0 ≤ s) : H s = f s := by
    have hshift := continuous_semigroup_integral_shift f hf hmul hε.le hs
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (μ := volume) 0 s) (hf.intervalIntegrable (μ := volume) s (s + ε))
    have hdiff : F (s + ε) - F s = f s * J := by
      change (∫ u in (0 : ℝ)..s + ε, f u) - (∫ u in (0 : ℝ)..s, f u) =
        f s * (∫ u in (0 : ℝ)..ε, f u)
      rw [← hadd, add_sub_cancel_left, hshift]
    dsimp only [H]
    rw [hdiff, mul_assoc, Ring.mul_inverse_cancel J hunit, mul_one]
  refine ⟨G, fun s hs => ?_⟩
  have hnum : HasDerivAt (fun t => F (t + ε) - F t)
      (f (s + ε) - f s) s := by
    convert ((hF (s + ε)).scomp s ((hasDerivAt_id s).add_const ε)).sub (hF s) using 1
    · rfl
    · simp only [one_smul]
  have hd : HasDerivAt H (f s * G) s := by
    convert hnum.mul_const (Ring.inverse J) using 1
    dsimp only [G]
    rw [hmul s ε hs hε.le]
    simp only [mul_sub, one_mul, sub_mul, mul_assoc]
  exact hd.hasDerivWithinAt.congr
    (fun t ht => (hH t (hs.trans ht)).symm) (hH s hs).symm

/-- The bounded generator obtained by averaging represents the semigroup
by an exponential for every nonnegative time. -/
theorem continuous_semigroup_eq_exp (f : ℝ → A) (hf : Continuous f)
    (hzero : f 0 = 1)
    (hmul : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → f (s + t) = f s * f t) :
    ∃ G : A, ∀ t : ℝ, 0 ≤ t → f t = NormedSpace.exp (t • G) := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  obtain ⟨G, hG⟩ := continuous_semigroup_hasRightDerivative f hf hzero hmul
  let g : ℝ → A := fun t => f t * NormedSpace.exp (t • (-G))
  have hg : Continuous g := hf.mul
    (differentiable_exp_smul_const ℝ (-G)).continuous
  have hgderiv (s : ℝ) (hs : 0 ≤ s) : HasDerivWithinAt g 0 (Ici s) s := by
    have h := (hG s hs).mul
      (hasDerivAt_exp_smul_const' (-G) s).hasDerivWithinAt
    convert h using 1
    simp only [neg_mul, mul_neg, mul_assoc, add_neg_cancel]
  refine ⟨G, fun t ht => ?_⟩
  have heq : f t * NormedSpace.exp (t • (-G)) = 1 := by
    have h := constant_of_has_deriv_right_zero (a := 0) (b := t)
      hg.continuousOn (fun s hs => hgderiv s hs.1) t ⟨ht, le_rfl⟩
    simpa only [g, hzero, zero_smul, NormedSpace.exp_zero, mul_one] using h
  have hinv : NormedSpace.exp (t • (-G)) * NormedSpace.exp (t • G) = 1 := by
    rw [smul_neg, ← NormedSpace.exp_add_of_commute ((Commute.refl (t • G)).neg_left),
      neg_add_cancel, NormedSpace.exp_zero]
  calc
    f t = f t * (NormedSpace.exp (t • (-G)) * NormedSpace.exp (t • G)) := by
      rw [hinv, mul_one]
    _ = (f t * NormedSpace.exp (t • (-G))) * NormedSpace.exp (t • G) :=
      (mul_assoc _ _ _).symm
    _ = NormedSpace.exp (t • G) := by rw [heq, one_mul]

end Averaging

section FiniteDimension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Strongly continuous finite-dimensional semigroups are matrix
exponentials; differentiability is a conclusion. -/
theorem finiteDimensional_semigroup_eq_exp (S : ℝ≥0 → E →L[ℂ] E)
    (hS : ∀ x : E, Continuous (fun t => S t x)) (hzero : S 0 = 1)
    (hadd : ∀ s t : ℝ≥0, S (s + t) = S t * S s) :
    ∃ G : E →L[ℂ] E, ∀ t : ℝ≥0, S t = NormedSpace.exp ((t : ℝ) • G) := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hc : Continuous S := continuous_clm_apply.mpr hS
  let f : ℝ → E →L[ℂ] E := fun t => S t.toNNReal
  have hf : Continuous f := hc.comp continuous_real_toNNReal
  have hf0 : f 0 = 1 := by simpa only [f, Real.toNNReal_zero] using hzero
  have hmul (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) : f (s + t) = f s * f t := by
    dsimp only [f]
    rw [Real.toNNReal_add hs ht, add_comm, hadd]
  obtain ⟨G, hG⟩ := continuous_semigroup_eq_exp f hf hf0 hmul
  refine ⟨G, fun t => ?_⟩
  simpa only [f, Real.toNNReal_coe] using hG t t.2

end FiniteDimension

end DefocusingNLS

end OAI
