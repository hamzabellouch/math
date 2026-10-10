import OAI.GroupTheory.PolycyclicRecognition.Geometry.AlgebraExponential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ConjugationFlow
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace OAI

/-! # Separation of arbitrary exponential preimages near a regular logarithm

If the exponential has trivial kernel, a local injectivity neighborhood
cannot have an additional logarithm outside that neighborhood. Conjugating
the small logarithm by the one-parameter subgroup of the other logarithm
first forces the two logarithms to commute.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Topology

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem exp_eq_of_local_injectivity
    (hker : ∀ a : A, NormedSpace.exp a = 1 → a = 0)
    (U : Set A) (hU : IsOpen U) (hi : Set.InjOn NormedSpace.exp U)
    {a b : A} (hb : b ∈ U) (he : NormedSpace.exp a = NormedSpace.exp b) : a = b := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  let C : ℝ → A := fun t => NormedSpace.exp (t • a) * b * NormedSpace.exp (-(t • a))
  have hC0 : C 0 = b := by simp [C]
  have hcont : Continuous C := by
    apply Continuous.mul
    · exact ((NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)).mul
        continuous_const)
    · exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const).neg
  have hCexp (t : ℝ) : NormedSpace.exp (C t) = NormedSpace.exp b := by
    have hc : Commute (NormedSpace.exp (t • a)) (NormedSpace.exp a) :=
      ((Commute.refl a).smul_left t).exp
    have hz : NormedSpace.exp (t • a) * NormedSpace.exp (-(t • a)) = 1 := by
      rw [← NormedSpace.exp_add_of_commute (Commute.refl (t • a)).neg_right,
        add_neg_cancel, NormedSpace.exp_zero]
    change NormedSpace.exp
      ((algebraExpUnit (t • a) : A) * b * ((algebraExpUnit (t • a))⁻¹ : Aˣ)) = _
    rw [NormedSpace.exp_units_conj, ← he]
    change NormedSpace.exp (t • a) * NormedSpace.exp a * NormedSpace.exp (-(t • a)) = _
    rw [hc.eq, mul_assoc, hz, mul_one]
  have hCU : ∀ᶠ t in 𝓝 (0 : ℝ), C t ∈ U := by
    apply hcont.continuousAt.preimage_mem_nhds
    rw [hC0]
    exact hU.mem_nhds hb
  have hCe : C =ᶠ[𝓝 (0 : ℝ)] fun _ => b :=
    hCU.mono fun t ht => hi ht hb (hCexp t)
  have hd : HasDerivAt C (a * b - b * a) 0 := by
    have hp : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • a)) a 0 := by
      simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using
        (hasDerivAt_exp_smul_const a (0 : ℝ))
    have hn : HasDerivAt (fun t : ℝ => NormedSpace.exp (-(t • a))) (-a) 0 := by
      simpa only [smul_neg, zero_smul, neg_zero, NormedSpace.exp_zero, one_mul] using
        (hasDerivAt_exp_smul_const (-a) (0 : ℝ))
    have hd0 := (hp.mul_const b).mul hn
    have hfun : ((fun t : ℝ => NormedSpace.exp (t • a) * b) *
        fun t : ℝ => NormedSpace.exp (-(t • a))) = C := rfl
    rw [hfun] at hd0
    simpa only [zero_smul, neg_zero, NormedSpace.exp_zero, one_mul, mul_one,
      mul_neg, sub_eq_add_neg] using hd0
  have hz : a * b - b * a = 0 :=
    (hd.congr_of_eventuallyEq hCe.symm).unique (hasDerivAt_const (0 : ℝ) b)
  have hc : Commute a b := sub_eq_zero.mp hz
  have hezero : NormedSpace.exp (a - b) = 1 := by
    rw [sub_eq_add_neg, NormedSpace.exp_add_of_commute hc.neg_right, he,
      ← NormedSpace.exp_add_of_commute (Commute.refl b).neg_right,
      add_neg_cancel, NormedSpace.exp_zero]
  exact sub_eq_zero.mp (hker (a - b) hezero)

/-- Near the identity the inverse-function logarithm is the only logarithm,
even among points outside its initial domain. -/
theorem exists_unique_local_logarithm
    (hker : ∀ a : A, NormedSpace.exp a = 1 → a = 0) :
    ∃ log : A → A, ContinuousAt log 1 ∧ log 1 = 0 ∧
      ∀ᶠ z in 𝓝 (1 : A), NormedSpace.exp (log z) = z ∧
        ∀ a, NormedSpace.exp a = z → a = log z := by
  let d : A ≃L[ℝ] A := ContinuousLinearEquiv.refl ℝ A
  have hd : HasStrictFDerivAt (NormedSpace.exp : A → A) d.toContinuousLinearMap 0 :=
    hasStrictFDerivAt_exp_zero
  let p := hd.toOpenPartialHomeomorph NormedSpace.exp
  have hzero : (0 : A) ∈ p.source := hd.mem_toOpenPartialHomeomorph_source
  have hone : (1 : A) ∈ p.target := by
    simpa only [NormedSpace.exp_zero] using hd.image_mem_toOpenPartialHomeomorph_target
  refine ⟨p.symm, p.continuousAt_symm hone, ?_, ?_⟩
  · have h := p.left_inv hzero
    simpa only [p, HasStrictFDerivAt.toOpenPartialHomeomorph_coe,
      NormedSpace.exp_zero] using h
  · filter_upwards [p.open_target.mem_nhds hone] with z hz
    have hinv : NormedSpace.exp (p.symm z) = z := p.right_inv hz
    refine ⟨hinv, fun a ha => ?_⟩
    exact exp_eq_of_local_injectivity hker p.source p.open_source p.injOn
      (p.map_target hz) (ha.trans hinv.symm)

end PolycyclicRecognition

end

end OAI
