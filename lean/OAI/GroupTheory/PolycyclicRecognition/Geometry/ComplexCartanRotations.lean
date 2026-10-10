import Mathlib.Algebra.Lie.Weights.Cartan
import Mathlib.Algebra.Lie.Weights.Linear
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace OAI

/-! # Rotations on complex Cartan weight spaces

The imaginary parts of the generalized weights define genuine Lie algebra
automorphisms. Their coefficient vectors lie in a fixed compact torus. These
are the rotations to be removed in the real-triangulable model construction.
-/

noncomputable section
namespace PolycyclicRecognition.ComplexCartan

open LieAlgebra LieModule Module
open scoped DirectSum

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

/-- The generalized Cartan decomposition over the complex numbers. -/
def weightDecomposition :
    (⨁ χ : Weight ℂ H L, (genWeightSpace L χ).toSubmodule) ≃ₗ[ℂ] L := by
  classical
  exact LinearEquiv.ofBijective (DirectSum.coeLinearMap
    (fun χ : Weight ℂ H L => (genWeightSpace L χ).toSubmodule))
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (LieSubmodule.iSupIndep_toSubmodule.mpr (iSupIndep_genWeightSpace' ℂ H L))
      (LieSubmodule.iSup_toSubmodule_eq_top.mpr (iSup_genWeightSpace_eq_top' ℂ H L)))

/-- A scalar on each generalized weight block. -/
def weightOperator (z : Weight ℂ H L → ℂ) : L →ₗ[ℂ] L := by
  classical
  exact (DirectSum.toModule ℂ (Weight ℂ H L) L
    (fun χ => z χ • (genWeightSpace L χ).toSubmodule.subtype)).comp
      (weightDecomposition H).symm.toLinearMap

theorem weightOperator_apply (z : Weight ℂ H L → ℂ) (χ : Weight ℂ H L)
    {x : L} (hx : x ∈ genWeightSpace L χ) : weightOperator H z x = z χ • x := by
  classical
  let S := fun χ : Weight ℂ H L => (genWeightSpace L χ).toSubmodule
  have he : weightDecomposition H
      (DirectSum.lof ℂ (Weight ℂ H L) (fun χ => S χ) χ ⟨x, hx⟩) = x :=
    DirectSum.coeLinearMap_lof S χ ⟨x, hx⟩
  change (DirectSum.toModule ℂ (Weight ℂ H L) L
    (fun χ => z χ • (S χ).subtype)) ((weightDecomposition H).symm x) = _
  rw [← he, LinearEquiv.symm_apply_apply, DirectSum.toModule_lof, he]
  rfl

theorem root_induction {p : L → Prop}
    (hp : ∀ (χ : Weight ℂ H L) (x : L), x ∈ genWeightSpace L χ → p x)
    (hzero : p 0) (hadd : ∀ x y, p x → p y → p (x + y)) (x : L) : p x := by
  have hx : x ∈ ⨆ χ : Weight ℂ H L, (genWeightSpace L χ).toSubmodule := by
    rw [LieSubmodule.iSup_toSubmodule_eq_top.mpr (iSup_genWeightSpace_eq_top' ℂ H L)]
    trivial
  exact Submodule.iSup_induction (fun χ : Weight ℂ H L =>
    (genWeightSpace L χ).toSubmodule) (motive := p) hx hp hzero hadd

/-- The imaginary part, viewed as a purely imaginary complex number. -/
def imaginaryPart : ℂ →ₗ[ℝ] ℂ where
  toFun z := z.im * Complex.I
  map_add' z w := by simp [add_mul]
  map_smul' r z := by simp [mul_assoc]

/-- Rotational scalar on a weight block. -/
def phase (h : H) (χ : H → ℂ) : ℂ := Complex.exp (imaginaryPart (χ h))

omit [FiniteDimensional ℂ L] [H.IsCartanSubalgebra] in
@[simp] theorem norm_phase (h : H) (χ : H → ℂ) : ‖phase H h χ‖ = 1 := by
  simp [phase, imaginaryPart, Complex.norm_exp]

def rotationLinear (h : H) : L →ₗ[ℂ] L := weightOperator H (fun χ => phase H h χ)

theorem rotationLinear_apply (h : H) (χ : Weight ℂ H L) {x : L}
    (hx : x ∈ genWeightSpace L χ) : rotationLinear H h x = phase H h χ • x :=
  weightOperator_apply H _ χ hx

theorem rotationLinear_apply_genWeight (h : H) (χ : H → ℂ) {x : L}
    (hx : x ∈ genWeightSpace L χ) : rotationLinear H h x = phase H h χ • x := by
  by_cases hχ : genWeightSpace L χ = ⊥
  · have hx0 : x = 0 := by simpa only [hχ, LieSubmodule.mem_bot] using hx
    simp [hx0]
  · exact rotationLinear_apply H h ⟨χ, hχ⟩ hx

omit [FiniteDimensional ℂ L] [H.IsCartanSubalgebra] in
@[simp] theorem phase_add_weight (h : H) (χ ψ : H → ℂ) :
    phase H h (χ + ψ) = phase H h χ * phase H h ψ := by
  simp only [phase, Pi.add_apply, map_add, Complex.exp_add]

@[simp] theorem phase_add (h k : H) (χ : Weight ℂ H L) :
    phase H (h + k) χ = phase H h χ * phase H k χ := by
  simp only [phase, map_add, Complex.exp_add]

@[simp] theorem phase_zero (χ : Weight ℂ H L) : phase H 0 χ = 1 := by
  simp [phase]

theorem rotationLinear_map_lie (h : H) (x y : L) :
    rotationLinear H h ⁅x, y⁆ = ⁅rotationLinear H h x, rotationLinear H h y⁆ := by
  apply root_induction H (x := x)
  · intro χ u hu
    apply root_induction H (x := y)
    · intro ψ v hv
      rw [rotationLinear_apply_genWeight H h (χ + ψ)
        (lie_mem_genWeightSpace_of_mem_genWeightSpace hu hv),
        rotationLinear_apply H h χ hu, rotationLinear_apply H h ψ hv,
        phase_add_weight]
      simp only [lie_smul, smul_lie, smul_smul, mul_comm]
    · simp
    · intro v w hv hw
      simp only [lie_add, map_add, hv, hw]
  · simp
  · intro u v hu hv
    simp only [add_lie, map_add, hu, hv]

@[simp] theorem rotationLinear_add_apply (h k : H) (x : L) :
    rotationLinear H (h + k) x = rotationLinear H h (rotationLinear H k x) := by
  apply root_induction H (x := x)
  · intro χ u hu
    rw [rotationLinear_apply H (h + k) χ hu, rotationLinear_apply H k χ hu,
      map_smul, rotationLinear_apply H h χ hu, phase_add, smul_smul, mul_comm]
  · simp
  · intro u v hu hv
    simp only [map_add, hu, hv]

@[simp] theorem rotationLinear_zero_apply (x : L) : rotationLinear H 0 x = x := by
  apply root_induction H (x := x)
  · intro χ u hu
    rw [rotationLinear_apply H 0 χ hu, phase_zero, one_smul]
  · simp
  · intro u v hu hv
    simp only [map_add, hu, hv]

/-- Rotation is an actual Lie automorphism, inverted by negating the Cartan
parameter, with no semisimplicity assumption on the original Cartan action. -/
def rotation (h : H) : L ≃ₗ⁅ℂ⁆ L where
  toFun := rotationLinear H h
  map_add' := (rotationLinear H h).map_add
  map_smul' := (rotationLinear H h).map_smul
  invFun := rotationLinear H (-h)
  left_inv x := by rw [← rotationLinear_add_apply, neg_add_cancel, rotationLinear_zero_apply]
  right_inv x := by rw [← rotationLinear_add_apply, add_neg_cancel, rotationLinear_zero_apply]
  map_lie' := fun {x y} => rotationLinear_map_lie H h x y

omit [FiniteDimensional ℂ L] in
/-- All rotational coefficient vectors lie in one compact set. -/
theorem phase_coefficients_precompact :
    IsCompact {z : Weight ℂ H L → ℂ | ∀ χ, ‖z χ‖ = 1} ∧
      ∀ h : H, (fun χ : Weight ℂ H L => phase H h χ) ∈
        {z : Weight ℂ H L → ℂ | ∀ χ, ‖z χ‖ = 1} := by
  refine ⟨?_, fun h χ => norm_phase H h χ⟩
  have he : {z : Weight ℂ H L → ℂ | ∀ χ, ‖z χ‖ = 1} =
      Set.pi Set.univ (fun _ : Weight ℂ H L => Metric.sphere (0 : ℂ) 1) := by
    ext z
    simp
  rw [he]
  exact isCompact_univ_pi (fun _ => isCompact_sphere 0 1)

end PolycyclicRecognition.ComplexCartan

end

end OAI
