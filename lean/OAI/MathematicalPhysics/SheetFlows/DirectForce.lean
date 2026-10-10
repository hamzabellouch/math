import Mathlib
import OAI.MathematicalPhysics.SheetFlows.Model

namespace OAI

/-! SheetFlows direct force. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

@[simp] theorem spatialPartial_zero (j : Fin 3) : spatialPartial (0 : Field) j = 0 := by
  funext t x
  simp [spatialPartial]

@[simp] theorem timePartial_zero : timePartial (0 : Field) = 0 := by
  funext t x
  simp [timePartial]

@[simp] theorem laplacian_zero : laplacian (0 : Field) = 0 := by
  funext t x
  simp [laplacian]

@[simp] theorem gradient_zero : gradient (0 : Pressure) = 0 := by
  funext t x j
  simp [gradient]

@[simp] theorem advection_zero : advection (0 : Field) = 0 := by
  funext t x
  simp [advection]

@[simp] theorem mixedDerivative_zero (α : List (Fin 4)) :
    mixedDerivative (0 : Field) α = 0 := by
  induction α with
  | nil => rfl
  | cons j α ih =>
    funext z
    simp [mixedDerivative, ih]

theorem zero_spatially_periodic : SpatiallyPeriodic (0 : Field) := by
  intro t x k
  rfl

theorem zero_smooth : Smooth (0 : Field) := contDiff_const

theorem zero_mean_zero : MeanZero (0 : Field) := by
  intro t
  simp

theorem zero_divergence_free : DivergenceFree (0 : Field) := by
  intro t x
  simp [divergence]

theorem zero_one_periodic : OnePeriodic (0 : Field) := by
  intro t x
  rfl

theorem zero_integer_collars : IntegerCollars (0 : Field) := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro n t x _
  rfl

theorem rational_computable (q : ℚ) : ComputableReal (q : ℝ) := by
  refine ⟨Nat.Partrec.Code.const (Encodable.encode q), ?_⟩
  intro n
  refine ⟨q, ?_, ?_⟩
  · simp [Nat.Partrec.Code.eval_const]
  · simp

theorem zero_effective : Effective (0 : Field) := by
  refine ⟨Nat.Partrec.Code.const (@Encodable.encode (Fin 3 → ℚ) Encodable.finArrow 0), ?_⟩
  intro α c z _ ε hε
  refine ⟨0, ?_, ?_⟩
  · simp [Nat.Partrec.Code.eval_const]
  · simpa using (show (0 : ℝ) < (ε : ℝ) by exact_mod_cast hε)

theorem zero_effective_bounds : EffectiveBounds (0 : Field) := by
  refine ⟨Nat.Partrec.Code.const (Encodable.encode (0 : ℚ)), ?_⟩
  intro α
  refine ⟨0, ?_, le_rfl, ?_⟩
  · simp [Nat.Partrec.Code.eval_const]
  · intro z
    simp

theorem EffectiveBounds.bounded {u : Field} (h : EffectiveBounds u)
    (α : List (Fin 4)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : SpaceTime, ‖mixedDerivative u α z‖ ≤ B := by
  obtain ⟨e, he⟩ := h
  obtain ⟨B, _, hB, hbound⟩ := he α
  exact ⟨(B : ℝ), by exact_mod_cast hB, hbound⟩

theorem zero_classical_solution (ν : ℝ) :
    ClassicalSolution ν (0 : Field) 0 (0 : Pressure) where
  spatial_periodic_u := zero_spatially_periodic
  spatial_periodic_p := by intro t x k; rfl
  continuous_u := fun _ _ => continuous_const.continuousOn
  differentiable_t := fun _ _ _ => differentiableWithinAt_const _
  continuous_t := by
    intro T _
    rw [timePartial_zero]
    exact continuous_const.continuousOn
  differentiable_x := fun _ _ => differentiable_const _
  continuous_x := by
    intro T _ j
    simp only [spatialPartial_zero]
    exact continuous_const.continuousOn
  differentiable_xx := by
    intro t _ j
    rw [spatialPartial_zero]
    exact differentiable_const _
  continuous_xx := by
    intro T _ i j
    simp only [spatialPartial_zero]
    exact continuous_const.continuousOn
  continuous_p := fun _ _ => continuous_const.continuousOn
  differentiable_p := fun _ _ => differentiable_const _
  continuous_px := by
    intro T _
    rw [gradient_zero]
    exact continuous_const.continuousOn
  pressure_mean_zero := by intro t _; simp
  incompressible := fun t _ x => zero_divergence_free t x
  initial := fun _ => rfl
  equation := by intro t _ x; simp

theorem zero_material_flow : MaterialFlow (0 : Field) (fun _ a => a) := by
  refine ⟨fun _ => rfl, fun _ => continuous_const.continuousOn, ?_⟩
  intro a t _
  exact hasDerivWithinAt_const t (Set.Ici 0) a

def directForce (ν : ℝ) (u : Field) : Field :=
  fun t x => timePartial u t x - ν • laplacian u t x

theorem directForce_equation (ν : ℝ) (u : Field)
    (hadv : ∀ t x, advection u t x = 0) (t : ℝ) (x : Space) :
    timePartial u t x + advection u t x =
      -gradient (0 : Pressure) t x + ν • laplacian u t x + directForce ν u t x := by
  simp only [hadv, add_zero, gradient_zero, Pi.zero_apply, neg_zero, zero_add, directForce]
  abel

def eraseAxis (i : Fin 3) : Space →L[ℝ] Space :=
  ContinuousLinearMap.id ℝ Space -
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).smulRight (basis i)

@[simp] theorem eraseAxis_apply (i : Fin 3) (x : Space) :
    eraseAxis i x = x - x i • basis i := rfl

@[simp] theorem eraseAxis_basis (i : Fin 3) : eraseAxis i (basis i) = 0 := by
  simp [eraseAxis, basis]

def axialField (i : Fin 3) (a : ℝ → Space → ℝ) : Field :=
  fun t x => a t (eraseAxis i x) • basis i

theorem fderiv_axialField (i : Fin 3) (a : ℝ → Space → ℝ) (t : ℝ) (x : Space)
    (ha : DifferentiableAt ℝ (a t) (eraseAxis i x)) :
    fderiv ℝ (axialField i a t) x =
      ((fderiv ℝ (a t) (eraseAxis i x)).comp (eraseAxis i)).smulRight (basis i) := by
  exact ((ha.hasFDerivAt.comp x (eraseAxis i).hasFDerivAt).smul_const (basis i)).fderiv

theorem divergence_axialField (i : Fin 3) (a : ℝ → Space → ℝ) (t : ℝ) (x : Space)
    (ha : DifferentiableAt ℝ (a t) (eraseAxis i x)) :
    divergence (axialField i a) t x = 0 := by
  unfold divergence
  apply Finset.sum_eq_zero
  intro j _
  dsimp [spatialPartial]
  rw [fderiv_axialField i a t x ha]
  by_cases h : j = i
  · subst j
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      eraseAxis_basis, map_zero, zero_smul, Pi.zero_apply]
  · simp [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, basis,
      Pi.single_eq_of_ne h]

theorem advection_axialField (i : Fin 3) (a : ℝ → Space → ℝ) (t : ℝ) (x : Space)
    (ha : DifferentiableAt ℝ (a t) (eraseAxis i x)) :
    advection (axialField i a) t x = 0 := by
  dsimp [advection]
  rw [fderiv_axialField i a t x ha]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    axialField, map_smul, eraseAxis_basis, smul_zero, map_zero, zero_smul]

theorem axialField_divergence_free (i : Fin 3) (a : ℝ → Space → ℝ)
    (ha : ∀ t, Differentiable ℝ (a t)) : DivergenceFree (axialField i a) := by
  intro t x
  exact divergence_axialField i a t x (ha t _)

def pulseField (i : Fin 3) (β : ℝ → ℝ) (g : Space → ℝ) : Field :=
  fun t x => β t • (g (eraseAxis i x) • basis i)

def pulseTrajectory (i : Fin 3) (A : ℝ → ℝ) (g : Space → ℝ)
    (a : Space) (t : ℝ) : Space :=
  a + (A t * g (eraseAxis i a)) • basis i

@[simp] theorem eraseAxis_pulseTrajectory (i : Fin 3) (A : ℝ → ℝ)
    (g : Space → ℝ) (a : Space) (t : ℝ) :
    eraseAxis i (pulseTrajectory i A g a t) = eraseAxis i a := by
  simp only [pulseTrajectory, map_add, map_smul, eraseAxis_basis, smul_zero, add_zero]

theorem pulseTrajectory_hasDerivAt (i : Fin 3) (A β : ℝ → ℝ) (g : Space → ℝ)
    (a : Space) (t : ℝ) (hA : HasDerivAt A (β t) t) :
    HasDerivAt (pulseTrajectory i A g a)
      (pulseField i β g t (pulseTrajectory i A g a t)) t := by
  have h := (hasDerivAt_const t a).add
    ((hA.mul_const (g (eraseAxis i a))).smul_const (basis i))
  rw [pulseField, eraseAxis_pulseTrajectory]
  change HasDerivAt (fun s => a + (A s * g (eraseAxis i a)) • basis i)
    (β t • (g (eraseAxis i a) • basis i)) t
  convert h using 1
  first | rfl | simp [smul_smul]

theorem pulse_material_flow (i : Fin 3) (A β : ℝ → ℝ) (g : Space → ℝ)
    (hA₀ : A 0 = 0) (hA : ∀ t, 0 ≤ t → HasDerivAt A (β t) t) :
    MaterialFlow (pulseField i β g) (fun t a => pulseTrajectory i A g a t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    simp [pulseTrajectory, hA₀]
  · intro a t ht
    exact (pulseTrajectory_hasDerivAt i A β g a t (hA t ht)).continuousAt.continuousWithinAt
  · intro a t ht
    exact (pulseTrajectory_hasDerivAt i A β g a t (hA t ht)).hasDerivWithinAt

theorem pulseTrajectory_endpoint (i : Fin 3) (A : ℝ → ℝ) (g : Space → ℝ)
    (a : Space) (T : ℝ) (hT : A T = 1) :
    pulseTrajectory i A g a T = a + g (eraseAxis i a) • basis i := by
  simp [pulseTrajectory, hT]

end Solenoidal
end
end

end OAI
