import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarCompactLift

namespace OAI

/-! A rational volume-independent coordinate change for the Euclidean cube
observer. The velocity is pushed forward; the force is subsequently defined
by its Navier--Stokes residual, so anisotropic diffusion causes no restriction. -/

noncomputable section
namespace ForcedComputation.BalancedStretch
open ShearFlows Set
open scoped ContDiff BigOperators

def coefficient (j : Fin 3) : ℝ := if j = 1 then 16 else 1

def linear : Space →L[ℝ] Space :=
  ContinuousLinearMap.pi (fun j => coefficient j •
    (ContinuousLinearMap.proj j : Space →L[ℝ] ℝ))

def inverseLinear : Space →L[ℝ] Space :=
  ContinuousLinearMap.pi (fun j => (coefficient j)⁻¹ •
    (ContinuousLinearMap.proj j : Space →L[ℝ] ℝ))

@[simp] theorem linear_apply (x : Space) (j : Fin 3) :
    linear x j = coefficient j * x j := rfl

@[simp] theorem inverseLinear_apply (x : Space) (j : Fin 3) :
    inverseLinear x j = (coefficient j)⁻¹ * x j := rfl

theorem coefficient_ne (j : Fin 3) : coefficient j ≠ 0 := by
  simp only [coefficient]
  split_ifs <;> norm_num

def stretch : Space ≃L[ℝ] Space :=
  { toLinearEquiv :=
      { toFun := linear
        invFun := inverseLinear
        left_inv := by
          intro x
          ext j
          simp [coefficient_ne]
        right_inv := by
          intro x
          ext j
          simp [coefficient_ne]
        map_add' := linear.map_add
        map_smul' := linear.map_smul }
    continuous_toFun := linear.continuous
    continuous_invFun := inverseLinear.continuous }

@[simp] theorem stretch_apply (x : Space) (j : Fin 3) :
    stretch x j = coefficient j * x j := rfl

@[simp] theorem stretch_symm_apply (x : Space) (j : Fin 3) :
    stretch.symm x j = (coefficient j)⁻¹ * x j := rfl

@[simp] theorem stretch_symm_basis (j : Fin 3) :
    stretch.symm (basis j) = (coefficient j)⁻¹ • basis j := by
  ext k
  by_cases h : k = j
  · subst k
    simp [basis]
  · simp [basis, Pi.single_eq_of_ne h]

def push (a : Space → Space) (x : Space) : Space := stretch (a (stretch.symm x))

def velocity (V : Velocity) : Velocity := fun y => push (fun x => V (y.1, x)) y.2

theorem push_smooth {a : Space → Space} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (push a) :=
  stretch.contDiff.comp (ha.comp stretch.symm.contDiff)

theorem velocity_smooth {V : Velocity} (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (velocity V) :=
  stretch.contDiff.comp
    (hV.comp (contDiff_fst.prodMk (stretch.symm.contDiff.comp contDiff_snd)))

theorem push_derivative (a : Space → Space) (x : Space) (j : Fin 3) :
    derivative (push a) j x =
      (coefficient j)⁻¹ • stretch (derivative a j (stretch.symm x)) := by
  change fderiv ℝ (stretch ∘ (a ∘ stretch.symm)) x (basis j) = _
  rw [stretch.comp_fderiv, stretch.symm.comp_right_fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    stretch_symm_basis, map_smul, derivative]

theorem push_divergence (a : Space → Space) (x : Space) :
    divergence (push a) x = divergence a (stretch.symm x) := by
  unfold divergence
  apply Finset.sum_congr rfl
  intro j _
  rw [push_derivative]
  simp only [Pi.smul_apply, smul_eq_mul, stretch_apply]
  rw [← mul_assoc, inv_mul_cancel₀ (coefficient_ne j), one_mul]

theorem velocity_divergence {V : Velocity}
    (hV : ∀ t x, divergence (fun y => V (t, y)) x = 0) (t : ℝ) (x : Space) :
    divergence (fun y => velocity V (t, y)) x = 0 := by
  exact (push_divergence _ _).trans (hV _ _)

theorem push_zero_iff (a : Space → Space) (x : Space) :
    push a x = 0 ↔ a (stretch.symm x) = 0 := by
  change stretch _ = 0 ↔ _
  exact stretch.map_eq_zero_iff

theorem push_support {a : Space → Space} {K : Set Space}
    (hK : IsClosed K) (ha : tsupport a ⊆ K) :
    tsupport (push a) ⊆ stretch '' K := by
  apply closure_minimal
  · intro x hx
    refine ⟨stretch.symm x, ha ?_, by simp⟩
    exact subset_tsupport _ ((push_zero_iff a x).not.mp hx)
  · exact stretch.toHomeomorph.isClosedMap _ hK

theorem push_compact {a : Space → Space} (ha : HasCompactSupport a) :
    HasCompactSupport (push a) :=
  (ha.image stretch.continuous).of_isClosed_subset (isClosed_tsupport _)
    (push_support (isClosed_tsupport _) (Subset.refl _))

theorem trajectory {V : Velocity} {γ : ℝ → Space} {a t : ℝ}
    (hγ : HasDerivAt γ (V (a + t, γ t)) t) :
    HasDerivAt (fun s => stretch (γ s))
      (velocity V (a + t, stretch (γ t))) t := by
  apply hasDerivAt_pi.mpr
  intro j
  simpa only [velocity, push, stretch_apply, ContinuousLinearEquiv.symm_apply_apply]
    using ((hasDerivAt_pi.mp hγ) j).const_mul (coefficient j)

/-- The cube used by the balanced Euclidean main result. -/
def observer : Set Space := {x | ∀ j : Fin 3, -1 < x j ∧ x j < 2}

theorem nonhalting_outside {x : Plane} (hx : 3 / 16 ≤ x 1) :
    stretch (atHeight x 0) ∉ observer := by
  intro h
  have h₁ := (h (1 : Fin 3)).2
  change coefficient 1 * x 1 < 2 at h₁
  norm_num [coefficient] at h₁
  linarith

theorem halting_inside {x : Plane} (hx : 0 < x 0 ∧ x 0 < 1)
    (hy : 1 / 16 ≤ x 1 ∧ x 1 ≤ 3 / 32) :
    stretch (atHeight x 0) ∈ observer := by
  intro j
  fin_cases j <;> simp only [stretch_apply, coefficient, atHeight]
  · norm_num
    constructor <;> linarith [hx.1, hx.2]
  · norm_num
    constructor <;> linarith [hy.1, hy.2]
  · norm_num

/-- A straight loading path stays outside the cube whenever its endpoint
satisfies `x₀+x₁≥4`. This lets the body use a fixed machine-only normalization. -/
theorem loading_outside {p : Space} (hp : 4 ≤ p 0 + p 1)
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    (1 - θ) • ![4, 0, 0] + θ • p ∉ observer := by
  intro h
  have h₀ := (h (0 : Fin 3)).2
  have h₁ := (h (1 : Fin 3)).2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, zero_add] at h₀ h₁
  have hs : 4 ≤ (1 - θ) * 4 + θ * p 0 + θ * p 1 := by
    nlinarith [mul_nonneg hθ.1 (sub_nonneg.mpr hp)]
  linarith

end ForcedComputation.BalancedStretch

end

end OAI
