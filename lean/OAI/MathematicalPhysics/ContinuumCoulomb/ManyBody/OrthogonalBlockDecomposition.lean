import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ThirdOrderBottom

namespace OAI

/-! Block coordinates on an orthogonal subspace and its actual complement.
The high space may retain an unused copy of the low coordinates, since the
physical vectors and trial vectors lie in the kernel of the restriction. -/

noncomputable section
namespace ContinuumCoulomb.Perturbation
open scoped InnerProductSpace
variable {L H : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def orthogonalHighPart (E : L →L[ℝ] H) (R : H →L[ℝ] L) (x : H) : H := x-E (R x)

theorem orthogonalHighPart_kernel (E : L →L[ℝ] H) (R : H →L[ℝ] L)
    (hRE : ∀ p, R (E p) = p) (x : H) : R (orthogonalHighPart E R x) = 0 := by
  simp [orthogonalHighPart,hRE]

theorem orthogonal_assemble (E : L →L[ℝ] H) (R : H →L[ℝ] L) (x : H) :
    E (R x)+orthogonalHighPart E R x = x := by
  unfold orthogonalHighPart
  abel

theorem orthogonalInclusion_norm (E : L →L[ℝ] H) (R : H →L[ℝ] L)
    (hRE : ∀ p, R (E p) = p) (hAdj : ∀ p x, ⟪E p,x⟫_ℝ = ⟪p,R x⟫_ℝ) (p : L) :
    ‖E p‖ = ‖p‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, hAdj,hRE,real_inner_self_eq_norm_sq]

theorem orthogonalParts_norm (E : L →L[ℝ] H) (R : H →L[ℝ] L)
    (hRE : ∀ p, R (E p) = p) (hAdj : ∀ p x, ⟪E p,x⟫_ℝ = ⟪p,R x⟫_ℝ) (x : H) :
    ‖R x‖^2+‖orthogonalHighPart E R x‖^2 = ‖x‖^2 := by
  have h := norm_add_sq_real (E (R x)) (orthogonalHighPart E R x)
  rw [orthogonal_assemble,hAdj,orthogonalHighPart_kernel E R hRE,inner_zero_right,
    orthogonalInclusion_norm E R hRE hAdj] at h
  linarith

theorem orthogonalAssemble_norm (E : L →L[ℝ] H) (R : H →L[ℝ] L)
    (hRE : ∀ p, R (E p) = p) (hAdj : ∀ p x, ⟪E p,x⟫_ℝ = ⟪p,R x⟫_ℝ)
    (p : L) (q : H) (hq : R q = 0) : ‖E p+q‖^2 = ‖p‖^2+‖q‖^2 := by
  rw [norm_add_sq_real,hAdj,hq,inner_zero_right,orthogonalInclusion_norm E R hRE hAdj]
  ring

theorem orthogonalBlock_energy (E : L →L[ℝ] H) (R : H →L[ℝ] L)
    (M A D : H →L[ℝ] H) (C : L →L[ℝ] L) (B : L →L[ℝ] H)
    (hRE : ∀ p, R (E p) = p) (hAdj : ∀ p x, ⟪E p,x⟫_ℝ = ⟪p,R x⟫_ℝ)
    (hM : ∀ x y, ⟪x,M y⟫_ℝ = ⟪M x,y⟫_ℝ)
    (hLow : ∀ p, M (E p) = E (C p)+B p) (hRB : ∀ p, R (B p) = 0)
    (hHigh : ∀ q, R q = 0 → ⟪q,M q⟫_ℝ = penaltyForm A q+⟪q,D q⟫_ℝ)
    (p : L) (q : H) (hq : R q = 0) :
    ⟪E p+q,M (E p+q)⟫_ℝ = lowBlockEnergy C A D B p q := by
  have hEq : ⟪E p,M (E p)⟫_ℝ = ⟪p,C p⟫_ℝ := by
    rw [hLow,inner_add_right,hAdj,hRE,hAdj,hRB,inner_zero_right,add_zero]
  have hqE : ⟪q,E (C p)⟫_ℝ = 0 := by
    rw [real_inner_comm,hAdj,hq,inner_zero_right]
  have hqM : ⟪q,M (E p)⟫_ℝ = ⟪q,B p⟫_ℝ := by
    rw [hLow,inner_add_right,hqE,zero_add]
  have hMq : ⟪E p,M q⟫_ℝ = ⟪q,B p⟫_ℝ := by
    rw [hM,real_inner_comm,hqM]
  simp only [map_add,inner_add_left,inner_add_right,hEq,hqM,hMq,hHigh q hq]
  unfold lowBlockEnergy blockEnergy
  ring

theorem orthogonalBlock_full_energy (E : L →L[ℝ] H) (R : H →L[ℝ] L)
    (M A D : H →L[ℝ] H) (C : L →L[ℝ] L) (B : L →L[ℝ] H)
    (hRE : ∀ p, R (E p) = p) (hAdj : ∀ p x, ⟪E p,x⟫_ℝ = ⟪p,R x⟫_ℝ)
    (hM : ∀ x y, ⟪x,M y⟫_ℝ = ⟪M x,y⟫_ℝ)
    (hLow : ∀ p, M (E p) = E (C p)+B p) (hRB : ∀ p, R (B p) = 0)
    (hHigh : ∀ q, R q = 0 → ⟪q,M q⟫_ℝ = penaltyForm A q+⟪q,D q⟫_ℝ) (x : H) :
    ⟪x,M x⟫_ℝ = lowBlockEnergy C A D B (R x) (orthogonalHighPart E R x) := by
  have h := orthogonalBlock_energy E R M A D C B hRE hAdj hM hLow hRB hHigh
    (R x) (orthogonalHighPart E R x) (orthogonalHighPart_kernel E R hRE x)
  rwa [orthogonal_assemble] at h

end ContinuumCoulomb.Perturbation

end

end OAI
