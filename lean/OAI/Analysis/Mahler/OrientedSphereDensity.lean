import OAI.Analysis.Mahler.NormExteriorPower
import OAI.Analysis.Mahler.SphereNormalization
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

namespace OAI

open scoped BigOperators
open MeasureTheory Metric

namespace Mahler

section Cofactors
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {d : ℕ}

/-- Outward surface coefficient in an ambient orthonormal frame. Division by
`Ω b` fixes the orientation to the specified ambient volume form. At a unit
normal x this is the cofactor formula for the restriction of B to x-perp. -/
noncomputable def orientedDensity (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (Ω : E [⋀^Fin (d+1)]→ₗ[ℝ] ℂ) (B : E [⋀^Fin d]→ₗ[ℝ] ℂ) (x : E) : ℂ :=
  (∑ i : Fin (d+1), (b.repr x i : ℂ) * (-1 : ℂ)^i.val * B (i.removeNth b)) / Ω b

lemma volume_update_basis (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (Ω : E [⋀^Fin (d+1)]→ₗ[ℝ] ℂ) (x : E) (i : Fin (d+1)) :
    Ω (Function.update b i x) = (b.repr x i : ℂ) * Ω b := by
  classical
  nth_rw 1 [← b.sum_repr x]
  rw [Ω.map_update_sum, Finset.sum_eq_single i]
  · rw [Ω.map_update_smul, Function.update_eq_self]
    rfl
  · intro j hj hji
    rw [Ω.map_update_smul, Ω.map_update_self _ hji.symm, smul_zero]
  · simp

lemma volume_cons_remove (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (Ω : E [⋀^Fin (d+1)]→ₗ[ℝ] ℂ) (x : E) (i : Fin (d+1)) :
    Ω (Matrix.vecCons x (i.removeNth b)) =
      (-1 : ℂ)^i.val * (b.repr x i : ℂ) * Ω b := by
  have h := Ω.neg_one_pow_smul_map_insertNth i x (i.removeNth b)
  rw [Fin.insertNth_removeNth, volume_update_basis] at h
  rw [← h]
  simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  ring

/-- The cofactor density of contraction of ambient volume by the outward
radial vector is exactly norm squared, with positive sign. -/
theorem orientedDensity_contraction (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (Ω : E [⋀^Fin (d+1)]→ₗ[ℝ] ℂ) (hΩ : Ω b ≠ 0) (x : E) :
    orientedDensity b Ω (Ω.curryLeft x) x = (‖x‖^2 : ℝ) := by
  unfold orientedDensity
  have hs : (∑ i : Fin (d+1), (b.repr x i : ℂ) * (-1 : ℂ)^i.val *
      Ω.curryLeft x (i.removeNth b)) =
      (∑ i : Fin (d+1), ((b.repr x i)^2 : ℝ)) * Ω b := by
    rw [Complex.ofReal_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [AlternatingMap.curryLeft_apply_apply, volume_cons_remove]
    have hsign : (-1 : ℂ)^i.val * (-1 : ℂ)^i.val = 1 := by
      rw [← mul_pow]; norm_num
    push_cast
    linear_combination (b.repr x i : ℂ)^2 * Ω b * hsign
  rw [hs, mul_div_cancel_right₀ _ hΩ]
  congr 1
  have hn := EuclideanSpace.norm_sq_eq (b.repr x)
  simpa only [LinearIsometryEquiv.norm_map, Real.norm_eq_abs, sq_abs] using hn.symm

lemma orientedDensity_smul (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (Ω : E [⋀^Fin (d+1)]→ₗ[ℝ] ℂ) (B : E [⋀^Fin d]→ₗ[ℝ] ℂ) (x : E) (c : ℂ) :
    orientedDensity b Ω (c • B) x = c * orientedDensity b Ω B x := by
  unfold orientedDensity
  simp only [AlternatingMap.smul_apply, smul_eq_mul]
  rw [← mul_div_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Exterior multiplication by the normal covector, expressed by the
standard alternating sum. It is used only to verify the surface density. -/
noncomputable def normalWedge (x : E) (B : E [⋀^Fin d]→ₗ[ℝ] ℂ) :
    E [⋀^Fin (d+1)]→ₗ[ℝ] ℂ :=
  AlternatingMap.alternatizeUncurryFin ((innerSL ℝ x).toLinearMap.smulRight B)

lemma normalWedge_basis (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (B : E [⋀^Fin d]→ₗ[ℝ] ℂ) (x : E) :
    normalWedge x B b =
      ∑ i : Fin (d+1), (b.repr x i : ℂ) * (-1 : ℂ)^i.val * B (i.removeNth b) := by
  rw [normalWedge, AlternatingMap.alternatizeUncurryFin_apply]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [LinearMap.smulRight_apply, AlternatingMap.smul_apply,
    ContinuousLinearMap.coe_coe, innerSL_apply_apply, OrthonormalBasis.repr_apply_apply,
    real_inner_comm x (b i), Complex.real_smul, zsmul_eq_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one]
  ring

lemma orientedDensity_eq_normalWedge (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (Ω : E [⋀^Fin (d+1)]→ₗ[ℝ] ℂ) (B : E [⋀^Fin d]→ₗ[ℝ] ℂ) (x : E) :
    orientedDensity b Ω B x = normalWedge x B b / Ω b := by
  rw [normalWedge_basis]; rfl

/-- On a unit sphere, the normal wedge evaluates on outward normal followed
by tangent vectors as exactly the boundary form. This checks the sign and
shows which surface restriction the cofactor formula represents. -/
theorem normalWedge_outward_tangent (B : E [⋀^Fin d]→ₗ[ℝ] ℂ) {x : E}
    (hx : ‖x‖ = 1) (v : Fin d → E) (hv : ∀ i, inner ℝ x (v i) = 0) :
    normalWedge x B (Matrix.vecCons x v) = B v := by
  rw [normalWedge, AlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ]
  have hzero : (∑ i : Fin d, (-1 : ℤ)^i.succ.val •
      ((innerSL ℝ x).toLinearMap.smulRight B) (Matrix.vecCons x v i.succ)
        (i.succ.removeNth (Matrix.vecCons x v))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [Matrix.vecCons, LinearMap.smulRight_apply, hv i]
  rw [hzero]
  simp [LinearMap.smulRight_apply, hx, Matrix.vecCons]

lemma topForm_ext_on_basis (b : Module.Basis (Fin (d+1)) ℝ E)
    {A C : E [⋀^Fin (d+1)]→ₗ[ℝ] ℂ} (h : A b = C b) : A = C := by
  classical
  apply b.ext_alternating
  intro v hv
  let e : Equiv.Perm (Fin (d+1)) := Equiv.ofBijective v ⟨hv, Finite.surjective_of_injective hv⟩
  change A (b ∘ e) = C (b ∘ e)
  rw [A.map_perm, C.map_perm, h]

lemma normalWedge_eq_density_smul (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (Ω : E [⋀^Fin (d+1)]→ₗ[ℝ] ℂ) (hΩ : Ω b ≠ 0)
    (B : E [⋀^Fin d]→ₗ[ℝ] ℂ) (x : E) :
    normalWedge x B = orientedDensity b Ω B x • Ω := by
  apply topForm_ext_on_basis b.toBasis
  change normalWedge x B b = orientedDensity b Ω B x * Ω b
  rw [orientedDensity_eq_normalWedge, div_mul_cancel₀ _ hΩ]

/-- The density multiplies the outward area form to give the actual
restriction of B to every tuple of tangent vectors. -/
theorem orientedDensity_spec (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (Ω : E [⋀^Fin (d+1)]→ₗ[ℝ] ℂ) (hΩ : Ω b ≠ 0)
    (B : E [⋀^Fin d]→ₗ[ℝ] ℂ) {x : E} (hx : ‖x‖ = 1)
    (v : Fin d → E) (hv : ∀ i, inner ℝ x (v i) = 0) :
    B v = orientedDensity b Ω B x * Ω (Matrix.vecCons x v) := by
  rw [← normalWedge_outward_tangent B hx v hv, normalWedge_eq_density_smul b Ω hΩ]
  rfl

/-- Cofactor density is independent of the ambient orthonormal frame.
Both frames use the same specified source orientation Ω. -/
theorem orientedDensity_frame_independent
    (b c : OrthonormalBasis (Fin (d+1)) ℝ E)
    (Ω : E [⋀^Fin (d+1)]→ₗ[ℝ] ℂ) (hb : Ω b ≠ 0) (hc : Ω c ≠ 0)
    (B : E [⋀^Fin d]→ₗ[ℝ] ℂ) (x : E) :
    orientedDensity b Ω B x = orientedDensity c Ω B x := by
  have h := congrArg (fun A : E [⋀^Fin (d+1)]→ₗ[ℝ] ℂ => A c)
    (normalWedge_eq_density_smul b Ω hb B x)
  change normalWedge x B c = orientedDensity b Ω B x * Ω c at h
  rw [orientedDensity_eq_normalWedge c, h, mul_div_cancel_right₀ _ hc]

end Cofactors

end Mahler

end OAI
