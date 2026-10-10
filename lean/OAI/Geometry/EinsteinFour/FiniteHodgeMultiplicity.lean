import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Basic.Real.Basic

namespace OAI

/-! The finite-dimensional multiplicity identity for a nonzero Hodge
eigenvalue, expressed through its actual codifferential image. -/

namespace PositiveEinsteinFour.Geometry

noncomputable section

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

def hodgeRangePair (C : V →ₗ[ℝ] W) (S : Module.End ℝ V) :
    V →ₗ[ℝ] C.range × C.range :=
  C.rangeRestrict.prod (C.rangeRestrict.comp S)

theorem hodgeRangePair_bijective (C : V →ₗ[ℝ] W) (A S : Module.End ℝ V)
    (κ : ℝ) (hκ : κ ≠ 0)
    (hS : ∀ u, S (S u) = u)
    (hCA : ∀ u, C (A u) = κ • C u)
    (hCSA : ∀ u, C (S (A u)) = 0)
    (hker : ∀ u, C u = 0 → A u = 0)
    (hsplit : ∀ u, A u + S (A (S u)) = κ • u) :
    Function.Bijective (hodgeRangePair C S) := by
  constructor
  · intro u v huv
    have h₁ : C u = C v := congrArg (fun z : C.range × C.range => z.1.val) huv
    have h₂ : C (S u) = C (S v) := congrArg (fun z : C.range × C.range => z.2.val) huv
    have h₃ : A (u - v) = 0 := hker _ (by rw [map_sub, h₁, sub_self])
    have h₄ : A (S (u - v)) = 0 := hker _ (by rw [map_sub, map_sub, h₂, sub_self])
    have h := hsplit (u - v)
    rw [h₃, h₄, map_zero, add_zero] at h
    exact sub_eq_zero.mp ((smul_eq_zero.mp h.symm).resolve_left hκ)
  · rintro ⟨u, v⟩
    obtain ⟨a, ha⟩ := u.property
    obtain ⟨b, hb⟩ := v.property
    refine ⟨κ⁻¹ • (A a + S (A b)), ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      change C (κ⁻¹ • (A a + S (A b))) = u.val
      rw [map_smul, map_add, hCA, hCSA, add_zero, inv_smul_smul₀ hκ, ha]
    · apply Subtype.ext
      change C (S (κ⁻¹ • (A a + S (A b)))) = v.val
      rw [map_smul, map_add, hS, map_smul, map_add, hCSA, hCA,
        zero_add, inv_smul_smul₀ hκ, hb]

theorem finite_hodge_multiplicity [FiniteDimensional ℝ V]
    (C : V →ₗ[ℝ] W) (A S : Module.End ℝ V) (κ : ℝ) (hκ : κ ≠ 0)
    (hS : ∀ u, S (S u) = u)
    (hCA : ∀ u, C (A u) = κ • C u)
    (hCSA : ∀ u, C (S (A u)) = 0)
    (hker : ∀ u, C u = 0 → A u = 0)
    (hsplit : ∀ u, A u + S (A (S u)) = κ • u) :
    Module.finrank ℝ V = 2 * Module.finrank ℝ C.range := by
  let e := LinearEquiv.ofBijective (hodgeRangePair C S)
    (hodgeRangePair_bijective C A S κ hκ hS hCA hCSA hker hsplit)
  simpa only [Module.finrank_prod, two_mul] using e.finrank_eq

end
end PositiveEinsteinFour.Geometry

end OAI
