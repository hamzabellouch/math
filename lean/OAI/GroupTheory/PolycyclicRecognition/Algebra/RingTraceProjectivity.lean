import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteGroupProjectiveNorm

namespace OAI

/-! # A norm-one element makes a ring coefficient projective

For a finite group acting on a ring which is projective over the integers,
an element with trace one gives an equivariant lift by averaging. Unlike
rational averaging, no division by the group order is used.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {H R : Type} [Group H] [Fintype H] [Ring R] [MulSemiringAction H R]

abbrev ringActionRepresentation : Rep ℤ H :=
  Rep.of (Representation.ofDistribMulAction ℤ H R)

def ringTraceLift (e : R) (E : Rep.{0} ℤ H)
    (l : R →ₗ[ℤ] E) : R →ₗ[ℤ] E where
  toFun x := ∑ h : H, E.ρ h (l (e * (h⁻¹ • x)))
  map_add' x y := by
    simp only [smul_add, mul_add, map_add, Finset.sum_add_distrib]
  map_smul' z x := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro h _
    have hm : e * (h⁻¹ • (z • x)) = z • (e * (h⁻¹ • x)) := by
      rw [smul_comm h⁻¹ z x, mul_smul_comm]
    rw [hm]
    exact (congrArg (E.ρ h) (l.map_smul z (e * (h⁻¹ • x)))).trans
      ((E.ρ h).map_smul z (l (e * (h⁻¹ • x))))

theorem ringTraceLift_equivariant (e : R) (E : Rep.{0} ℤ H)
    (l : R →ₗ[ℤ] E) (g : H) (x : R) :
    ringTraceLift e E l (g • x) = E.ρ g (ringTraceLift e E l x) := by
  change (∑ h : H, E.ρ h (l (e * (h⁻¹ • (g • x))))) =
    E.ρ g (∑ h : H, E.ρ h (l (e * (h⁻¹ • x))))
  rw [map_sum]
  apply Fintype.sum_equiv (Equiv.mulLeft g).symm
  intro h
  change E.ρ h (l (e * (h⁻¹ • (g • x)))) =
    E.ρ g (E.ρ (g⁻¹ * h) (l (e * ((g⁻¹ * h)⁻¹ • x))))
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  simp only [mul_inv_rev, inv_inv, mul_smul]

def ringTraceLiftHom (e : R) (E : Rep.{0} ℤ H) (l : R →ₗ[ℤ] E) :
    ringActionRepresentation (H := H) (R := R) ⟶ E :=
  Rep.ofHom ⟨ringTraceLift e E l, fun g => by
    apply LinearMap.ext
    exact ringTraceLift_equivariant e E l g⟩

theorem ringTraceLiftHom_comp (e : R) (he : ∑ h : H, h • e = 1)
    {E X : Rep.{0} ℤ H} (p : E ⟶ X)
    (f : ringActionRepresentation (H := H) (R := R) ⟶ X)
    (l : R →ₗ[ℤ] E) (hl : p.hom.toLinearMap.comp l = f.hom.toLinearMap) :
    ringTraceLiftHom e E l ≫ p = f := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change p.hom (∑ h : H, E.ρ h (l (e * (h⁻¹ • x)))) = f.hom x
  rw [map_sum]
  have hh (h : H) : p.hom (E.ρ h (l (e * (h⁻¹ • x)))) = f.hom ((h • e) * x) := by
    rw [Rep.hom_comm_apply]
    have hl' := LinearMap.congr_fun hl (e * (h⁻¹ • x))
    change p.hom (l (e * (h⁻¹ • x))) = f.hom (e * (h⁻¹ • x)) at hl'
    rw [hl', ← Rep.hom_comm_apply]
    change f.hom (h • (e * (h⁻¹ • x))) = _
    rw [smul_mul', smul_inv_smul]
  simp_rw [hh]
  rw [← map_sum, ← Finset.sum_mul, he, one_mul]

theorem ringAction_projective_of_trace_one [Module.Projective ℤ R]
    (e : R) (he : ∑ h : H, h • e = 1) :
    Projective (ringActionRepresentation (H := H) (R := R)) where
  factors {E X} f p := by
    intro hp
    obtain ⟨l, hl⟩ := Module.projective_lifting_property p.hom.toLinearMap f.hom.toLinearMap
      ((Rep.epi_iff_surjective p).mp hp)
    exact ⟨ringTraceLiftHom e E l, ringTraceLiftHom_comp e he p f l hl⟩

end PolycyclicRecognition

end

end OAI
