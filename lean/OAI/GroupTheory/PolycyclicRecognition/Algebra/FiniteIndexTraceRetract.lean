import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SubgroupInductionDimension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RingTraceProjectivity
import Mathlib.GroupTheory.Index

namespace OAI

/-! # Relative trace-one coefficients are retracts of induced restrictions

The averaging is over a finite coset space, so the subgroup itself may be
infinite. The trace element is invariant under that subgroup.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits Representation
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G R : Type} [Group G] [Ring R] [MulSemiringAction G R]
variable (N : Subgroup G)

/-- Right multiplication is well-defined on right cosets without normality. -/
def subgroupRightCosetMulEquiv (g : G) : subgroupRightCosets N ≃ subgroupRightCosets N where
  toFun := Quotient.map (fun x => x * g) (by
    intro x y h
    apply (QuotientGroup.rightRel_apply).mpr
    simpa [mul_inv_rev, mul_assoc] using (QuotientGroup.rightRel_apply).mp h)
  invFun := Quotient.map (fun x => x * g⁻¹) (by
    intro x y h
    apply (QuotientGroup.rightRel_apply).mpr
    simpa [mul_inv_rev, mul_assoc] using (QuotientGroup.rightRel_apply).mp h)
  left_inv c := by induction c using Quotient.inductionOn; simp [mul_assoc]
  right_inv c := by induction c using Quotient.inductionOn; simp [mul_assoc]

@[simp]
theorem subgroupRightCosetMulEquiv_mk (g x : G) :
    subgroupRightCosetMulEquiv N g (subgroupRightCoset N x) =
      subgroupRightCoset N (x * g) := rfl

theorem induced_mk_mul_left (A : Rep.{0} ℤ N) (n : N) (g : G) (a : A) :
    IndV.mk N.subtype A.ρ ((n : G) * g) (A.ρ n a) = IndV.mk N.subtype A.ρ g a := by
  apply (subgroupInductionEquiv N ℤ A).injective
  change subgroupInductionCoordinates N ℤ A _ = subgroupInductionCoordinates N ℤ A _
  rw [subgroupInductionCoordinates_mk, subgroupInductionCoordinates_mk,
    subgroupRightCoset_mul, subgroupRightPart_mul]
  simp [mul_inv_rev, map_mul, Module.End.mul_apply]

variable (e : R) (he : ∀ n : N, (n : G) • e = e)

abbrev relativeTraceRepresentation : Rep ℤ G := ringActionRepresentation (H := G) (R := R)

def relativeTraceTerm (g : G) : R →ₗ[ℤ]
    Rep.ind N.subtype (Rep.res N.subtype (relativeTraceRepresentation (G := G) (R := R))) :=
  (IndV.mk N.subtype (Rep.res N.subtype (relativeTraceRepresentation (G := G) (R := R))).ρ g).comp
    ((LinearMap.mulLeft ℤ e).comp ((relativeTraceRepresentation (G := G) (R := R)).ρ g))

include he in
theorem relativeTraceTerm_mul (n : N) (g : G) :
    relativeTraceTerm N e ((n : G) * g) = relativeTraceTerm N e g := by
  ext b
  change IndV.mk _ _ ((n : G) * g) (e * (((n : G) * g) • b)) =
    IndV.mk _ _ g (e * (g • b))
  rw [mul_smul]
  have h : e * ((n : G) • (g • b)) = (n : G) • (e * (g • b)) := by
    rw [smul_mul', he]
  rw [h]
  exact induced_mk_mul_left N (Rep.res N.subtype (relativeTraceRepresentation (G := G) (R := R))) n g _

def relativeTraceCosetTerm (c : subgroupRightCosets N) : R →ₗ[ℤ]
    Rep.ind N.subtype (Rep.res N.subtype (relativeTraceRepresentation (G := G) (R := R))) :=
  Quotient.lift (relativeTraceTerm N e) (by
    intro g h hgh
    let n : N := ⟨h * g⁻¹, (QuotientGroup.rightRel_apply).mp hgh⟩
    have hn : (n : G) * g = h := by simp [n, mul_assoc]
    rw [← hn]
    exact (relativeTraceTerm_mul N e he n g).symm) c

@[simp]
theorem relativeTraceCosetTerm_mk (g : G) :
    relativeTraceCosetTerm N e he (subgroupRightCoset N g) = relativeTraceTerm N e g := rfl

include he in
theorem relativeTraceCosetTerm_action (g : G) (c : subgroupRightCosets N) (b : R) :
    relativeTraceCosetTerm N e he c (g • b) =
      (Rep.ind N.subtype (Rep.res N.subtype (relativeTraceRepresentation (G := G) (R := R)))).ρ g
        (relativeTraceCosetTerm N e he (subgroupRightCosetMulEquiv N g c) b) := by
  induction c using Quotient.inductionOn with
  | _ x =>
    change IndV.mk _ _ x (e * (x • (g • b))) =
      (Representation.ind _ _) g (IndV.mk _ _ (x * g) (e * ((x * g) • b)))
    rw [ind_mk, mul_inv_cancel_right, mul_smul]

variable [Fintype (subgroupRightCosets N)]

def relativeTraceSectionLinear : R →ₗ[ℤ]
    Rep.ind N.subtype (Rep.res N.subtype (relativeTraceRepresentation (G := G) (R := R))) :=
  ∑ c : subgroupRightCosets N, relativeTraceCosetTerm N e he c

def relativeTraceSection : relativeTraceRepresentation (G := G) (R := R) ⟶
    Rep.ind N.subtype (Rep.res N.subtype (relativeTraceRepresentation (G := G) (R := R))) :=
  Rep.ofHom ⟨relativeTraceSectionLinear N e he, fun g => by
    ext b
    simp only [relativeTraceSectionLinear]
    erw [LinearMap.comp_apply]
    change (∑ c : subgroupRightCosets N, relativeTraceCosetTerm N e he c) (g • b) =
      (Rep.ind N.subtype (Rep.res N.subtype (relativeTraceRepresentation (G := G) (R := R)))).ρ g
        ((∑ c : subgroupRightCosets N, relativeTraceCosetTerm N e he c) b)
    erw [LinearMap.sum_apply, LinearMap.sum_apply]
    rw [map_sum]
    apply Fintype.sum_equiv (subgroupRightCosetMulEquiv N g)
    intro c
    exact relativeTraceCosetTerm_action N e he g c b⟩

def relativeTraceCounit :
    Rep.ind N.subtype (Rep.res N.subtype (relativeTraceRepresentation (G := G) (R := R))) ⟶
      relativeTraceRepresentation (G := G) (R := R) :=
  (Rep.indResHomEquiv N.subtype _ _).symm (𝟙 _)

omit [Fintype (subgroupRightCosets N)] in
@[simp]
theorem relativeTraceCounit_mk (g : G) (b : R) :
    (relativeTraceCounit N (R := R)).hom (IndV.mk _ _ g b) = g⁻¹ • b := by
  simp [relativeTraceCounit, Rep.indResHomEquiv, IndV.mk]

include he in
theorem relativeTraceSection_counit
    (htrace : ∑ c : subgroupRightCosets N,
      (subgroupRightRepresentative N c)⁻¹ • e = 1) :
    relativeTraceSection N e he ≫ relativeTraceCounit N = 𝟙 _ := by
  apply Rep.hom_ext
  apply IntertwiningMap.ext
  ext b
  change (relativeTraceCounit N).hom (relativeTraceSectionLinear N e he b) = b
  simp only [relativeTraceSectionLinear, LinearMap.sum_apply]
  rw [map_sum]
  have hc (c : subgroupRightCosets N) :
      (relativeTraceCounit N).hom (relativeTraceCosetTerm N e he c b) =
        ((subgroupRightRepresentative N c)⁻¹ • e) * b := by
    rw [← subgroupRightRepresentative_coset N c, relativeTraceCosetTerm_mk]
    change (relativeTraceCounit N).hom (IndV.mk _ _ _ _) = _
    rw [relativeTraceCounit_mk]
    change (subgroupRightRepresentative N c)⁻¹ •
      (e * ((subgroupRightRepresentative N c) • b)) = _
    rw [smul_mul', inv_smul_smul, subgroupRightRepresentative_coset]
  simp_rw [hc]
  rw [← Finset.sum_mul, htrace, one_mul]

include he in
theorem relativeTrace_dimension_le (d : ℕ)
    (htrace : ∑ c : subgroupRightCosets N,
      (subgroupRightRepresentative N c)⁻¹ • e = 1)
    (hd : HasProjectiveDimensionLE
      (Rep.res N.subtype (relativeTraceRepresentation (G := G) (R := R))) d) :
    HasProjectiveDimensionLE (relativeTraceRepresentation (G := G) (R := R)) d := by
  let := subgroupInduction_projectiveDimension_le N _ d hd
  let r : Retract (relativeTraceRepresentation (G := G) (R := R))
      (Rep.ind N.subtype (Rep.res N.subtype (relativeTraceRepresentation (G := G) (R := R)))) :=
    ⟨relativeTraceSection N e he, relativeTraceCounit N,
      relativeTraceSection_counit N e he htrace⟩
  exact r.hasProjectiveDimensionLT (d + 1)

end PolycyclicRecognition

end

end OAI
