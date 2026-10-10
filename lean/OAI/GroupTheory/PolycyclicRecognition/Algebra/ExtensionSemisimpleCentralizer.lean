import OAI.GroupTheory.PolycyclicRecognition.Lattices.SemisimpleCentralizerCorrection
import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer

namespace OAI

/-! # Semisimple centralizers in a smooth nilpotent-kernel extension

For an abelian quotient, every quotient element has a lift whose conjugation
on the nilpotent kernel centralizes the semisimple part of a prescribed lift.
The correcting element lies in the actual completed kernel.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff IsMulCommutative
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q]

omit [LieRing.IsNilpotent L] in
theorem extension_conjAct_inl (E : GroupExtension L G Q) (u : L) :
    E.conjAct (E.inl u) = MulAut.conj u := by
  apply DFunLike.ext
  intro x
  apply E.inl_injective
  rw [E.inl_conjAct_comm]
  change E.inl u * E.inl x * (E.inl u)⁻¹ = E.inl (u * x * u⁻¹)
  rw [map_mul, map_mul, map_inv]

def semisimpleActionCentralizer (E : GroupExtension L G Q) (S : L ≃ₗ⁅ℝ⁆ L) : Subgroup G :=
  (Subgroup.centralizer {PolynomialExponentialCoordinates.groupAutomorphism (P := C) S}).comap
    E.conjAct

omit [LieRing.IsNilpotent L] in
theorem extension_outer_conjugation_identity [IsMulCommutative Q]
    (E : GroupExtension L G Q)
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)) (t g : G) :
    ∃ u : L, (polynomialInnerLieEquiv u).toLinearMap *
        (polynomialModelLieEquiv (E.conjAct t) (hsmooth t)).toLinearMap =
      (polynomialModelLieEquiv (E.conjAct g) (hsmooth g)).toLinearEquiv.conjRingEquiv
        (polynomialModelLieEquiv (E.conjAct t) (hsmooth t)).toLinearMap := by
  let A := polynomialModelLieEquiv (E.conjAct t) (hsmooth t)
  let B := polynomialModelLieEquiv (E.conjAct g) (hsmooth g)
  have ha (x : L) : A x = E.conjAct t x := polynomialModelLieEquiv_apply _ _ x
  have hb (x : L) : B x = E.conjAct g x := polynomialModelLieEquiv_apply _ _ x
  have hbi (x : L) : B.symm x = (E.conjAct g)⁻¹ x := by
    apply B.injective
    change B (B.symm x) = B ((E.conjAct g)⁻¹ x)
    rw [B.apply_symm_apply, hb]
    exact ((E.conjAct g).apply_symm_apply x).symm
  have hker : g * t * g⁻¹ * t⁻¹ ∈ E.inl.range := by
    rw [E.range_inl_eq_ker_rightHom]
    change E.rightHom (g * t * g⁻¹ * t⁻¹) = 1
    simp only [map_mul, map_inv]
    rw [mul_comm (E.rightHom g) (E.rightHom t)]
    group
  obtain ⟨u, hu⟩ := hker
  have hgroup : g * t * g⁻¹ = E.inl u * t := by rw [hu]; group
  have hconj := congrArg E.conjAct hgroup
  simp only [map_mul, map_inv, extension_conjAct_inl] at hconj
  refine ⟨u, ?_⟩
  apply LinearMap.ext
  intro x
  change polynomialInnerLieEquiv u (A x) = B (A (B.symm x))
  rw [polynomialInnerLieEquiv_apply, ha, hbi, hb, ha]
  exact (congrArg (fun f : MulAut L => f x) hconj).symm


theorem extension_semisimple_centralizer_correction [IsMulCommutative Q]
    (E : GroupExtension L G Q)
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g))
    (t : G) (S U : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : (polynomialModelLieEquiv (E.conjAct t) (hsmooth t)).toLinearMap =
      S.toLinearMap * U.toLinearMap) (g : G) :
    ∃ v : L, E.inl v * g ∈ semisimpleActionCentralizer E S := by
  let A := polynomialModelLieEquiv (E.conjAct t) (hsmooth t)
  let B := polynomialModelLieEquiv (E.conjAct g) (hsmooth g)
  obtain ⟨u, hlin⟩ := extension_outer_conjugation_identity E hsmooth t g
  obtain ⟨v, hv⟩ := semisimple_centralizer_inner_correction A S U B hS hU hSU hA u hlin
  refine ⟨v, ?_⟩
  change E.conjAct (E.inl v * g) ∈
    Subgroup.centralizer {PolynomialExponentialCoordinates.groupAutomorphism (P := C) S}
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  rw [map_mul, extension_conjAct_inl]
  apply DFunLike.ext
  intro x
  change v * E.conjAct g (S x) * v⁻¹ = S (v * E.conjAct g x * v⁻¹)
  have hh : polynomialInnerLieEquiv v (B (S x)) = S (polynomialInnerLieEquiv v (B x)) :=
    LinearMap.congr_fun hv.eq x
  simpa only [polynomialInnerLieEquiv_apply, B, polynomialModelLieEquiv_apply] using hh

theorem extension_semisimple_centralizer_surjective [IsMulCommutative Q]
    (E : GroupExtension L G Q)
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g))
    (t : G) (S U : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : (polynomialModelLieEquiv (E.conjAct t) (hsmooth t)).toLinearMap =
      S.toLinearMap * U.toLinearMap) :
    Function.Surjective (E.rightHom.comp (semisimpleActionCentralizer E S).subtype) := by
  intro q
  obtain ⟨g, hg⟩ := E.rightHom_surjective q
  obtain ⟨v, hv⟩ := extension_semisimple_centralizer_correction E hsmooth t S U hS hU hSU hA g
  exact ⟨⟨E.inl v * g, hv⟩, by simpa only [MonoidHom.comp_apply,
    Subgroup.coe_subtype, map_mul, E.rightHom_inl, one_mul] using hg⟩

end PolycyclicRecognition

end

end OAI
