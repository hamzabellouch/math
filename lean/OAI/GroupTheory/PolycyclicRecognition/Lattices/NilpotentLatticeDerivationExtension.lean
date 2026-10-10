import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentLatticeCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicParameterBasis
import OAI.GroupTheory.PolycyclicRecognition.Geometry.OrderedSemidirectWords
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SemidirectExponentialCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Lattices.DerivationSolvableModel

namespace OAI

/-! # Retaining the integral parameter in the real derivation extension -/

noncomputable section
namespace PolycyclicRecognition
open Module
attribute [local instance] semidirectProductTopology

variable {H : Type} [Group H]

theorem NilpotentLatticeCoordinates.derivation_extension
    (C : NilpotentLatticeCoordinates H) (a : MulAut H)
    (D : LieDerivation ℝ C.carrier C.carrier) (hD : IsNilpotent D.toLinearMap)
    (hstep : ∀ x, (C.equiv (a x) : C.carrier) =
      nilpotentDerivationFlow D hD 1 (C.equiv x)) :
    Nonempty (NilpotentLatticeCoordinates
      (H ⋊[integerPowerAction a] Multiplicative ℤ)) := by
  let L := C.carrier
  let φ := C.coordinates.derivationAction D hD
  obtain ⟨Γ, hΓ, f, hf⟩ := integer_semidirect_lattice_realization_with_coordinates
    φ a C.lattice C.uniform C.equiv hstep
  let := derivationSemidirectGroup D hD
  let _ : Mul (L × ℝ) := (derivationSemidirectGroup D hD).toMul
  obtain ⟨Q, E, hE⟩ := exists_semidirect_polynomial_exponential_coordinates D hD
  let := Q
  let T := DerivationLieSpace D hD
  let _ : Group T := Q.group
  let _ : Mul T := Q.group.toMul
  let F : T ≃* (L ⋊[φ] Multiplicative ℝ) := E.trans
    { derivationSemidirectEquiv D hD with map_mul' := fun _ _ => rfl }
  let : Group.IsSolvable (L ⋊[φ] Multiplicative ℝ) := semidirect_solvable φ
  let : Group.IsSolvable T :=
    Group.isSolvable_of_isSolvable_injective (f := F.toMonoidHom) F.injective
  let s := derivationLieSpaceSplit D hD
  let b := cyclicParameterBasis C.basis s
  let c := Module.finBasis ℝ (L × ℝ)
  let p := transportedProductParameter C.parameter s E.toEquiv
  have hpoly := polynomial_transported_product_parameter C.basis c b
    C.parameter s E.toEquiv C.polynomial C.polynomial_symm (hE b c).1 (hE b c).2
  have hF : Continuous F := by
    exact (continuous_derivationModelEquiv D hD).comp ((hE b c).1.contDiff.continuous)
  have hFi : Continuous F.symm := by
    exact (hE b c).2.contDiff.continuous.comp (continuous_derivationModelEquiv_symm D hD)
  let Λ := Γ.comap F.toMonoidHom
  let e : (H ⋊[integerPowerAction a] Multiplicative ℤ) ≃* Λ :=
    f.trans (comapSubgroupEquiv F Γ).symm
  refine ⟨{
    carrier := T
    lieNilpotent := derivationLieSpace_nilpotent D hD
    dimension := C.dimension + 1
    basis := b
    parameter := p
    polynomial := hpoly.1
    polynomial_symm := hpoly.2
    lattice := Λ
    uniform := hΓ.comap_mulEquiv F hF hFi
    equiv := e
    generators := cyclicExtensionGenerators a C.generators
    word_surjective := cyclicExtension_orderedWord_surjective a C.generators C.word_surjective
    integer_parameter := ?_ }⟩
  intro z
  apply F.injective
  change F (p (b.equivFun.symm (fun i => (z i : ℝ)))) =
    F (F.symm (f (orderedWord (cyclicExtensionGenerators a C.generators) z)))
  rw [F.apply_symm_apply, hf]
  have hp := transportedProductParameter_integer C.basis C.parameter s E.toEquiv z
  change E (p (b.equivFun.symm (fun i => (z i : ℝ)))) =
    (C.parameter (C.basis.equivFun.symm (fun i => (z i.castSucc : ℝ))),
      (z (Fin.last C.dimension) : ℝ)) at hp
  rw [cyclicExtension_orderedWord]
  apply SemidirectProduct.ext
  · change (E (p (b.equivFun.symm (fun i => (z i : ℝ))))).1 = _
    simpa [realIntegerSemidirectMap] using
      (congrArg Prod.fst hp).trans (C.integer_parameter _)
  · change Multiplicative.ofAdd (E (p (b.equivFun.symm (fun i => (z i : ℝ))))).2 = _
    simpa [realIntegerSemidirectMap, integerTimeHom] using
      congrArg Multiplicative.ofAdd (congrArg Prod.snd hp)

end PolycyclicRecognition

end

end OAI
