import Mathlib.AlgebraicGeometry.Noetherian
import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationLocalRing

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponent.CurveZeroPole
open scoped Polynomial

universe u
variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)

def parameterCurveOpenCover : (parameterCurve f hf).OpenCover where
  I₀ := Bool
  X b := if b then Spec (.of (parameterChart f⁻¹ (transcendental_inverse f hf)))
    else Spec (.of (parameterChart f hf))
  f b := by
    cases b
    · exact zeroChartInclusion f hf
    · exact infinityChartInclusion f hf
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro x
      rcases parameterCurve_twoChartCover f hf x with ⟨q, rfl⟩ | ⟨q, rfl⟩
      · exact ⟨false, q, rfl⟩
      · exact ⟨true, q, rfl⟩
    · intro b
      cases b <;> infer_instance

instance parameterChart_noetherian [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    IsNoetherianRing (parameterChart f hf) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  infer_instance

instance parameterCurve_noetherian [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    IsNoetherian (parameterCurve f hf) := by
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  have hlocal : ∀ b, IsLocallyNoetherian ((parameterCurveOpenCover f hf).X b) := by
    intro b
    cases b <;> dsimp [parameterCurveOpenCover] <;> infer_instance
  have : IsLocallyNoetherian (parameterCurve f hf) :=
    (isLocallyNoetherian_iff_openCover (parameterCurveOpenCover f hf)).mpr hlocal
  exact ⟨⟩

attribute [local instance] specializationOrder

theorem parameterCurve_dimension_le_one [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    topologicalKrullDim (parameterCurve f hf) ≤ 1 := by
  have hs (x : parameterCurve f hf) :
      ringKrullDim ((parameterCurve f hf).presheaf.stalk x) ≤ 1 := by
    by_cases hx : x = genericPoint (parameterCurve f hf)
    · subst x
      change ringKrullDim (parameterCurve f hf).functionField ≤ 1
      have h : Ring.KrullDimLE 1 (parameterCurve f hf).functionField := inferInstance
      exact (Ring.krullDimLE_iff.mp h)
    · let := parameterCurve_stalkDVR f hf x hx
      exact (Ring.krullDimLE_iff.mp (inferInstance :
        Ring.KrullDimLE 1 ((parameterCurve f hf).presheaf.stalk x)))
  change Order.krullDim (IrreducibleCloseds (parameterCurve f hf)) ≤ 1
  rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := parameterCurve f hf)),
    Order.krullDim_eq_iSup_coheight]
  exact iSup_le fun x => by simpa only [ringKrullDim_stalk_eq_coheight] using hs x

theorem parameterCurve_isClosed_of_ne_generic [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (x : parameterCurve f hf) (hx : x ≠ genericPoint (parameterCurve f hf)) :
    IsClosed ({x} : Set (parameterCurve f hf)) := by
  apply closure_subset_iff_isClosed.mp
  intro y hy
  have hyx : y ≤ x := specializes_iff_mem_closure.mpr hy
  by_contra hne
  have hylt : y < x := lt_of_le_of_ne hyx (by simpa using hne)
  have hdim : Order.krullDim (parameterCurve f hf) ≤ 1 := by
    have h := parameterCurve_dimension_le_one f hf
    change Order.krullDim (IrreducibleCloseds (parameterCurve f hf)) ≤ 1 at h
    rwa [Order.krullDim_eq_of_orderIso
      (irreducibleSetEquivPoints (α := parameterCurve f hf))] at h
  have hyco : Order.coheight y ≤ (1 : ℕ∞) := by
    exact_mod_cast (Order.coheight_le_krullDim y).trans hdim
  have hxco : Order.coheight x < (1 : ℕ∞) :=
    Order.coheight_le_coe_iff.mp hyco x hylt
  have hxmax : IsMax x := Order.coheight_eq_zero.mp (Order.lt_one_iff.mp hxco)
  exact hx hxmax.eq_top

theorem parameterCurve_exists_nongeneric [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    ∃ x : parameterCurve f hf, x ≠ genericPoint (parameterCurve f hf) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let S := parameterChart f hf
  let : Module.IsTorsionFree F[X] S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  obtain ⟨q⟩ := (inferInstance : Nonempty ((zeroPrime F).primesOver S))
  let z : PrimeSpectrum S := ⟨q.val, q.property.1⟩
  have hz : z.asIdeal ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver (zeroPrime_ne_bot F) q.property
  refine ⟨zeroChartInclusion f hf z, ?_⟩
  intro heq
  have hgen := genericPoint_eq_of_isOpenImmersion (zeroChartInclusion f hf)
  have he : z = genericPoint (Spec (.of S)) :=
    (zeroChartInclusion f hf).isOpenEmbedding.injective (heq.trans hgen.symm)
  apply hz
  rw [he, genericPoint_eq_bot_of_affine]
  rfl

theorem parameterCurve_isClosed_iff_ne_generic [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (x : parameterCurve f hf) :
    IsClosed ({x} : Set (parameterCurve f hf)) ↔
      x ≠ genericPoint (parameterCurve f hf) := by
  constructor
  · intro hclosed heq
    subst x
    obtain ⟨y, hy⟩ := parameterCurve_exists_nongeneric f hf
    have hy' : y ∈ closure ({genericPoint (parameterCurve f hf)} :
        Set (parameterCurve f hf)) := by rw [genericPoint_closure]; trivial
    rw [hclosed.closure_eq] at hy'
    exact hy hy'
  · exact parameterCurve_isClosed_of_ne_generic f hf x

end PiExponent.CurveNormalizationModel

end

end OAI
