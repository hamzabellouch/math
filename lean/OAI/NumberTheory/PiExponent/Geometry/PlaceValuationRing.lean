import OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter

namespace OAI

noncomputable section

namespace PiExponent.PlaceValuationRing

open CurveValuationCenter WeightedCurveDegree

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

abbrev ring (p : NormalizedPlace F E) : ValuationSubring E :=
  p.valuation.toValuation.valuationSubring

def constantsHom (p : NormalizedPlace F E) : F →+* ring p where
  toFun c := ⟨algebraMap F E c, p.constants_nonneg c⟩
  map_zero' := by ext; exact map_zero _
  map_one' := by ext; exact map_one _
  map_add' _ _ := by ext; exact map_add _ _ _
  map_mul' _ _ := by ext; exact map_mul _ _ _

instance constantsAlgebra (p : NormalizedPlace F E) : Algebra F (ring p) :=
  (constantsHom p).toAlgebra

instance scalarTower (p : NormalizedPlace F E) : IsScalarTower F (ring p) E :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

@[simp] theorem constants_algebraMap (p : NormalizedPlace F E) (c : F) :
    (algebraMap F (ring p) c : E) = algebraMap F E c := rfl

instance valuation_nontrivial (p : NormalizedPlace F E) :
    p.valuation.toValuation.IsNontrivial := by
  obtain ⟨z, hz⟩ := p.normalized
  apply (Valuation.isNontrivial_iff_exists_lt_one _).mpr
  refine ⟨z, z.ne_zero, ?_⟩
  change (0 : WithTop ℤ) < p.valuation (z : E)
  rw [← coe_integerOrder, hz]
  norm_num

instance discreteValuationRing (p : NormalizedPlace F E) :
    IsDiscreteValuationRing (ring p) := by
  let : IsCyclic (Multiplicative (OrderDual (WithTop ℤ)))ˣ :=
    inferInstanceAs (IsCyclic (WithZero (Multiplicative ℤ))ˣ)
  let : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass p.valuation.toValuation)) := by
    infer_instance
  exact Valuation.valuationSubring_isDiscreteValuationRing p.valuation.toValuation

theorem valuation_eq_fractionAddValuation (p : NormalizedPlace F E) :
    p.valuation = CurveLocalOrder.fractionAddValuation (ring p) E := by
  apply DVRValuationUnique.eq_fractionAddValuation p.valuation
  · intro a
    exact a.property
  · intro a ha _
    exact p.valuation.toValuation.mem_maximalIdeal_iff.mp ha
  · exact p.normalized

end PiExponent.PlaceValuationRing

end

end OAI
