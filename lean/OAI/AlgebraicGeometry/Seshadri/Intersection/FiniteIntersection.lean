import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.FiniteScheme
import OAI.AlgebraicGeometry.Seshadri.Geometry.CurveFinite

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

variable {K : Type} [Field K] {X : Scheme}

theorem finite_subscheme_of_curve [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    (hd : topologicalKrullDim X ≤ 1) (I : X.IdealSheafData) (hI : I ≠ ⊥) :
    Finite I.subscheme := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNoetherian X := ⟨⟩
  have hp : (I.support : Set X) ≠ Set.univ := by
    intro he
    apply hI
    exact Scheme.IdealSheafData.support_eq_top_iff.mp (SetLike.coe_injective he)
  have hf := proper_closed_finite_of_dimension_one hd I.support.isClosed hp
  have hr : (Set.range I.subschemeι).Finite := I.range_subschemeι ▸ hf
  let : Finite (Set.range I.subschemeι) := hr.to_subtype
  exact Finite.of_injective (fun x : I.subscheme =>
    (⟨I.subschemeι x, ⟨x,rfl⟩⟩ : Set.range I.subschemeι))
    (fun a b h => I.subschemeι.isEmbedding.injective (congrArg (fun z : Set.range I.subschemeι => (z : X)) h))

theorem curve_subscheme_isFinite [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    (hd : topologicalKrullDim X ≤ 1) (I : X.IdealSheafData) (hI : I ≠ ⊥) :
    IsFinite (I.subschemeι ≫ f) := by
  let : Finite I.subscheme := finite_subscheme_of_curve f hd I hI
  exact proper_finite_scheme_isFinite (I.subschemeι ≫ f)

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
