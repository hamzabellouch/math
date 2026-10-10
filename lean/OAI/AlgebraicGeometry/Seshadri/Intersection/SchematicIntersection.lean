import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.FiniteIntersection

namespace OAI

section
noncomputable section
                                               
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

variable {K : Type} [Field K] {X : Scheme}

theorem finite_schematic_intersection (g : X ⟶ Spec (CommRingCat.of K)) [IsProper g]
    (I J : X.IdealSheafData) [IsIntegral I.subscheme]
    (hd : topologicalKrullDim I.subscheme ≤ 1) (hJ : ¬ J ≤ I) :
    Finite (I ⊔ J).subscheme := by
  classical
  let Q := J.comap I.subschemeι
  have hQ : Q ≠ ⊥ := by
    intro he
    apply hJ
    have h := Scheme.IdealSheafData.le_map_comap J I.subschemeι
    simpa only [show J.comap I.subschemeι = ⊥ from he,
      Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι] using h
  let : Finite Q.subscheme := finite_subscheme_of_curve (I.subschemeι ≫ g) hd Q hQ
  have hfin : (Q.support : Set I.subscheme).Finite := by
    rw [← Q.range_subschemeι]
    exact Set.finite_range Q.subschemeι
  let u : (I ⊔ J).subscheme ⟶ I.subscheme :=
    Scheme.IdealSheafData.inclusion le_sup_left
  have hu : u ≫ I.subschemeι = (I ⊔ J).subschemeι :=
    Scheme.IdealSheafData.inclusion_subschemeι le_sup_left
  have hm (z : (I ⊔ J).subscheme) : u z ∈ Q.support := by
    rw [Scheme.IdealSheafData.support_comap]
    change I.subschemeι (u z) ∈ J.support
    rw [← Scheme.Hom.comp_apply, hu]
    have hh : (I ⊔ J).subschemeι z ∈ (I ⊔ J).support := by
      change (I ⊔ J).subschemeι z ∈ ((I ⊔ J).support : Set X)
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨z,rfl⟩
    rw [Scheme.IdealSheafData.support_sup] at hh
    exact hh.2
  let : Finite (Q.support : Set I.subscheme) := hfin.to_subtype
  apply Finite.of_injective (fun z => (⟨u z,hm z⟩ : (Q.support : Set I.subscheme)))
  intro a b hab
  apply (I ⊔ J).subschemeι.isEmbedding.injective
  have h := congrArg (fun z : (Q.support : Set I.subscheme) => I.subschemeι z.1) hab
  simpa only [← Scheme.Hom.comp_apply, hu] using h

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
