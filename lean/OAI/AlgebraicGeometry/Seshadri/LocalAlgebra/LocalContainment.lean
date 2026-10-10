import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.OpenChartDegree

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.ProjectiveBertini MaximalSeshadri.Frames

variable {X Y : Scheme.{0}}

theorem pullback_section_zero_iff_local_coefficient
    (p : X ⟶ Spec (CommRingCat.of ℂ))
    (I : X.IdealSheafData) [IsIntegral I.subscheme]
    (L : LineBundle X) (s : O X ⟶ L.sheaf)
    (U : X.affineOpens) [Nonempty (I.subschemeι ⁻¹ᵁ U.1).toScheme]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    pullbackSection I.subschemeι s = 0 ↔
      U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)) ∈ I.ideal U := by
  let : Algebra ℂ Γ(X,U.1) := (openScalars p U.1).toAlgebra
  let : Algebra ℂ Γ((I.subschemeι ⁻¹ᵁ U.1).toScheme,⊤) :=
    (baseScalars ((I.subschemeι ⁻¹ᵁ U.1).ι ≫ (I.subschemeι ≫ p))).toAlgebra
  obtain ⟨eF,he⟩ := exists_restricted_pullback_frame I.subschemeι U.1 e s
  let π := structuralOpenChartMap p I.subschemeι U.1
  let f := U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))
  have hcoeff : π f = coefficient eF
      (restrictSection (I.subschemeι ⁻¹ᵁ U.1).ι (pullbackSection I.subschemeι s)) := by
    rw [he]
    change (I.subschemeι ∣_ U.1).appTop
      (U.1.topIso.inv (U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)))) = _
    rw [U.1.topIso.hom_inv_id_apply]
  have hker : f ∈ I.ideal U ↔ π f = 0 := by
    rw [← structuralOpenChartMap_ker p I U]
    rfl
  rw [show U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)) = f from rfl,
    hker, hcoeff]
  constructor
  · intro h
    rw [h,restrictSection_zero,coefficient_zero]
  · intro h
    apply (L.pullback I.subschemeι).restricted_coefficient_injective
      (I.subschemeι ⁻¹ᵁ U.1).ι eF
    change coefficient eF
      (restrictSection (I.subschemeι ⁻¹ᵁ U.1).ι (pullbackSection I.subschemeι s)) =
      coefficient eF (restrictSection (I.subschemeι ⁻¹ᵁ U.1).ι
        (0 : O I.subscheme ⟶ (Scheme.Modules.pullback I.subschemeι).obj L.sheaf))
    rw [restrictSection_zero,coefficient_zero]
    exact h

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
