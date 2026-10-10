import OAI.NumberTheory.PiExponent.Ampleness.NilpotentAmpleDescent
import OAI.NumberTheory.PiExponent.Ampleness.ReducedComponentAmple

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem isAmple_of_integral_closed_restrictions [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L H : LineBundle X) (hH : H.IsAmple)
    (hints : ∀ {Y : Scheme.{0}} [IsIntegral Y] (j : Y ⟶ X) [IsClosedImmersion j],
      (L.pullback j).IsAmple) : L.IsAmple := by
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds X)
  have hI : I.support = ⊤ := by
    ext x
    simp only [I, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  let : IsLocallyNoetherian I.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  let : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace I.subschemeι
  let : IsNoetherian I.subscheme := {}
  let : IsReduced I.subscheme := isReduced_vanishingIdeal_subscheme ⊤
  apply LineBundle.isAmple_of_fullSupport p I hI L
  apply ReducedComponentAmple.isAmple_of_reduced_components (I.subschemeι ≫ p)
    (L.pullback I.subschemeι) (H.pullback I.subschemeι)
    (hH.pullback_closedImmersion H I.subschemeι)
  intro C
  let j := CurveCycle.reducedComponentι I.subscheme C
  have hc : (L.pullback (j ≫ I.subschemeι)).IsAmple := hints (j ≫ I.subschemeι)
  exact AmpleIso.isAmple_of_sheaf_iso _ _
    ((Scheme.Modules.pullbackComp j I.subschemeι).app L.sheaf).symm hc

end
end PiExponent.NumericalAmpleness

end OAI
