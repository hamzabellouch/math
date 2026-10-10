import OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart
import OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeRestriction

namespace OAI

namespace PiExponent.ReesFrozenChart
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.ReesGrading PiExponent.ReesProductChart
attribute [local irreducible] affineBlowup projection
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

def restriction {s t : Finset J} (hst : s ⊆ t) : coordinateRing I a s →+* coordinateRing I a t :=
  (coordinateEquiv I a t).symm.toRingHom.comp
    ((ReesProductRestriction.chartRestriction I a hst).comp (coordinateEquiv I a s).toRingHom)

theorem restriction_base {s t : Finset J} (hst : s ⊆ t) (r : R) :
    restriction I a hst (base I a s r) = base I a t r := by
  simp only [restriction, base, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  change (coordinateEquiv I a t).symm
      (ReesProductRestriction.chartRestriction I a hst
        ((coordinateEquiv I a s)
          ((coordinateEquiv I a s).symm (ReesProductChart.chartBase I a s r)))) =
    (coordinateEquiv I a t).symm (ReesProductChart.chartBase I a t r)
  rw [RingEquiv.apply_symm_apply, ReesProductRestriction.chartRestriction_base]

theorem restriction_chart {s t : Finset J} (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ⊆ t) :
    Spec.map (CommRingCat.ofHom (restriction I a hst)) ≫ chart I a hs = chart I a ht := by
  have he : (restriction I a hst).comp (coordinateEquiv I a s).symm.toRingHom =
      (coordinateEquiv I a t).symm.toRingHom.comp (ReesProductRestriction.chartRestriction I a hst) := by
    apply RingHom.ext
    intro z
    simp only [restriction, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  have heCat :
      (CommRingCat.ofHom (coordinateEquiv I a s).symm.toRingHom :
        CommRingCat.of (Chart I a s) ⟶ coordinateRing I a s) ≫
        CommRingCat.ofHom (restriction I a hst) =
      (CommRingCat.ofHom (ReesProductRestriction.chartRestriction I a hst) :
        CommRingCat.of (Chart I a s) ⟶ CommRingCat.of (Chart I a t)) ≫
        CommRingCat.ofHom (coordinateEquiv I a t).symm.toRingHom :=
    congrArg (fun f : Chart I a s →+* coordinateRing I a t => CommRingCat.ofHom f) he
  rw [chart, ← Category.assoc, ← Spec.map_comp]
  erw [heCat]
  rw [Spec.map_comp, Category.assoc,
    ReesProductSchemeRestriction.chartRestriction_chartMorphism I a hs ht hst]
  rfl

end
end PiExponent.ReesFrozenChart

end OAI
