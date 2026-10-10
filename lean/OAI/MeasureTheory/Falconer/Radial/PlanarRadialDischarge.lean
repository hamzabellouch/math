import OAI.MeasureTheory.Falconer.Estimates.Published
import OAI.MeasureTheory.Falconer.Radial.RadialLpEnergy

namespace OAI

/-! # The planar radial moment for compact disjoint supports

The finite-energy radial projection estimate specializes to compact,
disjoint supports with the same circle measure.
-/
namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem published_planar_radial_moment : PublishedPlanarRadialMoment := by
  intro α β δ hδ hδ1 hα hβ hsep hEα hEβ
  obtain ⟨hs1,hs2,hp1,hp2,_ht0,hupt,htp,_hsδ,_htδ⟩ := radial_parameters hδ hδ1
  have hpq : (1+δ/8).HolderConjugate ((1+δ/8)/((1+δ/8)-1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp1).mpr rfl
  exact finite_radial_Lp_integral (α : Measure Plane) (β : Measure Plane)
    hα hβ hsep (α : Measure Plane).support_mem_ae (β : Measure Plane).support_mem_ae
    hpq hp2 hs1 hs2 (by simpa only [mul_comm] using hupt) htp hEα hEβ

end PlanarFalconer

end OAI
