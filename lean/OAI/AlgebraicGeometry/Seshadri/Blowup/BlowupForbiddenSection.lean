import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.BivariateSurfaceEuler
import OAI.AlgebraicGeometry.Seshadri.Blowup.BlowupSectionDescent
import OAI.AlgebraicGeometry.Seshadri.Blowup.BlowupLineDescent
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.PointIdealMembership
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.IdealContractionMembership
import OAI.AlgebraicGeometry.Seshadri.Intersection.IdealProductDegree
import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionCurveBound

namespace OAI


                                                
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

theorem PointBlowup.section_curve_bound (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) {r : ℕ} {p : Configuration S r} (B : PointBlowup S r p)
    (J : LineBundle B.surface.scheme) (ι : J.sheaf ⟶ O B.surface.scheme)
    (hJ : PresentsPullbackIdeal (centreIdeal S r p) B.projection J ι)
    (w : ℝ) (hw : 0 ≤ w)
    (hC : ∀ C : IntegralCurve S,
      w*(totalMultiplicity S r C p:ℝ) ≤ (curveDegree S L C:ℝ))
    (k m : ℕ)
    (q : O B.surface.scheme ⟶ ((J.pow m).tensor ((L.pow k).pullback B.projection)).sheaf)
    (hq : q ≠ 0) : w*((r*m:ℕ):ℝ) ≤ (k:ℝ)*selfIntersection S L := by
  classical
  let f := B.projection
  let : IsProper (f ≫ S.structureMap) := by rw [B.overComplex]; infer_instance
  let : IsProper f := IsProper.of_comp f S.structureMap
  let := S.blowup_structureMap_isIso p B.isBlowup
  have hmono : Mono (C := B.surface.scheme.Modules) (idealPowerInclusion J ι m) :=
    @idealPowerInclusion_mono B.surface.scheme J ι hJ.1 m
  have : Mono (C := B.surface.scheme.Modules)
      (tensorInclusion (J.pow m) ((L.pow k).pullback f) (idealPowerInclusion J ι m)) :=
    @tensorInclusion_mono B.surface.scheme (J.pow m) ((L.pow k).pullback f)
      (idealPowerInclusion J ι m) hmono
  let a := tensorInclusion (J.pow m) ((L.pow k).pullback f) (idealPowerInclusion J ι m)
  obtain ⟨s,hs⟩ := ((L.pow k).pullbackSection_bijective f).2 (q ≫ a)
  have hs0 : s ≠ 0 := by
    intro hz
    apply hq
    apply (cancel_mono a).mp
    rw [zero_comp]
    exact hs.symm.trans (by rw [hz]; simp [pullbackSection]; rfl)
  have hc : (((centreIdeal S r p).comap f)^m).map f = (centreIdeal S r p)^m :=
    FinitePointBlowup.finite_point_power_contraction
      (fun i => (p.val i).left) S.structureMap (fun i => (p.val i).w) p.property
      f B.isBlowup m
  choose U hp hU e t het using fun i : Fin r => S.etale_line_frame_inside (L.pow k) ⊤
    (p.val i).image (by trivial)
  choose ρ hρ using fun i => affineComplexPoint_factor S.structureMap (U i) (p.val i) (hp i)
  have ho (i : Fin r) : affineCoefficient (U i) (e i) s ∈ (RingHom.ker (ρ i))^m := by
    have hmem := descended_section_ideal_power f (centreIdeal S r p) J ι hJ m hc
      (L.pow k) s q hs.symm (U i) (e i)
    have hI : (centreIdeal S r p).ideal (U i) ≤ (p.val i).left.ker.ideal (U i) := by
      unfold centreIdeal
      rw [idealSheaf_prod_ideal]
      exact Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ i))
    rw [← hρ i,affineComplexPoint_ideal] at hI
    exact (pow_le_pow_left' hI m) hmem
  have hb := section_bound_of_curve_bound S L hL p w hw hC (L.pow k) s hs0 U e ρ hρ
    (fun _ => m) ho
  rw [mixedEuler_pow_right S L hL,mixedEuler_self] at hb
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,
    Int.cast_mul,Int.cast_natCast] using hb

end
end MaximalSeshadri.Geometry

end

end OAI
