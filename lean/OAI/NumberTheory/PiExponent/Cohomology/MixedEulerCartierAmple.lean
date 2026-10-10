import OAI.NumberTheory.PiExponent.Cohomology.AmpleLineCohomology
import OAI.NumberTheory.PiExponent.Cohomology.LineCohomologyDimension
import OAI.NumberTheory.PiExponent.Cohomology.MixedEulerCartier

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponent.SectionZeroIdeal PiExponent.ProjectiveO1
variable {X : Scheme.{0}}

theorem tensor_euler_difference_cartier_pair_of_ample
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (r : ℕ)
    (hdim : topologicalKrullDim X ≤ r)
    (L B M : LineBundle X)
    (s : GlobalSections X (L.tensor B).sheaf) (t : GlobalSections X B.sheaf)
    [Mono s] [Mono t] :
    eulerCharacteristic p r (L.tensor M).sheaf - eulerCharacteristic p r M.sheaf =
      eulerCharacteristic ((zeroIdeal (L.tensor B) s).subschemeι ≫ p) r
        (((L.tensor B).pullback (zeroIdeal (L.tensor B) s).subschemeι).tensor
          (M.pullback (zeroIdeal (L.tensor B) s).subschemeι)).sheaf -
      eulerCharacteristic ((zeroIdeal B t).subschemeι ≫ p) r
        (((B.tensor L).pullback (zeroIdeal B t).subschemeι).tensor
          (M.pullback (zeroIdeal B t).subschemeι)).sheaf := by
  let D := zeroIdeal (L.tensor B) s
  let E := zeroIdeal B t
  let jD := D.subschemeι
  let jE := E.subschemeι
  have hHD := LineBundle.IsAmple.pullback_closedImmersion H hH jD
  have hHE := LineBundle.IsAmple.pullback_closedImmersion H hH jE
  let e0 : (CartierEulerPair.source L M 0).sheaf ≅ M.sheaf :=
    moduleTensorUnit M.sheaf
  let e1 : (CartierEulerPair.source L M 1).sheaf ≅ (L.tensor M).sheaf :=
    moduleTensorIso (moduleTensorRightUnit L.sheaf) (Iso.refl M.sheaf)
  let em : (CartierEulerPair.middle L B M 0).sheaf ≅
      ((L.tensor B).tensor M).sheaf :=
    moduleTensorIso (Iso.refl _) e0
  let ee : (B.tensor (CartierEulerPair.source L M 1)).sheaf ≅
      ((B.tensor L).tensor M).sheaf :=
    moduleTensorIso (Iso.refl _) e1 ≪≫ (lineTensorAssoc B L M).symm
  have hv := CartierEulerPair.euler_difference p L B M s t 0 r
    (fun q _ => line_cohomology_finite_of_ample_all p H hH (CartierEulerPair.source L M 0) q)
    (fun q _ => line_cohomology_finite_of_ample_all p H hH (CartierEulerPair.source L M 1) q)
    (fun q _ => line_cohomology_finite_of_ample_all p H hH (CartierEulerPair.middle L B M 0) q)
    (fun q _ => line_cohomology_finite_of_ample_all (jD ≫ p) (H.pullback jD) hHD
      ((CartierEulerPair.middle L B M 0).pullback jD) q)
    (fun q _ => line_cohomology_finite_of_ample_all (jE ≫ p) (H.pullback jE) hHE
      ((B.tensor (CartierEulerPair.source L M 1)).pullback jE) q)
    (lineBundle_cohomology_zero_of_dimension_le r p H hH
      (CartierEulerPair.source L M 0) hdim (r+1) (by omega))
    (lineBundle_cohomology_zero_of_dimension_le r p H hH
      (CartierEulerPair.source L M 1) hdim (r+1) (by omega))
  rw [eulerCharacteristic_iso p e0 r, eulerCharacteristic_iso p e1 r] at hv
  have hD := eulerCharacteristic_iso (jD ≫ p)
    ((Scheme.Modules.pullback jD).mapIso em ≪≫
      PiExponentSeshadri.PullbackTensor.iso jD (L.tensor B) M) r
  have hE := eulerCharacteristic_iso (jE ≫ p)
    ((Scheme.Modules.pullback jE).mapIso ee ≪≫
      PiExponentSeshadri.PullbackTensor.iso jE (B.tensor L) M) r
  rw [hD, hE] at hv
  exact hv

end
end PiExponent.NumericalAmpleness

end OAI
