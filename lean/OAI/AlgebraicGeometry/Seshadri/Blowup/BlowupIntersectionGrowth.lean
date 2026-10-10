import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorPowerDistribution
import OAI.AlgebraicGeometry.Seshadri.Blowup.BlowupSectionDimensions
import OAI.AlgebraicGeometry.Seshadri.Cohomology.SurfaceH1Growth
import OAI.AlgebraicGeometry.Seshadri.Interpolation.PolynomialBounds

namespace OAI


                                                  
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.NefNumerics

lemma Surface.power_H0_bounds (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple) :
    ∃ b c e z : ℤ, ∀ n : ℕ,
      selfIntersection S L*(n:ℤ)^2+b*n+c ≤ 2*(cohomologyDimension S.structureMap (L.pow n).sheaf 0 : ℤ) ∧
      2*(cohomologyDimension S.structureMap (L.pow n).sheaf 0 : ℤ) ≤ selfIntersection S L*(n:ℤ)^2+e*n+z := by
  obtain ⟨B,hB⟩ := S.power_H0_quadratic_lower L hL
  obtain ⟨C,G,hC⟩ := S.power_H0_quadratic_upper L hL
  let d := eulerCharacteristic S.structureMap 2 L.sheaf-eulerCharacteristic S.structureMap 2 (O S.scheme)
  let q := selfIntersection S L
  refine ⟨-q+2*d,2*eulerCharacteristic S.structureMap 2 (O S.scheme)-2*B,
    -q+2*d+2*G,2*eulerCharacteristic S.structureMap 2 (O S.scheme)+2*C,fun n => ⟨?_,?_⟩⟩
  · have H := hB n
    dsimp [q,d]
    nlinarith only [H]
  · have H := hC n
    dsimp [q,d]
    nlinarith only [H]

lemma Surface.square_squeeze_of_sections (S T : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple)
    (D : LineBundle T.scheme) (hD : D.IsAmple) (k r : ℕ)
    (hb : ∀ n : ℕ,
      cohomologyDimension T.structureMap (D.pow n).sheaf 0 ≤ cohomologyDimension S.structureMap (L.pow (k*n)).sheaf 0 ∧
      2*cohomologyDimension S.structureMap (L.pow (k*n)).sheaf 0 ≤
        2*cohomologyDimension T.structureMap (D.pow n).sheaf 0 + r*n*(n+1)) :
    (k:ℤ)^2*selfIntersection S L-r ≤ selfIntersection T D ∧
    selfIntersection T D ≤ (k:ℤ)^2*selfIntersection S L := by
  obtain ⟨b,c,e,z,hS⟩ := S.power_H0_bounds L hL
  obtain ⟨b',c',e',z',hT⟩ := T.power_H0_bounds D hD
  have h₁ := quadratic_nonpos_leading (selfIntersection T D-(k:ℤ)^2*selfIntersection S L)
    (b'-(k:ℤ)*e) (c'-z) (fun n => by
      have H := (hT n).1
      have G := (hS (k*n)).2
      have F : (cohomologyDimension T.structureMap (D.pow n).sheaf 0 : ℤ) ≤
        cohomologyDimension S.structureMap (L.pow (k*n)).sheaf 0 := by exact_mod_cast (hb n).1
      push_cast at G
      nlinarith only [H,G,F])
  have h₂ := quadratic_nonpos_leading ((k:ℤ)^2*selfIntersection S L-(r:ℤ)-selfIntersection T D)
    ((k:ℤ)*b-r-e') (c-z') (fun n => by
      have H := (hT n).2
      have G := (hS (k*n)).1
      have F : 2*(cohomologyDimension S.structureMap (L.pow (k*n)).sheaf 0 : ℤ) ≤
        2*(cohomologyDimension T.structureMap (D.pow n).sheaf 0 : ℤ)+(r:ℤ)*n*(n+1) := by exact_mod_cast (hb n).2
      push_cast at G
      nlinarith only [H,G,F])
  omega

theorem Surface.ample_exceptional_square_squeeze (S T : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple)
    {r : ℕ} (p : Configuration S r) (f : T.scheme ⟶ S.scheme)
    (hf : f ≫ S.structureMap = T.structureMap)
    (hbl : IsBlowup (centreIdeal S r p) f)
    (J : LineBundle T.scheme) (ι : J.sheaf ⟶ O T.scheme)
    (hJ : PresentsPullbackIdeal (centreIdeal S r p) f J ι)
    (k : ℕ) (hD : (((L.pullback f).pow k).tensor J).IsAmple) :
    (k:ℤ)^2*selfIntersection S L-r ≤ selfIntersection T (((L.pullback f).pow k).tensor J) ∧
    selfIntersection T (((L.pullback f).pow k).tensor J) ≤ (k:ℤ)^2*selfIntersection S L := by
  let D := ((L.pullback f).pow k).tensor J
  refine S.square_squeeze_of_sections T L hL D hD k r ?_
  intro n
  have H := S.exceptional_twist_sections_bounds T L hL D hD p f hf hbl J ι hJ (L.pow (k*n)) n
  let e : (D.pow n).sheaf ≅ ((J.pow n).tensor ((L.pow (k*n)).pullback f)).sheaf :=
    lineTwistPower (L.pullback f) J k n ≪≫
    moduleTensorIso (PullbackTensor.powIso f L (k*n)).symm (Iso.refl _) ≪≫
    moduleTensorComm ((L.pow (k*n)).pullback f).sheaf (J.pow n).sheaf
  have he := cohomologyDimension_iso T.structureMap e 0
  change cohomologyDimension T.structureMap (D.pow n).sheaf 0 = _ at he
  rwa [he]

end
end MaximalSeshadri.Geometry

end


end OAI
