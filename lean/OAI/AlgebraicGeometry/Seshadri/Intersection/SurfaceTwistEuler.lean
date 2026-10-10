import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.SurfaceQuadraticEuler
import OAI.AlgebraicGeometry.Seshadri.Intersection.TwistNumerics

namespace OAI


                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

def mixedEuler (S : Surface) (L M : LineBundle S.scheme) : ℤ :=
  eulerCharacteristic S.structureMap 2 (L.tensor M).sheaf -
    eulerCharacteristic S.structureMap 2 L.sheaf -
    eulerCharacteristic S.structureMap 2 M.sheaf +
    eulerCharacteristic S.structureMap 2 (O S.scheme)

theorem generated_twist_euler_difference (S : Surface) (A : LineBundle S.scheme)
    (hA : A.IsAmple) (L M : LineBundle S.scheme) (d : ℕ)
    {σ : Type} [Fintype σ] (k : ℂ →+* Γ(S.scheme,⊤))
    (s : σ → (O S.scheme ⟶ (L.pow d).sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → ℂ)
    (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (hd : topologicalKrullDim (sectionIdeal k s hs v).subscheme = 1) (n : ℕ) :
    let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
      (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hd⟩
    eulerCharacteristic S.structureMap 2 ((L.pow (n+d)).tensor M).sheaf -
      eulerCharacteristic S.structureMap 2 ((L.pow n).tensor M).sheaf =
        ((n+d : ℕ) : ℤ)*curveDegree S L C + curveDegree S M C +
          eulerCharacteristic (C.embedding ≫ S.structureMap) 1 (O C.scheme) := by
  let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
      (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hd⟩
  let e : ((L.pow d).tensor ((L.pow n).tensor M)).sheaf ≅
      ((L.pow (n+d)).tensor M).sheaf :=
    (lineTensorAssoc (L.pow d) (L.pow n) M).symm ≪≫
    moduleTensorIso ((linePowerAdd L d n).symm ≪≫
      eqToIso (congrArg (fun j => (L.pow j).sheaf) (Nat.add_comm d n))) (Iso.refl _)
  have H := generated_section_euler_difference S A hA (L.pow d) ((L.pow n).tensor M) k s hs v hne hd
  have e₁ := eulerCharacteristic_iso S.structureMap e 2
  have e₂ := eulerCharacteristic_iso (C.embedding ≫ S.structureMap)
    ((Scheme.Modules.pullback C.embedding).mapIso e) 1
  have hdeg := curveDegree_tensor S A hA (L.pow (n+d)) M C
  rw [curveDegree_pow S A hA L C] at hdeg
  unfold curveDegree at hdeg
  change eulerCharacteristic S.structureMap 2 ((L.pow d).tensor ((L.pow n).tensor M)).sheaf -
    eulerCharacteristic S.structureMap 2 ((L.pow n).tensor M).sheaf =
      eulerCharacteristic (C.embedding ≫ S.structureMap) 1
        ((Scheme.Modules.pullback C.embedding).obj ((L.pow d).tensor ((L.pow n).tensor M)).sheaf) at H
  rw [e₁,e₂] at H
  change _ - _ = ((n+d : ℕ) : ℤ)*curveDegree S L C + curveDegree S M C +
    eulerCharacteristic (C.embedding ≫ S.structureMap) 1 (O C.scheme)
  change eulerCharacteristic (C.embedding ≫ S.structureMap) 1
      ((Scheme.Modules.pullback C.embedding).obj ((L.pow (n+d)).tensor M).sheaf) -
    eulerCharacteristic (C.embedding ≫ S.structureMap) 1 (O C.scheme) =
      ((n+d : ℕ) : ℤ)*curveDegree S L C + curveDegree S M C at hdeg
  omega

theorem Surface.twist_euler (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple)
    (M : LineBundle S.scheme) (n : ℕ) :
    eulerCharacteristic S.structureMap 2 ((L.pow n).tensor M).sheaf =
      eulerCharacteristic S.structureMap 2 (L.pow n).sheaf +
      eulerCharacteristic S.structureMap 2 M.sheaf -
      eulerCharacteristic S.structureMap 2 (O S.scheme) + (n : ℤ)*mixedEuler S L M := by
  classical
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let f (n : ℕ) := eulerCharacteristic S.structureMap 2 ((L.pow n).tensor M).sheaf -
    eulerCharacteristic S.structureMap 2 (L.pow n).sheaf
  have h0 : f 0 = eulerCharacteristic S.structureMap 2 M.sheaf -
      eulerCharacteristic S.structureMap 2 (O S.scheme) := by
    change eulerCharacteristic S.structureMap 2 (moduleTensor S.scheme (O S.scheme) M.sheaf) -
      eulerCharacteristic S.structureMap 2 (O S.scheme) = _
    exact congrArg (fun z : ℤ => z - eulerCharacteristic S.structureMap 2 (O S.scheme))
      (eulerCharacteristic_iso S.structureMap (moduleTensorUnit M.sheaf) 2)
  have h1 : f 1 - f 0 = mixedEuler S L M := by
    have ht := eulerCharacteristic_iso S.structureMap
      (moduleTensorIso (moduleTensorRightUnit L.sheaf) (Iso.refl M.sheaf)) 2
    change eulerCharacteristic S.structureMap 2 ((L.pow 1).tensor M).sheaf =
      eulerCharacteristic S.structureMap 2 (L.tensor M).sheaf at ht
    dsimp [f] at h0 ⊢
    rw [ht,S.euler_power_one L]
    unfold mixedEuler
    omega
  obtain ⟨a,ha,-,N,s,hs,v,hne,hi,hd⟩ := S.coprime_integral_section L hL 1 (by decide)
  let := hi
  let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
      (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hd⟩
  obtain ⟨b,hb,hab,N',s',hs',v',hne',hi',hd'⟩ := S.coprime_integral_section L hL a ha
  let := hi'
  let D : IntegralCurve S := ⟨(sectionIdeal k s' hs' v').subscheme,
      (sectionIdeal k s' hs' v').subschemeι,inferInstance,inferInstance,hd'⟩
  have ha' (m : ℕ) : f (m+a)-f m = curveDegree S M C := by
    have h := generated_twist_euler_difference S L hL L M a k s hs v hne hd m
    have h' := generated_power_euler_difference S L hL L a k s hs v hne hd m
    dsimp only [f]
    dsimp only at h h'
    linarith
  have hb' (m : ℕ) : f (m+b)-f m = curveDegree S M D := by
    have h := generated_twist_euler_difference S L hL L M b k s' hs' v' hne' hd' m
    have h' := generated_power_euler_difference S L hL L b k s' hs' v' hne' hd' m
    dsimp only [f]
    dsimp only at h h'
    linarith
  have H := EulerNumerics.affine_of_coprime_differences f a b hab _ _ ha' hb' n
  rw [h1,h0] at H
  dsimp only [f] at H
  omega

end
end MaximalSeshadri.Geometry

end



end OAI
