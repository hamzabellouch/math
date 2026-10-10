import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.CartierEuler
import OAI.AlgebraicGeometry.Seshadri.Intersection.AmbientCurveDegree
import OAI.AlgebraicGeometry.Seshadri.Divisors.CoprimeDivisor
import OAI.AlgebraicGeometry.Seshadri.Intersection.QuadraticSequence

namespace OAI


                                               
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem generated_power_euler_difference (S : Surface) (A : LineBundle S.scheme)
    (hA : A.IsAmple) (L : LineBundle S.scheme) (d : ℕ)
    {σ : Type} [Fintype σ] (k : ℂ →+* Γ(S.scheme,⊤))
    (s : σ → (O S.scheme ⟶ (L.pow d).sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → ℂ)
    (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (hd : topologicalKrullDim (sectionIdeal k s hs v).subscheme = 1) (n : ℕ) :
    let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
      (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hd⟩
    eulerCharacteristic S.structureMap 2 (L.pow (n+d)).sheaf -
      eulerCharacteristic S.structureMap 2 (L.pow n).sheaf =
        ((n+d : ℕ) : ℤ)*curveDegree S L C +
          eulerCharacteristic (C.embedding ≫ S.structureMap) 1 (O C.scheme) := by
  let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
      (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hd⟩
  have H := generated_section_euler_difference S A hA (L.pow d) (L.pow n) k s hs v hne hd
  have e₁ := eulerCharacteristic_iso S.structureMap (linePowerAdd L d n) 2
  have e₂ := eulerCharacteristic_iso (C.embedding ≫ S.structureMap)
    ((Scheme.Modules.pullback C.embedding).mapIso (linePowerAdd L d n)) 1
  have e₃ := curveDegree_pow S A hA L C (d+n)
  change eulerCharacteristic S.structureMap 2 (L.pow (d+n)).sheaf =
    eulerCharacteristic S.structureMap 2 ((L.pow d).tensor (L.pow n)).sheaf at e₁
  change eulerCharacteristic (C.embedding ≫ S.structureMap) 1
      ((Scheme.Modules.pullback C.embedding).obj (L.pow (d+n)).sheaf) =
    eulerCharacteristic (C.embedding ≫ S.structureMap) 1
      ((Scheme.Modules.pullback C.embedding).obj ((L.pow d).tensor (L.pow n)).sheaf) at e₂
  change eulerCharacteristic S.structureMap 2 ((L.pow d).tensor (L.pow n)).sheaf -
    eulerCharacteristic S.structureMap 2 (L.pow n).sheaf =
      eulerCharacteristic (C.embedding ≫ S.structureMap) 1
        ((Scheme.Modules.pullback C.embedding).obj ((L.pow d).tensor (L.pow n)).sheaf) at H
  rw [← e₁,← e₂] at H
  unfold curveDegree at e₃
  change _ = ((d+n : ℕ) : ℤ)*curveDegree S L C at e₃
  rw [Nat.add_comm d n] at H e₃
  change eulerCharacteristic S.structureMap 2 (L.pow (n+d)).sheaf -
    eulerCharacteristic S.structureMap 2 (L.pow n).sheaf =
      ((n+d : ℕ) : ℤ)*curveDegree S L C +
        eulerCharacteristic (C.embedding ≫ S.structureMap) 1 (O C.scheme)
  change eulerCharacteristic (C.embedding ≫ S.structureMap) 1
      ((Scheme.Modules.pullback C.embedding).obj (L.pow (n+d)).sheaf) -
    eulerCharacteristic (C.embedding ≫ S.structureMap) 1 (O C.scheme) =
      ((n+d : ℕ) : ℤ)*curveDegree S L C at e₃
  linarith

lemma Surface.euler_power_one (S : Surface) (L : LineBundle S.scheme) :
    eulerCharacteristic S.structureMap 2 (L.pow 1).sheaf =
      eulerCharacteristic S.structureMap 2 L.sheaf :=
  eulerCharacteristic_iso S.structureMap (moduleTensorRightUnit L.sheaf) 2

lemma Surface.euler_power_second_difference (S : Surface) (L : LineBundle S.scheme) :
    eulerCharacteristic S.structureMap 2 (L.pow 2).sheaf -
      2*eulerCharacteristic S.structureMap 2 (L.pow 1).sheaf +
      eulerCharacteristic S.structureMap 2 (L.pow 0).sheaf = selfIntersection S L := by
  rw [S.euler_power_one]
  rfl

theorem Surface.power_euler_quadratic (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) (n : ℕ) :
    2*eulerCharacteristic S.structureMap 2 (L.pow n).sheaf =
      (n : ℤ)*((n : ℤ)-1)*selfIntersection S L +
      2*(n : ℤ)*(eulerCharacteristic S.structureMap 2 L.sheaf -
        eulerCharacteristic S.structureMap 2 (O S.scheme)) +
      2*eulerCharacteristic S.structureMap 2 (O S.scheme) := by
  classical
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let f (n : ℕ) := eulerCharacteristic S.structureMap 2 (L.pow n).sheaf
  obtain ⟨a,ha,-,N,s,hs,v,hne,hi,hd⟩ := S.coprime_integral_section L hL 1 (by decide)
  let := hi
  let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
      (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hd⟩
  obtain ⟨b,hb,hab,N',s',hs',v',hne',hi',hd'⟩ := S.coprime_integral_section L hL a ha
  let := hi'
  let D : IntegralCurve S := ⟨(sectionIdeal k s' hs' v').subscheme,
      (sectionIdeal k s' hs' v').subschemeι,inferInstance,inferInstance,hd'⟩
  have ha' (m : ℕ) : f (m+a)-f m = (m : ℤ)*curveDegree S L C +
      ((a : ℤ)*curveDegree S L C+eulerCharacteristic (C.embedding ≫ S.structureMap) 1 (O C.scheme)) := by
    have H := generated_power_euler_difference S L hL L a k s hs v hne hd m
    change f (m+a)-f m = _ at H
    push_cast at H
    linarith
  have hb' (m : ℕ) : f (m+b)-f m = (m : ℤ)*curveDegree S L D +
      ((b : ℤ)*curveDegree S L D+eulerCharacteristic (D.embedding ≫ S.structureMap) 1 (O D.scheme)) := by
    have H := generated_power_euler_difference S L hL L b k s' hs' v' hne' hd' m
    change f (m+b)-f m = _ at H
    push_cast at H
    linarith
  have H := EulerNumerics.quadratic_of_coprime_differences f a b hab _ _ _ _ ha' hb' n
  have hq := S.euler_power_second_difference L
  have h1 := S.euler_power_one L
  change f 2-2*f 1+f 0 = selfIntersection S L at hq
  change f 1 = _ at h1
  rw [hq,h1] at H
  exact H

theorem generated_curveDegree_eq_power_selfIntersection (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (d : ℕ)
    {σ : Type} [Fintype σ] (k : ℂ →+* Γ(S.scheme,⊤))
    (s : σ → (O S.scheme ⟶ (L.pow d).sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → ℂ)
    (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (hd : topologicalKrullDim (sectionIdeal k s hs v).subscheme = 1) :
    let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
      (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hd⟩
    curveDegree S L C = (d : ℤ)*selfIntersection S L := by
  let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
      (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hd⟩
  let f (n : ℕ) := eulerCharacteristic S.structureMap 2 (L.pow n).sheaf
  apply EulerNumerics.slope_of_quadratic f (selfIntersection S L) _ d _
    ((d : ℤ)*curveDegree S L C + eulerCharacteristic (C.embedding ≫ S.structureMap) 1 (O C.scheme))
  · intro n
    have H := generated_power_euler_difference S L hL L d k s hs v hne hd n
    change f (n+d)-f n = _ at H
    push_cast at H
    linarith
  · intro n
    have H := S.power_euler_quadratic L hL n
    rw [← S.euler_power_one L] at H
    exact H

end
end MaximalSeshadri.Geometry

end



end OAI
