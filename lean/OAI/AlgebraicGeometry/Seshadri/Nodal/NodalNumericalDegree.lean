import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Nodal.NodalIdealDegree
import OAI.AlgebraicGeometry.Seshadri.Intersection.SurfaceQuadraticEuler

namespace OAI


                                              
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem generated_power_euler_of_iso (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) (M : LineBundle S.scheme) (d : ℕ) (e : M.sheaf ≅ (L.pow d).sheaf)
    {σ : Type} [Fintype σ] (k : ℂ →+* Γ(S.scheme,⊤))
    (s : σ → (O S.scheme ⟶ M.sheaf)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → ℂ) (hne : sectionCombination k s v ≠ 0)
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
  let g : (M.tensor (L.pow n)).sheaf ≅ (L.pow (d+n)).sheaf :=
    moduleTensorIso e (Iso.refl (L.pow n).sheaf) ≪≫ (linePowerAdd L d n).symm
  have H := generated_section_euler_difference S L hL M (L.pow n) k s hs v hne hd
  have e₁ := eulerCharacteristic_iso S.structureMap g 2
  have e₂ := eulerCharacteristic_iso (C.embedding ≫ S.structureMap)
    ((Scheme.Modules.pullback C.embedding).mapIso g) 1
  have e₃ := curveDegree_pow S L hL L C (d+n)
  change eulerCharacteristic S.structureMap 2 (M.tensor (L.pow n)).sheaf =
    eulerCharacteristic S.structureMap 2 (L.pow (d+n)).sheaf at e₁
  change eulerCharacteristic (C.embedding ≫ S.structureMap) 1
      ((Scheme.Modules.pullback C.embedding).obj (M.tensor (L.pow n)).sheaf) =
    eulerCharacteristic (C.embedding ≫ S.structureMap) 1
      ((Scheme.Modules.pullback C.embedding).obj (L.pow (d+n)).sheaf) at e₂
  change eulerCharacteristic S.structureMap 2 (M.tensor (L.pow n)).sheaf -
    eulerCharacteristic S.structureMap 2 (L.pow n).sheaf =
      eulerCharacteristic (C.embedding ≫ S.structureMap) 1
        ((Scheme.Modules.pullback C.embedding).obj (M.tensor (L.pow n)).sheaf) at H
  rw [e₁,e₂] at H
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

theorem generated_curveDegree_of_power_iso (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) (M : LineBundle S.scheme) (d : ℕ) (e : M.sheaf ≅ (L.pow d).sheaf)
    {σ : Type} [Fintype σ] (k : ℂ →+* Γ(S.scheme,⊤))
    (s : σ → (O S.scheme ⟶ M.sheaf)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → ℂ) (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (hd : topologicalKrullDim (sectionIdeal k s hs v).subscheme = 1) :
    let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
      (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hd⟩
    curveDegree S L C = (d : ℤ)*selfIntersection S L := by
  let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
    (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hd⟩
  let f (n : ℕ) : ℤ := eulerCharacteristic S.structureMap 2 (L.pow n).sheaf
  apply EulerNumerics.slope_of_quadratic f (selfIntersection S L) _ d _
    ((d : ℤ)*curveDegree S L C + eulerCharacteristic (C.embedding ≫ S.structureMap) 1 (O C.scheme))
  · intro n
    have H := generated_power_euler_of_iso S L hL M d e k s hs v hne hd n
    change f (n+d)-f n = _ at H
    push_cast at H
    linarith
  · intro n
    have H := S.power_euler_quadratic L hL n
    rw [← S.euler_power_one L] at H
    exact H

theorem doublePointQuartic_curveDegree (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) (d a : ℕ) {σ : Type} [Fintype σ]
    (k : ℂ →+* Γ(S.scheme,⊤)) (s : Option σ → (O S.scheme ⟶ (L.pow d).sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : QuarticIndex σ → ℂ)
    (hne : sectionCombination k (doublePointQuartics s) v ≠ 0)
    [IsIntegral (doublePointQuarticIdeal k s hs v).subscheme]
    (hd : topologicalKrullDim (doublePointQuarticIdeal k s hs v).subscheme = 1) :
    curveDegree S (L.pow a) (IntegralCurve.ofIdeal S (doublePointQuarticIdeal k s hs v) hd) =
      (a : ℤ)*(d*4)*selfIntersection S L := by
  have hc : sectionCombination k (augmentedQuartics s) (fun j => j.elim 0 v) =
      sectionCombination k (doublePointQuartics s) v := by
    rw [sectionCombination_extend_zero]
    rfl
  have hn : sectionCombination k (augmentedQuartics s) (fun j => j.elim 0 v) ≠ 0 := by rwa [hc]
  have H := @generated_curveDegree_of_power_iso S L hL ((L.pow d).pow 4) (d*4)
    (linePowerMul L d 4) (Option (QuarticIndex σ)) inferInstance k
    (augmentedQuartics s) (augmentedQuartics_cover s hs) (fun j => j.elim 0 v) hn
    (inferInstanceAs (IsIntegral (doublePointQuarticIdeal k s hs v).subscheme)) hd
  rw [curveDegree_pow S L hL]
  change curveDegree S L (IntegralCurve.ofIdeal S (doublePointQuarticIdeal k s hs v) hd) =
    ((d*4 : ℕ) : ℤ)*selfIntersection S L at H
  rw [H]
  push_cast
  ring

end
end MaximalSeshadri.Geometry

end

end OAI
