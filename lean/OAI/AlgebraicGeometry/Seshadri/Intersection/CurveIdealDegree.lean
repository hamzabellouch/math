import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorInclusion
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.IdealEquation
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorPowerDistribution
import OAI.AlgebraicGeometry.Seshadri.Intersection.MixedIntersection
import OAI.AlgebraicGeometry.Seshadri.Intersection.ArbitraryCartierEuler

namespace OAI


                                          
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem IntegralCurve.ideal_euler_difference (S : Surface)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (C : IntegralCurve S)
    (J : LineBundle S.scheme) (ι : J.sheaf ⟶ O S.scheme)
    (h : PresentsPullbackIdeal C.embedding.ker (𝟙 S.scheme) J ι)
    (M : LineBundle S.scheme) :
    eulerCharacteristic S.structureMap 2 M.sheaf -
      eulerCharacteristic S.structureMap 2 (J.tensor M).sheaf =
      eulerCharacteristic (C.embedding ≫ S.structureMap) 1
        ((Scheme.Modules.pullback C.embedding).obj M.sheaf) := by
  have : Mono ι := h.1
  have := tensorInclusion_mono J M ι
  apply C.cartier_euler_difference S A hA (J.tensor M) M (tensorInclusion J M ι)
  intro x
  obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames J M x
  refine ⟨U,hx,tensorFrame J M U.1 e f,f,?_⟩
  rw [tensor_inclusion_ideal]
  exact InvertibleLocal.presented_frame_equation C.embedding.ker J ι h U e

lemma mixedEuler_comm (S : Surface) (L M : LineBundle S.scheme) :
    mixedEuler S L M = mixedEuler S M L := by
  have h := eulerCharacteristic_iso S.structureMap (moduleTensorComm L.sheaf M.sheaf) 2
  unfold mixedEuler
  change eulerCharacteristic S.structureMap 2 (L.tensor M).sheaf =
    eulerCharacteristic S.structureMap 2 (M.tensor L).sheaf at h
  rw [h]
  ring

theorem IntegralCurve.ideal_mixed_degree (S : Surface)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (C : IntegralCurve S)
    (J : LineBundle S.scheme) (ι : J.sheaf ⟶ O S.scheme)
    (h : PresentsPullbackIdeal C.embedding.ker (𝟙 S.scheme) J ι)
    (M : LineBundle S.scheme) :
    mixedEuler S M J = -curveDegree S M C := by
  have hM := C.ideal_euler_difference S A hA J ι h M
  have hO := C.ideal_euler_difference S A hA J ι h (A.pow 0)
  have he := eulerCharacteristic_iso S.structureMap (moduleTensorRightUnit J.sheaf) 2
  have hp := eulerCharacteristic_iso (C.embedding ≫ S.structureMap)
    (pullbackUnitIso C.embedding) 1
  rw [mixedEuler_comm]
  change eulerCharacteristic S.structureMap 2 (O S.scheme) -
    eulerCharacteristic S.structureMap 2 (moduleTensor S.scheme J.sheaf (O S.scheme)) =
      eulerCharacteristic (C.embedding ≫ S.structureMap) 1
        ((Scheme.Modules.pullback C.embedding).obj (O S.scheme)) at hO
  change eulerCharacteristic S.structureMap 2 (moduleTensor S.scheme J.sheaf (O S.scheme)) =
    eulerCharacteristic S.structureMap 2 J.sheaf at he
  rw [he,hp] at hO
  unfold mixedEuler curveDegree
  dsimp only [O] at *
  linarith

theorem mixedEuler_tensor_right (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple)
    (M N : LineBundle S.scheme) :
    mixedEuler S L (M.tensor N) = mixedEuler S L M + mixedEuler S L N := by
  classical
  obtain ⟨d,hd,-,n,s,hs,v,hne,hi,hC⟩ := S.coprime_integral_section L hL 1 (by decide)
  have := hi
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
    (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hC⟩
  have h₁ := generated_curveDegree_eq_mixedEuler S L hL M d k s hs v hne hC
  have h₂ := generated_curveDegree_eq_mixedEuler S L hL N d k s hs v hne hC
  have h₃ := generated_curveDegree_eq_mixedEuler S L hL (M.tensor N) d k s hs v hne hC
  change curveDegree S M C = (d : ℤ)*mixedEuler S L M at h₁
  change curveDegree S N C = (d : ℤ)*mixedEuler S L N at h₂
  change curveDegree S (M.tensor N) C = (d : ℤ)*mixedEuler S L (M.tensor N) at h₃
  rw [curveDegree_tensor S L hL,h₁,h₂] at h₃
  have hd' : (d : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  apply mul_left_cancel₀ hd'
  rw [← h₃]
  ring

end
end MaximalSeshadri.Geometry

end

end OAI
