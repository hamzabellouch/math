import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.SurfaceTwistEuler

namespace OAI


                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem generated_curveDegree_eq_mixedEuler (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (M : LineBundle S.scheme) (d : ℕ)
    {σ : Type} [Fintype σ] (k : ℂ →+* Γ(S.scheme,⊤))
    (s : σ → (O S.scheme ⟶ (L.pow d).sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → ℂ)
    (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (hd : topologicalKrullDim (sectionIdeal k s hs v).subscheme = 1) :
    let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
      (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hd⟩
    curveDegree S M C = (d : ℤ)*mixedEuler S L M := by
  let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
      (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hd⟩
  have h := generated_twist_euler_difference S L hL L M d k s hs v hne hd 0
  have h' := generated_power_euler_difference S L hL L d k s hs v hne hd 0
  have h₀ := S.twist_euler L hL M 0
  have h₁ := S.twist_euler L hL M d
  simp only [Nat.zero_add,Nat.cast_zero,zero_mul,add_zero] at h h' h₀
  change curveDegree S M C = _
  linarith

theorem mixedEuler_pow_right (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple)
    (M : LineBundle S.scheme) (n : ℕ) :
    mixedEuler S L (M.pow n) = (n : ℤ)*mixedEuler S L M := by
  classical
  obtain ⟨d,hd,-,N,s,hs,v,hne,hi,hC⟩ := S.coprime_integral_section L hL 1 (by decide)
  let := hi
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
    (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hC⟩
  have h₁ := generated_curveDegree_eq_mixedEuler S L hL M d k s hs v hne hC
  have h₂ := generated_curveDegree_eq_mixedEuler S L hL (M.pow n) d k s hs v hne hC
  change curveDegree S M C = (d : ℤ)*mixedEuler S L M at h₁
  change curveDegree S (M.pow n) C = (d : ℤ)*mixedEuler S L (M.pow n) at h₂
  rw [curveDegree_pow S L hL,h₁] at h₂
  have hd' : (d : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  apply mul_left_cancel₀ hd'
  rw [← h₂]
  ring

end
end MaximalSeshadri.Geometry

end



end OAI
