import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.AllCurveDegree

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.SectionOpens MaximalSeshadri.Frames

section Curve
variable {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
variable {σ : Type} [Fintype σ]
variable (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {A : X.Modules}
    (a : σ → (O X ⟶ A)) (ha : (⨆ i, isoOpen (a i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (baseScalars p) a ha)]
include hd a ha

theorem projective_negative_degree_section_zero (L : LineBundle X)
    (hL : eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (O X) < 0)
    (s : O X ⟶ L.sheaf) : s = 0 := by
  by_contra hs
  have he := projective_section_euler_difference p hd a ha L s hs
  let := Module.compHom Γ(CategoryTheory.Limits.cokernel s,⊤) (baseScalars p)
  have hn : (0 : ℤ) ≤ Module.finrank ℂ Γ(CategoryTheory.Limits.cokernel s,⊤) :=
    Nat.cast_nonneg _
  rw [he] at hL
  omega

theorem projective_degree_zero_section_isoOpen (L : LineBundle X)
    (hL : eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (O X) = 0)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) : isoOpen s = ⊤ := by
  by_contra hz
  have hh := projective_section_positive_degree p hd a ha L s hs hz
  rw [hL] at hh
  exact (lt_irrefl _ hh)

theorem projective_negative_degree_power_section_zero (L : LineBundle X)
    (hL : eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (O X) < 0)
    (n : ℕ) (hn : 0 < n) (s : O X ⟶ (L.pow n).sheaf) : s = 0 := by
  apply projective_negative_degree_section_zero p hd a ha (L.pow n) _ s
  rw [projective_curve_power_euler p hd a ha L n]
  exact mul_neg_of_pos_of_neg (by exact_mod_cast hn) hL

end Curve

theorem IntegralCurve.negative_degree_section_zero (S : Surface) (C : IntegralCurve S)
    (A L : LineBundle S.scheme) (hA : A.IsAmple) (hL : curveDegree S L C < 0)
    (s : O C.scheme ⟶ (L.pullback C.embedding).sheaf) : s = 0 := by
  obtain ⟨σ,hσ,B,a,ha,hc⟩ := C.exists_projective_sections S A hA
  let := hσ
  let := hc
  exact projective_negative_degree_section_zero (C.embedding ≫ S.structureMap)
    C.dimension a ha (L.pullback C.embedding) hL s

end
end MaximalSeshadri.Geometry
end

end
end


end OAI
