import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.SurfaceTopGrowth

namespace OAI


                                      
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]

omit [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] in
lemma curve_euler_expansion (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) :
    eulerCharacteristic p 1 M =
      (cohomologyDimension p M 0 : ℤ) - (cohomologyDimension p M 1 : ℤ) := by
  simp [eulerCharacteristic,Finset.sum_range_succ,sub_eq_add_neg]

theorem projective_curve_H1_le {σ : Type} [Fintype σ]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {A : X.Modules}
    (a : σ → (O X ⟶ A)) (ha : (⨆ i, SectionOpens.isoOpen (a i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (baseScalars p) a ha)]
    (M : LineBundle X)
    (hdeg : 0 ≤ eulerCharacteristic p 1 M.sheaf - eulerCharacteristic p 1 (O X)) :
    cohomologyDimension p M.sheaf 1 ≤ cohomologyDimension p (O X) 1 := by
  classical
  have : IsClosedImmersion (sectionsMorphism
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) a ha) :=
      inferInstanceAs (IsClosedImmersion (sectionsMorphism (baseScalars p) a ha))
  by_cases h : ∃ s : O X ⟶ M.sheaf, s ≠ 0
  · obtain ⟨s,hs⟩ := h
    have : Subsingleton (cohomology (cokernel s) 1) := ⟨fun x y =>
      (M.cokernel_ext_zero hd.le s hs 0 x).trans (M.cokernel_ext_zero hd.le s hs 0 y).symm⟩
    let B : LineBundle X := ⟨O X, fun x =>
      ⟨⊤,trivial,⟨Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι⟩⟩⟩
    exact cohomologyDimension_le_of_shortExact p (M.section_shortExact s hs) 1
      (projective_curve_cohomology_finite p hd a ha B 1)
  · have hz : cohomologyDimension p M.sheaf 0 = 0 := by
      let := Module.compHom (cohomology M.sheaf 0) (baseScalars p)
      have : Subsingleton (cohomology M.sheaf 0) := ⟨fun x y => by
        apply (Ext.linearEquiv₀ (R := Γ(X,⊤))).injective
        apply Eq.trans (not_exists.mp h _ |> not_not.mp)
        exact (not_exists.mp h _ |> not_not.mp).symm⟩
      exact Module.finrank_zero_of_subsingleton
    rw [curve_euler_expansion,curve_euler_expansion,hz] at hdeg
    have h0 : (0 : ℤ) ≤ cohomologyDimension p (O X) 0 := Nat.cast_nonneg _
    exact_mod_cast (show (cohomologyDimension p M.sheaf 1 : ℤ) ≤
      cohomologyDimension p (O X) 1 by omega)
                                                                  
theorem IntegralCurve.H1_le (S : Surface) (C : IntegralCurve S)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (M : LineBundle C.scheme)
    (hdeg : 0 ≤ eulerCharacteristic (C.embedding ≫ S.structureMap) 1 M.sheaf -
      eulerCharacteristic (C.embedding ≫ S.structureMap) 1 (O C.scheme)) :
    cohomologyDimension (C.embedding ≫ S.structureMap) M.sheaf 1 ≤
      cohomologyDimension (C.embedding ≫ S.structureMap) (O C.scheme) 1 := by
  obtain ⟨σ,hσ,N,a,ha,hclosed⟩ := C.exists_projective_sections S A hA
  let := hσ
  have := hclosed
  exact projective_curve_H1_le (C.embedding ≫ S.structureMap) C.dimension a ha M hdeg
end
end MaximalSeshadri.Geometry

end

end OAI
