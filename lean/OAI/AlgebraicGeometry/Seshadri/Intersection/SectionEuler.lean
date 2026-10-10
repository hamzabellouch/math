import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.ProjectiveCurveCohomology
import OAI.AlgebraicGeometry.Seshadri.Intersection.FiniteEuler
import OAI.AlgebraicGeometry.Seshadri.Intersection.EulerExact
import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionCokernel
import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionMono

namespace OAI

section
noncomputable section
                                      
section

namespace MaximalSeshadri.Cohomology
noncomputable section
open CategoryTheory CategoryTheory.Abelian

lemma finite_middle_of_exact {K U V W : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Module.Finite K U] [Module.Finite K W]
    (f : U →ₗ[K] V) (g : V →ₗ[K] W) (h : Function.Exact f g) :
    Module.Finite K V := by
  have he : Function.Exact f g.rangeRestrict := by
    intro x
    rw [Subtype.ext_iff]
    exact h x
  exact Module.Finite.of_exact he g.surjective_rangeRestrict
end
end MaximalSeshadri.Cohomology

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames

variable {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]

omit [AlgebraicGeometry.IsNoetherian X] in
lemma LineBundle.section_shortExact (L : LineBundle X) (s : O X ⟶ L.sheaf)
    (hs : s ≠ 0) : (ShortComplex.mk s (cokernel.π s) (cokernel.condition s)).ShortExact := by
  exact {
    exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel s)
    mono_f := L.mono_section s hs }

lemma LineBundle.cokernel_ext_zero (hd : topologicalKrullDim X ≤ 1)
    (L : LineBundle X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0)
    (n : ℕ) (z : cohomology (cokernel s) (n+1)) : z = 0 := by
  let := L.cokernel_flasque hd s hs
  exact FlasqueCohomology.flasque_ext_zero X.ringCatSheaf n (cokernel s) z

theorem projective_section_cokernel_finite {σ : Type} [Fintype σ]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {M : X.Modules}
    (a : σ → (O X ⟶ M)) (ha : (⨆ i, SectionOpens.isoOpen (a i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (baseScalars p) a ha)]
    (L : LineBundle X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0) (n : ℕ) :
    letI := Module.compHom (cohomology (cokernel s) n) (baseScalars p)
    Module.Finite ℂ (cohomology (cokernel s) n) := by
  let : IsClosedImmersion (sectionsMorphism
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) a ha) :=
    inferInstanceAs (IsClosedImmersion (sectionsMorphism (baseScalars p) a ha))
  cases n with
  | succ n =>
    let := Module.compHom (cohomology (cokernel s) (n+1)) (baseScalars p)
    let : Subsingleton (cohomology (cokernel s) (n+1)) := ⟨fun x y =>
      (L.cokernel_ext_zero hd.le s hs n x).trans (L.cokernel_ext_zero hd.le s hs n y).symm⟩
    infer_instance
  | zero =>
    let := sheafComplexLinear p
    let B : LineBundle X := ⟨O X, fun x =>
      ⟨⊤,trivial,⟨Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι⟩⟩⟩
    let S := ShortComplex.mk s (cokernel.π s) (cokernel.condition s)
    have hS := L.section_shortExact s hs
    let hL : Module.Finite ℂ (cohomology L.sheaf 0) := by
      change @Module.Finite ℂ (cohomology L.sheaf 0) _ _ (complexExtModule p L.sheaf 0)
      rw [complexExtModule_eq]
      exact projective_curve_cohomology_finite p hd a ha L 0
    let hO : Module.Finite ℂ (cohomology (O X) 1) := by
      change @Module.Finite ℂ (cohomology (O X) 1) _ _ (complexExtModule p (O X) 1)
      rw [complexExtModule_eq]
      exact projective_curve_cohomology_finite p hd a ha B 1
    let : Module.Finite ℂ (Ext (O X) S.X₂ 0) := hL
    let : Module.Finite ℂ (Ext (O X) S.X₁ (0+1)) := hO
    have he := Cohomology.finite_middle_of_exact
      (Cohomology.cohomologyMap₂ (K := ℂ) (O X) (S := S) 0)
      (Cohomology.cohomologyBoundary (K := ℂ) (O X) hS 0)
      (Cohomology.cohomology_exact₃ (K := ℂ) (O X) hS 0)
    change @Module.Finite ℂ (cohomology (cokernel s) 0) _ _
      (complexExtModule p (cokernel s) 0) at he
    rw [complexExtModule_eq] at he
    exact he

theorem projective_section_euler_difference {σ : Type} [Fintype σ]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {M : X.Modules}
    (a : σ → (O X ⟶ M)) (ha : (⨆ i, SectionOpens.isoOpen (a i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (baseScalars p) a ha)]
    (L : LineBundle X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0) :
    eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (O X) =
      letI := Module.compHom Γ(cokernel s, ⊤) (baseScalars p)
      (Module.finrank ℂ Γ(cokernel s,⊤) : ℤ) := by
  let : IsClosedImmersion (sectionsMorphism
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) a ha) :=
    inferInstanceAs (IsClosedImmersion (sectionsMorphism (baseScalars p) a ha))
  let B : LineBundle X := ⟨O X, fun x =>
    ⟨⊤,trivial,⟨Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι⟩⟩⟩
  let : (O X).IsQuasicoherent := B.quasicoherent
  let : Subsingleton (cohomology (O X) (1+1)) := ⟨fun x y =>
    (projective_curve_ext_zero p hd a ha (O X) 0 x).trans
      (projective_curve_ext_zero p hd a ha (O X) 0 y).symm⟩
  have he := eulerCharacteristic_add p (L.section_shortExact s hs) 1
    (fun n _ => projective_curve_cohomology_finite p hd a ha B n)
    (fun n _ => projective_curve_cohomology_finite p hd a ha L n)
    (fun n _ => projective_section_cokernel_finite p hd a ha L s hs n)
  change eulerCharacteristic p 1 L.sheaf =
    eulerCharacteristic p 1 (O X) + eulerCharacteristic p 1 (cokernel s) at he
  rw [he, add_sub_cancel_left]
  rw [eulerCharacteristic, Finset.sum_range_succ, Finset.sum_range_succ]
  let : Subsingleton (cohomology (cokernel s) 1) := ⟨fun x y =>
    (L.cokernel_ext_zero hd.le s hs 0 x).trans (L.cokernel_ext_zero hd.le s hs 0 y).symm⟩
  have hz : cohomologyDimension p (cokernel s) 1 = 0 := by
    let := Module.compHom (cohomology (cokernel s) 1) (baseScalars p)
    exact Module.finrank_zero_of_subsingleton
  simp only [Finset.sum_range_zero, zero_add, pow_zero, one_mul,
    hz, Nat.cast_zero, mul_zero, add_zero]
  rw [cohomologyDimension_zero]
end
end MaximalSeshadri.Geometry
end


end
end

end OAI
