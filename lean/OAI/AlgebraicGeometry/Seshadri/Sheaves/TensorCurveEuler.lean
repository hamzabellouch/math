import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorDivision

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.SectionOpens MaximalSeshadri.Projective

variable {X : Scheme.{0}}

lemma tensor_multiply_isoOpen (L M : LineBundle X) (s : O X ⟶ L.sheaf) :
    isoOpen (sectionMultiply L M s) = isoOpen s := by
  apply SetLike.coe_injective
  ext x
  obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames L M x
  have h : U.1.ι ⁻¹ᵁ isoOpen (sectionMultiply L M s) = U.1.ι ⁻¹ᵁ isoOpen s := by
    let restrictedMultiply : M.sheaf.restrict U.1.ι ⟶
        (L.tensor M).sheaf.restrict U.1.ι :=
      (Scheme.Modules.restrictFunctor U.1.ι).map (sectionMultiply L M s)
    let tensorTrivialization : (L.tensor M).sheaf.restrict U.1.ι ≅ O U.1.toScheme :=
      tensorFrame L M U.1 e f
    calc
      _ = isoOpen restrictedMultiply := (isoOpen_restrict (sectionMultiply L M s) U.1.ι).symm
      _ = isoOpen (restrictedMultiply ≫ tensorTrivialization.hom) :=
        (isoOpen_postcomp restrictedMultiply tensorTrivialization).symm
      _ = isoOpen (f.inv ≫ restrictedMultiply ≫ tensorTrivialization.hom) :=
        (isoOpen_precomp f.symm (restrictedMultiply ≫ tensorTrivialization.hom)).symm
      _ = isoOpen ((tensorUnitTwist M U.1 f).hom ≫ (restrictSection U.1.ι s ≫ e.hom)) :=
        congrArg (fun morphism : O U.1.toScheme ⟶ O U.1.toScheme => isoOpen morphism)
          (tensor_multiply_framed L M s U.1 e f)
      _ = isoOpen (restrictSection U.1.ι s ≫ e.hom) :=
        isoOpen_precomp (tensorUnitTwist M U.1 f) _
      _ = isoOpen (restrictSection U.1.ι s) := isoOpen_postcomp _ e
      _ = _ := isoOpen_restrictSection s U.1.ι
  exact SetLike.ext_iff.mp h ⟨x,hx⟩

lemma tensor_multiply_shortExact [IsIntegral X] (L M : LineBundle X)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) :
    (ShortComplex.mk (sectionMultiply L M s) (cokernel.π (sectionMultiply L M s))
      (cokernel.condition _)).ShortExact := by
  exact {
    exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
    mono_f := sectionMultiply_mono L M s hs }

theorem tensor_multiply_cokernel_flasque [IsIntegral X] [IsNoetherian X]
    (hd : topologicalKrullDim X ≤ 1) (L M : LineBundle X)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj
      (cokernel (sectionMultiply L M s))) := by
  let S : Set X := (isoOpen s : Set X)ᶜ
  have hfin : S.Finite := L.cokernel_support_finite hd s hs
  have hclosed : ∀ x ∈ S, IsClosed ({x} : Set X) := by
    intro x hx
    have hc : closure ({x} : Set X) ⊆ S :=
      closure_minimal (Set.singleton_subset_iff.mpr hx) (isoOpen s).isOpen.isClosed_compl
    have hsub : (closure ({x} : Set X)).Subsingleton := by
      apply proper_irreducible_closed_subsingleton hd isClosed_closure
        isIrreducible_singleton.closure
      intro he
      have hb : S = Set.univ := Set.eq_univ_of_univ_subset (he ▸ hc)
      exact L.isoOpen_ne_bot s hs (SetLike.coe_injective (by simpa [S] using hb))
    have he : closure ({x} : Set X) = {x} := by
      apply Set.Subset.antisymm
      · intro y hy
        exact hsub hy (subset_closure (Set.mem_singleton x))
      · exact subset_closure
    exact he ▸ isClosed_closure
  apply FiniteSupport.finite_closed_support_flasque _ S hfin hclosed
  intro x hx
  apply cokernel_stalk_subsingleton (sectionMultiply L M s) x
  rw [tensor_multiply_isoOpen]
  exact not_not.mp hx

lemma tensor_multiply_cokernel_ext_zero [IsIntegral X] [IsNoetherian X]
    (hd : topologicalKrullDim X ≤ 1) (L M : LineBundle X)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0)
    (n : ℕ) (z : cohomology (cokernel (sectionMultiply L M s)) (n+1)) : z = 0 := by
  let : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj
      (cokernel (sectionMultiply L M s))) := tensor_multiply_cokernel_flasque hd L M s hs
  exact FlasqueCohomology.flasque_ext_zero X.ringCatSheaf n
    (cokernel (sectionMultiply L M s)) z

variable [IsIntegral X] [IsNoetherian X]

theorem projective_tensor_cokernel_finite {σ : Type} [Fintype σ]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {A : X.Modules}
    (a : σ → (O X ⟶ A)) (ha : (⨆ i, SectionOpens.isoOpen (a i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (baseScalars p) a ha)]
    (L M : LineBundle X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0) (n : ℕ) :
    letI := Module.compHom (cohomology (cokernel (sectionMultiply L M s)) n) (baseScalars p)
    Module.Finite ℂ (cohomology (cokernel (sectionMultiply L M s)) n) := by
  let : IsClosedImmersion (sectionsMorphism
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) a ha) :=
    inferInstanceAs (IsClosedImmersion (sectionsMorphism (baseScalars p) a ha))
  cases n with
  | succ n =>
    let := Module.compHom (cohomology (cokernel (sectionMultiply L M s)) (n+1)) (baseScalars p)
    let : Subsingleton (cohomology (cokernel (sectionMultiply L M s)) (n+1)) := ⟨fun x y =>
      (tensor_multiply_cokernel_ext_zero hd.le L M s hs n x).trans (tensor_multiply_cokernel_ext_zero hd.le L M s hs n y).symm⟩
    infer_instance
  | zero =>
    let := sheafComplexLinear p
    let S : ShortComplex X.Modules :=
      ShortComplex.mk (sectionMultiply L M s) (cokernel.π (sectionMultiply L M s)) (cokernel.condition _)
    have hS := tensor_multiply_shortExact L M s hs
    let hL : Module.Finite ℂ (cohomology (L.tensor M).sheaf 0) := by
      change @Module.Finite ℂ (cohomology (L.tensor M).sheaf 0) _ _ (complexExtModule p (L.tensor M).sheaf 0)
      rw [complexExtModule_eq]
      exact projective_curve_cohomology_finite p hd a ha (L.tensor M) 0
    let hO : Module.Finite ℂ (cohomology M.sheaf 1) := by
      change @Module.Finite ℂ (cohomology M.sheaf 1) _ _ (complexExtModule p M.sheaf 1)
      rw [complexExtModule_eq]
      exact projective_curve_cohomology_finite p hd a ha M 1
    let : Module.Finite ℂ (Ext (O X) S.X₂ 0) := hL
    let : Module.Finite ℂ (Ext (O X) S.X₁ (0+1)) := hO
    have he := Cohomology.finite_middle_of_exact
      (Cohomology.cohomologyMap₂ (K := ℂ) (O X) (S := S) 0)
      (Cohomology.cohomologyBoundary (K := ℂ) (O X) hS 0)
      (Cohomology.cohomology_exact₃ (K := ℂ) (O X) hS 0)
    change @Module.Finite ℂ (cohomology (cokernel (sectionMultiply L M s)) 0) _ _
      (complexExtModule p (cokernel (sectionMultiply L M s)) 0) at he
    rw [complexExtModule_eq] at he
    exact he

theorem projective_tensor_euler_difference {σ : Type} [Fintype σ]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {A : X.Modules}
    (a : σ → (O X ⟶ A)) (ha : (⨆ i, SectionOpens.isoOpen (a i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (baseScalars p) a ha)]
    (L M : LineBundle X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0) :
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
      letI := Module.compHom Γ(cokernel (sectionMultiply L M s), ⊤) (baseScalars p)
      (Module.finrank ℂ Γ(cokernel (sectionMultiply L M s),⊤) : ℤ) := by
  let : IsClosedImmersion (sectionsMorphism
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) a ha) :=
    inferInstanceAs (IsClosedImmersion (sectionsMorphism (baseScalars p) a ha))
  let : M.sheaf.IsQuasicoherent := M.quasicoherent
  let : Subsingleton (cohomology M.sheaf (1+1)) := ⟨fun x y =>
    (projective_curve_ext_zero p hd a ha M.sheaf 0 x).trans
      (projective_curve_ext_zero p hd a ha M.sheaf 0 y).symm⟩
  have he := eulerCharacteristic_add p (tensor_multiply_shortExact L M s hs) 1
    (fun n _ => projective_curve_cohomology_finite p hd a ha M n)
    (fun n _ => projective_curve_cohomology_finite p hd a ha (L.tensor M) n)
    (fun n _ => projective_tensor_cokernel_finite p hd a ha L M s hs n)
  change eulerCharacteristic p 1 (L.tensor M).sheaf =
    eulerCharacteristic p 1 M.sheaf + eulerCharacteristic p 1 (cokernel (sectionMultiply L M s)) at he
  rw [he, add_sub_cancel_left]
  rw [eulerCharacteristic, Finset.sum_range_succ, Finset.sum_range_succ]
  let : Subsingleton (cohomology (cokernel (sectionMultiply L M s)) 1) := ⟨fun x y =>
    (tensor_multiply_cokernel_ext_zero hd.le L M s hs 0 x).trans (tensor_multiply_cokernel_ext_zero hd.le L M s hs 0 y).symm⟩
  have hz : cohomologyDimension p (cokernel (sectionMultiply L M s)) 1 = 0 := by
    let := Module.compHom (cohomology (cokernel (sectionMultiply L M s)) 1) (baseScalars p)
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
