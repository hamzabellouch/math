import Mathlib
import OAI.AlgebraicGeometry.RelativeTriviality.FiniteSections

namespace OAI

noncomputable section

namespace CampanaPeternellSix.RelativeCech
section
open CategoryTheory AlgebraicGeometry Limits Opposite TopologicalSpace
universe u v w
variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J RingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

lemma free_free_evaluation (I : Type u) [Finite I] (U : Cᵒᵖ) :
    Module.Free (𝒪.obj.obj U) ((SheafOfModules.evaluation 𝒪 U).obj
      (SheafOfModules.free I)) := by
  classical
  let := Fintype.ofFinite I
  let F := SheafOfModules.evaluation 𝒪 U
  let f : I → SheafOfModules 𝒪 := fun _ ↦ SheafOfModules.unit 𝒪
  let : HasBiproduct f := HasBiproduct.of_hasProduct f
  let i₁ : SheafOfModules.free I ≅ ∏ᶜ f :=
    (biproduct.isoCoproduct f).symm ≪≫ biproduct.isoProduct f
  let i₂ := F.mapIso i₁ ≪≫ asIso (piComparison F f) ≪≫ ModuleCat.piIsoPi (F.obj ∘ f)
  have : Module.Free (𝒪.obj.obj U) (ModuleCat.of (𝒪.obj.obj U) ((i : I) → (F.obj (f i)))) := by
    change Module.Free (𝒪.obj.obj U) (I → (𝒪.obj.obj U))
    infer_instance
  exact Module.Free.of_equiv' this i₂.symm.toLinearEquiv

lemma free_sections_of_le_frame (X : Scheme.{u}) (E : X.Modules)
    (q : E.LocalGeneratorsData) [q.IsLocallyFreeData] [q.IsFiniteType]
    (i : q.I) (V : X.Opens) (hV : V ≤ q.X i) : Module.Free Γ(X,V) Γ(E,V) := by
  have := SheafOfModules.LocalGeneratorsData.IsFiniteType.isFiniteType (p := q) i
  have := SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.isIso (q := q) i
  let a : Over (q.X i) := Over.mk (homOfLE hV)
  let F := SheafOfModules.evaluation (X.ringCatSheaf.over (q.X i)) (op a)
  have := free_free_evaluation (X.ringCatSheaf.over (q.X i)) (q.generators i).I (op a)
  let : CommRing ((X.ringCatSheaf.over (q.X i)).obj.obj (op a)) :=
    inferInstanceAs (CommRing Γ(X,V))
  change Module.Free ((X.ringCatSheaf.over (q.X i)).obj.obj (op a))
    (F.obj (E.over (q.X i)))
  exact Module.Free.of_equiv
    (R := ↑((X.ringCatSheaf.over (q.X i)).obj.obj (op a)))
    (F.mapIso (asIso (q.generators i).π)).toLinearEquiv

end

section
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
universe u v w z
lemma flat_of_semilinearEquiv {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {M : Type w} {N : Type z} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (e : R ≃+* S) (f : LinearEquiv (e : R →+* S) (σ' := (e.symm : S →+* R)) M N) [Module.Flat R M] : Module.Flat S N := by
  let : Algebra S R := e.symm.toRingHom.toAlgebra
  let er : S ≃ₗ[S] R := { e.symm with map_smul' := fun a b => e.symm.map_mul a b }
  have : Module.Flat S R := Module.Flat.of_linearEquiv er.symm
  let : Module R N := Module.compHom N e.toRingHom
  let fl : M ≃ₗ[R] N := { f.toAddEquiv with map_smul' := f.map_smul' }
  have : Module.Flat R N := Module.Flat.of_linearEquiv fl.symm
  let : IsScalarTower S R N := ⟨fun s r n => by
    change e (e.symm s * r) • n = s • e r • n
    rw [map_mul, e.apply_symm_apply, mul_smul]⟩
  exact Module.Flat.trans S R N
end

section
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
open CategoryTheory AlgebraicGeometry Limits Opposite TopologicalSpace
universe u
lemma free_restriction_sections (X Y : Scheme.{u}) (E : Y.Modules)
    (f : X ⟶ Y) [IsOpenImmersion f] (U : X.Opens)
    [Module.Free Γ(Y, f ''ᵁ U) Γ(E, f ''ᵁ U)] :
    Module.Free Γ(X,U) Γ(E.restrict f,U) := by
  let e := (f.appIso U).commRingCatIsoToRingEquiv
  let g : LinearEquiv (e : Γ(Y,f ''ᵁ U) →+* Γ(X,U)) (σ' := (e.symm : Γ(X,U) →+* Γ(Y,f ''ᵁ U))) Γ(E, f ''ᵁ U) Γ(E.restrict f,U) := {
    toFun := (E.restrictAppIso f U).inv
    invFun := (E.restrictAppIso f U).hom
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := map_add _
    map_smul' := fun r m ↦ by
      exact Scheme.Modules.smul_restrictAppIso_inv_apply f E U r m
  }
  exact Module.Free.of_equiv g

theorem flat_affine_restriction (R : CommRingCat.{u}) (X : Scheme.{u})
    (E : X.Modules)
    (hE : ∃ q : E.LocalGeneratorsData, q.IsLocallyFreeData ∧ q.IsFiniteType)
    (f : Spec R ⟶ X) [IsOpenImmersion f] :
    Module.Flat R (moduleSpecΓFunctor.obj (E.restrict f)) := by
  classical
  obtain ⟨q, hq, ht⟩ := hE
  let := hq
  let := ht
  let := q.isLocallyFree
  have : E.IsQuasicoherent := q.quasiCoherentData.isQuasicoherent
  let T : Set R := {r | ∃ i, f ''ᵁ (PrimeSpectrum.basicOpen r) ≤ q.X i}
  have hT : Ideal.span T = ⊤ := by
    have he : Set.range (fun r : T ↦ (r : R)) = T := by ext r; simp
    rw [← he, ← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
    apply top_unique
    intro x hx
    have hcov := (Opens.coversTop_iff _ _).mp q.coversTop
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show f x ∈ ⨆ i, q.X i from by rw [hcov]; trivial)
    obtain ⟨V, ⟨r, rfl⟩, hxV, hV⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hi
        (f ⁻¹ᵁ (q.X i)).isOpen
    refine Opens.mem_iSup.mpr ⟨⟨r, i, ?_⟩, hxV⟩
    rintro y ⟨z, hz, rfl⟩
    exact hV hz
  let E' := E.restrict f
  let M := modulesSpecToSheaf.obj E'
  let D (r : R) : (Spec R).Opens := PrimeSpectrum.basicOpen r
  have : E'.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor f E
  have : IsIso E'.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent E'
  let res (r : T) : moduleSpecΓFunctor.obj E' →ₗ[R] Γ(E', D r.val) :=
    (M.obj.map (show (Spec R).Opens from PrimeSpectrum.basicOpen r.val).leTop.op).hom
  have (r : T) : IsLocalizedModule.Away r.val (res r) :=
    (isIso_fromTildeΓ_iff_isLocalizing E').mp inferInstance r.val
  let : IsScalarTower R R (moduleSpecΓFunctor.obj E') := ⟨mul_smul⟩
  apply Module.flat_of_isLocalized_span (R := R) R (moduleSpecΓFunctor.obj E') T hT
    (fun r => Γ(E', D r.val)) res
  intro r
  obtain ⟨i, hi⟩ := r.property
  have := free_sections_of_le_frame X E q i _ hi
  have := free_restriction_sections (Spec R) X E f (PrimeSpectrum.basicOpen r.val)
  have : Module.Flat R Γ(Spec R, D r.val) :=
    IsLocalization.flat _ (Submonoid.powers r.val)
  exact Module.Flat.trans R Γ(Spec R, D r.val)
    Γ(E', D r.val)

lemma flat_affine_image (R : CommRingCat.{u}) (X : Scheme.{u})
    (E : X.Modules)
    (hE : ∃ q : E.LocalGeneratorsData, q.IsLocallyFreeData ∧ q.IsFiniteType)
    (f : Spec R ⟶ X) [IsOpenImmersion f] :
    Module.Flat Γ(X,f ''ᵁ ⊤) Γ(E, f ''ᵁ ⊤) := by
  have := flat_affine_restriction R X E hE f
  let e := ((Scheme.ΓSpecIso R).symm ≪≫ (f.appIso ⊤).symm).commRingCatIsoToRingEquiv
  let m : LinearEquiv (e : R →+* Γ(X,f ''ᵁ ⊤)) (σ' := (e.symm : Γ(X,f ''ᵁ ⊤) →+* R)) (moduleSpecΓFunctor.obj (E.restrict f)) Γ(E,f ''ᵁ ⊤) := {
    toFun := (E.restrictAppIso f ⊤).hom
    invFun := (E.restrictAppIso f ⊤).inv
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := map_add _
    map_smul' := fun r m ↦ by
      exact Scheme.Modules.smul_restrictAppIso_hom_apply f E ⊤
        ((Scheme.ΓSpecIso R).inv r) m
  }
  exact flat_of_semilinearEquiv e m

lemma flat_affine_open (X : Scheme.{u}) (E : X.Modules)
    (hE : ∃ q : E.LocalGeneratorsData, q.IsLocallyFreeData ∧ q.IsFiniteType)
    (U : X.Opens) (hU : IsAffineOpen U) : Module.Flat Γ(X,U) Γ(E,U) := by
  have h := flat_affine_image Γ(X,U) X E hE hU.fromSpec
  rw [hU.fromSpec.image_top_eq_opensRange, hU.opensRange_fromSpec] at h
  exact h
end

open CategoryTheory AlgebraicGeometry Limits Opposite TopologicalSpace
universe u
theorem finitePresentation_affine_restriction (R : CommRingCat.{u}) (X : Scheme.{u})
    (E : X.Modules)
    (hE : ∃ q : E.LocalGeneratorsData, q.IsLocallyFreeData ∧ q.IsFiniteType)
    (f : Spec R ⟶ X) [IsOpenImmersion f] :
    Module.FinitePresentation R (moduleSpecΓFunctor.obj (E.restrict f)) := by
  classical
  obtain ⟨q, hq, ht⟩ := hE
  let := hq
  let := ht
  let := q.isLocallyFree
  have : E.IsQuasicoherent := q.quasiCoherentData.isQuasicoherent
  let T : Set R := {r | ∃ i, f ''ᵁ (PrimeSpectrum.basicOpen r) ≤ q.X i}
  have hT : Ideal.span T = ⊤ := by
    have he : Set.range (fun r : T ↦ (r : R)) = T := by ext r; simp
    rw [← he, ← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
    apply top_unique
    intro x hx
    have hcov := (Opens.coversTop_iff _ _).mp q.coversTop
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show f x ∈ ⨆ i, q.X i from by rw [hcov]; trivial)
    obtain ⟨V, ⟨r, rfl⟩, hxV, hV⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hi
        (f ⁻¹ᵁ (q.X i)).isOpen
    refine Opens.mem_iSup.mpr ⟨⟨r, i, ?_⟩, hxV⟩
    rintro y ⟨z, hz, rfl⟩
    exact hV hz
  let E' := E.restrict f
  let M := modulesSpecToSheaf.obj E'
  let D (r : R) : (Spec R).Opens := PrimeSpectrum.basicOpen r
  have : E'.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor f E
  have : IsIso E'.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent E'
  let res (r : T) : moduleSpecΓFunctor.obj E' →ₗ[R] Γ(E', D r.val) :=
    (M.obj.map (show (Spec R).Opens from PrimeSpectrum.basicOpen r.val).leTop.op).hom
  have (r : T) : IsLocalizedModule.Away r.val (res r) :=
    (isIso_fromTildeΓ_iff_isLocalizing E').mp inferInstance r.val
  apply Module.FinitePresentation.of_localizationSpan' T hT
    (Rₚ := fun r => Γ(Spec R, D r.val)) res
  intro r
  obtain ⟨i, hi⟩ := r.property
  have := free_sections_of_le_frame X E q i _ hi
  have := finite_sections_of_le_frame X E q i _ hi
  have := free_restriction_sections (Spec R) X E f (PrimeSpectrum.basicOpen r.val)
  have := finite_restriction_sections (Spec R) X E f (PrimeSpectrum.basicOpen r.val)
  exact Module.finitePresentation_of_projective _ _

end CampanaPeternellSix.RelativeCech

end

end OAI
