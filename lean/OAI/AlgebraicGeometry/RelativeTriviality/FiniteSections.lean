import Mathlib

namespace OAI

noncomputable section

namespace CampanaPeternellSix.RelativeCech
section
open CategoryTheory AlgebraicGeometry Limits Opposite TopologicalSpace
universe u v w
variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J RingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

private lemma finiteRingPi (A : RingCat.{u}) (I : Type u) [Finite I] :
    Module.Finite A (I → A) := inferInstance

lemma finite_free_evaluation (I : Type u) [Finite I] (U : Cᵒᵖ) :
    Module.Finite (𝒪.obj.obj U) ((SheafOfModules.evaluation 𝒪 U).obj
      (SheafOfModules.free I)) := by
  classical
  let := Fintype.ofFinite I
  let F := SheafOfModules.evaluation 𝒪 U
  let f : I → SheafOfModules 𝒪 := fun _ ↦ SheafOfModules.unit 𝒪
  let : HasBiproduct f := HasBiproduct.of_hasProduct f
  let i₁ : SheafOfModules.free I ≅ ∏ᶜ f :=
    (biproduct.isoCoproduct f).symm ≪≫ biproduct.isoProduct f
  let i₂ := F.mapIso i₁ ≪≫ asIso (piComparison F f) ≪≫ ModuleCat.piIsoPi (F.obj ∘ f)
  have : Module.Finite (𝒪.obj.obj U) (ModuleCat.of (𝒪.obj.obj U) ((i : I) → (F.obj (f i)))) := by
    change Module.Finite (𝒪.obj.obj U) (I → (𝒪.obj.obj U))
    exact finiteRingPi (𝒪.obj.obj U) I
  exact @Module.Finite.equiv _ _ _ _ _ _ _ _ this i₂.symm.toLinearEquiv

lemma finite_sections_of_le_frame (X : Scheme.{u}) (E : X.Modules)
    (q : E.LocalGeneratorsData) [q.IsLocallyFreeData] [q.IsFiniteType]
    (i : q.I) (V : X.Opens) (hV : V ≤ q.X i) : Module.Finite Γ(X,V) Γ(E,V) := by
  have := SheafOfModules.LocalGeneratorsData.IsFiniteType.isFiniteType (p := q) i
  have := SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.isIso (q := q) i
  let a : Over (q.X i) := Over.mk (homOfLE hV)
  let F := SheafOfModules.evaluation (X.ringCatSheaf.over (q.X i)) (op a)
  have := finite_free_evaluation (X.ringCatSheaf.over (q.X i)) (q.generators i).I (op a)
  change Module.Finite ((X.ringCatSheaf.over (q.X i)).obj.obj (op a))
    (F.obj (E.over (q.X i)))
  exact Module.Finite.equiv
    (R := ↑((X.ringCatSheaf.over (q.X i)).obj.obj (op a)))
    (F.mapIso (asIso (q.generators i).π)).toLinearEquiv

theorem finite_affine_sections (R : CommRingCat.{u}) (E : (Spec R).Modules)
    (hE : ∃ q : E.LocalGeneratorsData, q.IsLocallyFreeData ∧ q.IsFiniteType) :
    Module.Finite R (moduleSpecΓFunctor.obj E) := by
  classical
  obtain ⟨q, hq, ht⟩ := hE
  let := hq
  let := ht
  let := q.isLocallyFree
  have : E.IsQuasicoherent := q.quasiCoherentData.isQuasicoherent
  let T : Set R := {r | ∃ i, PrimeSpectrum.basicOpen r ≤ q.X i}
  have hT : Ideal.span T = ⊤ := by
    have he : Set.range (fun r : T ↦ (r : R)) = T := by ext r; simp
    rw [← he, ← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
    apply top_unique
    intro x hx
    have hcov := (Opens.coversTop_iff _ _).mp q.coversTop
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, q.X i from by rw [hcov]; trivial)
    obtain ⟨V, ⟨r, rfl⟩, hxV, hV⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hi (q.X i).isOpen
    exact Opens.mem_iSup.mpr ⟨⟨r, i, hV⟩, hxV⟩
  let M := (modulesSpecToSheaf.obj E)
  let D (r : R) : (Spec R).Opens := PrimeSpectrum.basicOpen r
  have : IsIso E.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent E
  let f (r : T) : moduleSpecΓFunctor.obj E →ₗ[R] Γ(E, D r.val) :=
    (M.obj.map (show (Spec R).Opens from PrimeSpectrum.basicOpen r.val).leTop.op).hom
  have (r : T) : IsLocalizedModule.Away r.val (f r) :=
    (isIso_fromTildeΓ_iff_isLocalizing E).mp inferInstance r.val
  exact Module.Finite.of_localizationSpan' T hT
    (Rₚ := fun r ↦ Γ(Spec R, D r.val)) f (fun r ↦ by
      obtain ⟨i, hi⟩ := r.property
      exact finite_sections_of_le_frame (Spec R) E q i _ hi)

lemma finite_restriction_sections (X Y : Scheme.{u}) (E : Y.Modules)
    (f : X ⟶ Y) [IsOpenImmersion f] (U : X.Opens)
    [Module.Finite Γ(Y, f ''ᵁ U) Γ(E, f ''ᵁ U)] :
    Module.Finite Γ(X,U) Γ(E.restrict f,U) := by
  let g : Γ(E, f ''ᵁ U) →ₛₗ[(f.appIso U).hom.hom] Γ(E.restrict f,U) := {
    toFun := (E.restrictAppIso f U).inv
    map_add' := map_add _
    map_smul' := fun r m ↦ by
      exact Scheme.Modules.smul_restrictAppIso_inv_apply f E U r m
  }
  exact Module.Finite.of_surjective g (ConcreteCategory.bijective_of_isIso
    (E.restrictAppIso f U).inv).surjective

theorem finite_affine_restriction (R : CommRingCat.{u}) (X : Scheme.{u})
    (E : X.Modules)
    (hE : ∃ q : E.LocalGeneratorsData, q.IsLocallyFreeData ∧ q.IsFiniteType)
    (f : Spec R ⟶ X) [IsOpenImmersion f] :
    Module.Finite R (moduleSpecΓFunctor.obj (E.restrict f)) := by
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
  exact Module.Finite.of_localizationSpan' T hT
    (Rₚ := fun r ↦ Γ(Spec R, D r.val)) res (fun r ↦ by
      obtain ⟨i, hi⟩ := r.property
      have := finite_sections_of_le_frame X E q i _ hi
      exact finite_restriction_sections (Spec R) X E f _)

lemma finite_affine_image (R : CommRingCat.{u}) (X : Scheme.{u})
    (E : X.Modules)
    (hE : ∃ q : E.LocalGeneratorsData, q.IsLocallyFreeData ∧ q.IsFiniteType)
    (f : Spec R ⟶ X) [IsOpenImmersion f] :
    Module.Finite Γ(X,f ''ᵁ ⊤) Γ(E, f ''ᵁ ⊤) := by
  have := finite_affine_restriction R X E hE f
  let σ : R →+* Γ(X, f ''ᵁ ⊤) :=
    (f.appIso ⊤).inv.hom.comp (Scheme.ΓSpecIso R).inv.hom
  let m : moduleSpecΓFunctor.obj (E.restrict f) →ₛₗ[σ] Γ(E,f ''ᵁ ⊤) := {
    toFun := (E.restrictAppIso f ⊤).hom
    map_add' := map_add _
    map_smul' := fun r m ↦ by
      exact Scheme.Modules.smul_restrictAppIso_hom_apply f E ⊤
        ((Scheme.ΓSpecIso R).inv r) m
  }
  exact Module.Finite.of_surjective m (ConcreteCategory.bijective_of_isIso
    (E.restrictAppIso f ⊤).hom).surjective

lemma finite_affine_open (X : Scheme.{u}) (E : X.Modules)
    (hE : ∃ q : E.LocalGeneratorsData, q.IsLocallyFreeData ∧ q.IsFiniteType)
    (U : X.Opens) (hU : IsAffineOpen U) : Module.Finite Γ(X,U) Γ(E,U) := by
  have h := finite_affine_image Γ(X,U) X E hE hU.fromSpec
  rw [hU.fromSpec.image_top_eq_opensRange, hU.opensRange_fromSpec] at h
  exact h

end

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
universe u
lemma affine_image_restriction_spans (R : CommRingCat.{u}) (X : Scheme.{u})
    (E : X.Modules) [E.IsQuasicoherent] (f : Spec R ⟶ X)
    [IsOpenImmersion f] (r : R)
    (hle : f ''ᵁ (PrimeSpectrum.basicOpen r) ≤ f ''ᵁ ⊤) :
    Submodule.span Γ(X, f ''ᵁ (PrimeSpectrum.basicOpen r))
      (Set.range (E.presheaf.map (homOfLE hle).op)) = ⊤ := by
  let E' := E.restrict f
  let M := modulesSpecToSheaf.obj E'
  let D : (Spec R).Opens := PrimeSpectrum.basicOpen r
  let res : moduleSpecΓFunctor.obj E' →ₗ[R] Γ(E',D) :=
    (M.obj.map D.leTop.op).hom
  have : IsLocalizedModule.Away r res :=
    (isIso_fromTildeΓ_iff_isLocalizing E').mp inferInstance r
  have hspan : Submodule.span Γ(Spec R,D) (Set.range res) = ⊤ := by
    simpa only [Set.image_univ] using
      (span_eq_top_of_isLocalizedModule Γ(Spec R,D) (.powers r) res
        (v := Set.univ) (by simp))
  let V := f ''ᵁ D
  let B : Submodule Γ(X,V) Γ(E,V) := Submodule.span Γ(X,V)
    (Set.range (E.presheaf.map (homOfLE (f.image_mono D.leTop.le)).op))
  have hB : ∀ x : Γ(E',D), (E.restrictAppIso f D).hom x ∈ B := by
    intro x
    have hx : x ∈ Submodule.span Γ(Spec R,D) (Set.range res) := by rw [hspan]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨y, rfl⟩ := hx
        apply Submodule.subset_span
        refine ⟨(E.restrictAppIso f ⊤).hom y, ?_⟩
        exact (Scheme.Modules.map_restrictAppIso_hom_apply f E D.leTop.op y).symm
    | zero => simp
    | add x y hx hy ihx ihy => simpa using B.add_mem ihx ihy
    | smul a x hx ih =>
        rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
        exact B.smul_mem _ ih
  apply top_unique
  intro x hx
  obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (E.restrictAppIso f D).hom).surjective x
  exact hB y

theorem affine_restriction_spans (X : Scheme.{u}) (E : X.Modules)
    [E.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U) (s : Γ(X,U)) :
    Submodule.span Γ(X,X.basicOpen s)
      (Set.range (E.presheaf.map (homOfLE (X.basicOpen_le s)).op)) = ⊤ := by
  have h := affine_image_restriction_spans Γ(X,U) X E hU.fromSpec s
  rw [hU.fromSpec_image_basicOpen, hU.fromSpec.image_top_eq_opensRange,
    hU.opensRange_fromSpec] at h
  exact h _
end CampanaPeternellSix.RelativeCech

end

end OAI
