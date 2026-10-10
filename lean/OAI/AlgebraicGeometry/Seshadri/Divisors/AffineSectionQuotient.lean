import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.SectionEuler

namespace OAI

section
noncomputable section
                                               
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames

variable {X : Scheme.{0}}

lemma global_sections_exact {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    Function.Exact (S.f.app ⊤) (S.g.app ⊤) := by
  let := hS.mono_f
  intro m
  constructor
  · intro hm
    let t : O X ⟶ S.X₂ := (FlasqueCohomology.globalHomEquiv X.ringCatSheaf S.X₂).symm m
    have ht : t ≫ S.g = 0 := by
      apply (FlasqueCohomology.globalHomEquiv X.ringCatSheaf S.X₃).injective
      change S.g.app ⊤ ((FlasqueCohomology.globalHomEquiv X.ringCatSheaf S.X₂) t) = 0
      exact (congrArg (S.g.app ⊤) (Equiv.apply_symm_apply _ m)).trans hm
    obtain ⟨u,hu⟩ := hS.exact.lift' t ht
    refine ⟨FlasqueCohomology.globalHomEquiv X.ringCatSheaf S.X₁ u, ?_⟩
    change FlasqueCohomology.globalHomEquiv X.ringCatSheaf S.X₂ (u ≫ S.f) = m
    exact (congrArg (FlasqueCohomology.globalHomEquiv X.ringCatSheaf S.X₂) hu).trans
      (Equiv.apply_symm_apply _ m)
  · rintro ⟨a,rfl⟩
    have h := congrArg (fun t : S.X₁ ⟶ S.X₃ => t.app ⊤ a) S.zero
    exact h

lemma affine_global_sections_surjective [IsAffine X] [IsNoetherian X]
    {S : ShortComplex X.Modules} (hS : S.ShortExact) [S.X₁.IsQuasicoherent] :
    Function.Surjective (S.g.app ⊤) := by
  intro m
  let t : O X ⟶ S.X₃ := (FlasqueCohomology.globalHomEquiv X.ringCatSheaf S.X₃).symm m
  have hz : (Ext.mk₀ t).comp hS.extClass (show 0+1=1 from rfl) = 0 :=
    AffineSchemeCohomology.affine_ext_zero X S.X₁ 0 _
  obtain ⟨z,hz⟩ := Ext.covariant_sequence_exact₃ (O X) hS (Ext.mk₀ t) rfl hz
  obtain ⟨u,rfl⟩ := (Ext.mk₀_bijective _ _).surjective z
  have hu : u ≫ S.g = t := by
    apply (Ext.mk₀_bijective _ _).injective
    rwa [Ext.mk₀_comp_mk₀] at hz
  refine ⟨FlasqueCohomology.globalHomEquiv X.ringCatSheaf S.X₂ u, ?_⟩
  change FlasqueCohomology.globalHomEquiv X.ringCatSheaf S.X₃ (u ≫ S.g) = m
  exact (congrArg (FlasqueCohomology.globalHomEquiv X.ringCatSheaf S.X₃) hu).trans
    (Equiv.apply_symm_apply _ m)

def frameCokernelMap {M : X.Modules} (e : M ≅ O X) (s : O X ⟶ M) :
    Γ(X,⊤) →ₗ[Γ(X,⊤)] Γ(cokernel s,⊤) where
  toFun r := (cokernel.π s).app ⊤ (e.inv.app ⊤ r)
  map_add' := by
    intro first second
    exact ((e.inv ≫ cokernel.π s).app ⊤).hom.map_add first second
  map_smul' := by
    intro scalar value
    exact (e.inv ≫ cokernel.π s).app_smul scalar value

lemma frameCokernelMap_ker [IsIntegral X] [IsNoetherian X]
    (L : LineBundle X) (e : L.sheaf ≅ O X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0) :
    LinearMap.ker (frameCokernelMap e s) = Ideal.span {coefficient e s} := by
  ext r
  rw [LinearMap.mem_ker]
  change (cokernel.π s).app ⊤ (e.inv.app ⊤ r) = 0 ↔ r ∈ Ideal.span {coefficient e s}
  rw [global_sections_exact (L.section_shortExact s hs), Ideal.mem_span_singleton]
  constructor
  · rintro ⟨a,ha⟩
    change Γ(X,⊤) at a
    refine ⟨a, ?_⟩
    have he := congrArg (fun m => e.hom.app ⊤ m) ha
    have scal : e.hom.app ⊤ (s.app ⊤ a) = a * coefficient e s := by
      have h := (s ≫ e.hom).app_smul (r := a) (x := (1 : Γ(X,⊤)))
      change e.hom.app ⊤ (s.app ⊤ (a * (1 : Γ(X,⊤)) : Γ(X,⊤))) = a * coefficient e s at h
      simpa only [mul_one] using h
    rw [scal] at he
    have hf : e.hom.app ⊤ (e.inv.app ⊤ r) = r := by
      have h := congrArg (fun t : O X ⟶ O X => t.app ⊤ r) e.inv_hom_id
      exact h
    rw [hf] at he
    exact he.symm.trans (mul_comm a (coefficient e s))
  · rintro ⟨a,ha⟩
    refine ⟨a, ?_⟩
    have hinj := (ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.toPresheaf X).mapIso e).app (Opposite.op ⊤)).hom).injective
    apply hinj
    change e.hom.app ⊤ (s.app ⊤ a) = e.hom.app ⊤ (e.inv.app ⊤ r)
    have h := (s ≫ e.hom).app_smul (r := a) (x := (1 : Γ(X,⊤)))
    change e.hom.app ⊤ (s.app ⊤ (a * (1 : Γ(X,⊤)) : Γ(X,⊤))) = a * coefficient e s at h
    rw [mul_one] at h
    rw [h]
    have hf := congrArg (fun t : O X ⟶ O X => t.app ⊤ r) e.inv_hom_id
    change e.hom.app ⊤ (e.inv.app ⊤ r) = r at hf
    rw [hf, ha, mul_comm]

lemma frameCokernelMap_surjective [IsIntegral X] [IsNoetherian X] [IsAffine X]
    (L : LineBundle X) (e : L.sheaf ≅ O X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0) :
    Function.Surjective (frameCokernelMap e s) := by
  let B : LineBundle X := ⟨O X, fun _ =>
    ⟨⊤,trivial,⟨Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι⟩⟩⟩
  let : (O X).IsQuasicoherent := B.quasicoherent
  have hp := affine_global_sections_surjective (L.section_shortExact s hs)
  have he := (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.toPresheaf X).mapIso e.symm).app (Opposite.op ⊤)).hom).surjective
  exact hp.comp he

def affine_section_quotient [IsIntegral X] [IsNoetherian X] [IsAffine X]
    (L : LineBundle X) (e : L.sheaf ≅ O X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0) :
    (Γ(X,⊤) ⧸ Ideal.span {coefficient e s}) ≃ₗ[Γ(X,⊤)] Γ(cokernel s,⊤) := by
  have he := (frameCokernelMap e s).quotKerEquivOfSurjective
    (frameCokernelMap_surjective L e s hs)
  rw [frameCokernelMap_ker L e s hs] at he
  exact he
end
end MaximalSeshadri.Geometry
end


end
end

end OAI
