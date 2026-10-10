import OAI.Algebra.AuslanderReiten.HomComplex.HomKunnethClass

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} A} {Y : ModuleCat.{u} B}
variable (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)
variable (i j n : ℕ) (h : i+j=n)
variable (f : P.complex.X i →ₗ[A] U) (g : Q.complex.X j →ₗ[B] V)
variable (hf : f.comp (P.complex.d (i+1) i).hom=0) (hg : g.comp (Q.complex.d (j+1) j).hom=0)

include hf hg in

theorem extKunnethEquiv_elementary :
    extKunnethEquiv k A B P Q U V n
      ((projectiveResolution k A B P Q).extMk
        (ModuleCat.ofHom (X := (complex k A B P.complex Q.complex).X n)
          (Y := moduleObject k A B U V)
          (elementaryHom k A B P.complex Q.complex U V i j n h f g)) (n+1) rfl
        (ModuleCat.hom_ext (elementary_closed k A B P.complex Q.complex U V i j n h f g hf hg))) =
      (Pi.single ⟨(i,j),h⟩
        (P.extMk (ModuleCat.ofHom f) (i+1) rfl (ModuleCat.hom_ext hf) ⊗ₜ[k]
          Q.extMk (ModuleCat.ofHom g) (j+1) rfl (ModuleCat.hom_ext hg)) :
          ∀ p : Diagonal n, Ext X U p.val.1 ⊗[k] Ext Y V p.val.2) := by
  let e := elementaryHom k A B P.complex Q.complex U V i j n h f g
  have he := elementary_closed k A B P.complex Q.complex U V i j n h f g hf hg
  let z := (⟨e,homCochain_mem_cycles k (A ⊗[k] B) (projectiveResolution k A B P Q)
    (moduleObject k A B U V) n e he⟩ :
    LinearMap.ker ((homCochain k (A ⊗[k] B) (complex k A B P.complex Q.complex)
      (moduleObject k A B U V)).d n (n+1)).hom)
  let xf := (⟨f,homCochain_mem_cycles k A P U i f hf⟩ :
    LinearMap.ker ((homCochain k A P.complex U).d i (i+1)).hom)
  let xg := (⟨g,homCochain_mem_cycles k B Q V j g hg⟩ :
    LinearMap.ker ((homCochain k B Q.complex V).d j (j+1)).hom)
  have hext := homCochainNativeExtEquiv_literal k (A ⊗[k] B)
    (projectiveResolution k A B P Q) (moduleObject k A B U V) n e he
  change extKunnethEquiv k A B P Q U V n
    ((projectiveResolution k A B P Q).extMk
      (ModuleCat.ofHom (X := (complex k A B P.complex Q.complex).X n)
        (Y := moduleObject k A B U V) e) (n+1) rfl (ModuleCat.hom_ext he)) = _
  refine (congrArg (extKunnethEquiv k A B P Q U V n) hext.symm).trans ?_
  unfold extKunnethEquiv
  erw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]
  have hk := homKunnethEquiv_elementary k A B P.complex Q.complex U V i j n h f g hf hg
    xf xg rfl rfl z rfl
  erw [hk]
  funext a
  by_cases ha : a=⟨(i,j),h⟩
  · subst a
    simp only [DFinsupp.linearEquivFunOnFintype_apply, DFinsupp.single_eq_same,
      LinearEquiv.piCongrRight_apply, Pi.single_eq_same, TensorProduct.congr_tmul]
    rw [homCochainExtEquiv_literal k A P U i f hf, homCochainExtEquiv_literal k B Q V j g hg]
  · simp only [DFinsupp.linearEquivFunOnFintype_apply, DFinsupp.single_eq_of_ne ha,
      LinearEquiv.piCongrRight_apply, Pi.single_eq_of_ne ha, map_zero]

end ArExplicit.ExternalTensor

end

end OAI
