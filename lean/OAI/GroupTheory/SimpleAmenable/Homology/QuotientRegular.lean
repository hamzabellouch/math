import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.FullGroupStability

namespace OAI

section

section

open Classical CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
open SimpleAmenable
namespace QuotientRegular

attribute [local instance 1200] Rep.hV2
variable {G Q : Type} [Group G] [Group Q] (f : G →* Q)

noncomputable abbrev regular : Rep ℤ G :=
  Rep.res f (Rep.of (Representation.leftRegular ℤ Q))

noncomputable def point : Rep.trivial ℤ f.ker ℤ ⟶ Rep.res f.ker.subtype (regular f) :=
  Rep.ofHom ⟨(MonoidAlgebra.coeffLinearEquiv ℤ).symm.toLinearMap.comp (Finsupp.lsingle (1:Q)),by
    intro g
    apply LinearMap.ext
    intro z
    change MonoidAlgebra.single (1:Q) z=Representation.leftRegular ℤ Q (f g.val) (MonoidAlgebra.single (1:Q) z)
    rw [g.property]
    simp⟩

noncomputable def kernelEquivStabilizer :
    letI : MulAction G Q := MulAction.compHom Q f
    f.ker ≃* MulAction.stabilizer G (1:Q) := by
  letI : MulAction G Q := MulAction.compHom Q f
  exact MulEquiv.subgroupCongr (by
    ext g
    change f g=1 ↔ f g*1=1
    simp)

noncomputable def permutationIso :
    letI : MulAction G Q := MulAction.compHom Q f
    regular f ≅ Rep.of (TransitiveInduction.permutationRep (G:=G) (X:=Q)) := by
  letI : MulAction G Q := MulAction.compHom Q f
  refine Rep.mkIso (.mk (MonoidAlgebra.coeffLinearEquiv ℤ) ?_)
  intro g
  apply MonoidAlgebra.lhom_ext'
  intro x
  apply LinearMap.ext
  intro z
  simp [TransitiveInduction.permutationRep]
  rfl

lemma isIso_point (hf : Function.Surjective f) (n : ℕ) :
    IsIso (groupHomology.map f.ker.subtype (point f) n) := by
  let : MulAction G Q := MulAction.compHom Q f
  have ht : ∀q:Q,∃g:G,g • (1:Q)=q := by
    intro q
    obtain ⟨g,rfl⟩ := hf q
    exact ⟨g,mul_one _⟩
  have he : groupHomology.map f.ker.subtype (point f) n ≫
      groupHomology.map (MonoidHom.id G) (permutationIso f).hom n =
      TrivialHomology.map (kernelEquivStabilizer f).toMonoidHom n ≫
      groupHomology.map (MulAction.stabilizer G (1:Q)).subtype
        (TransitiveInduction.pointMap (1:Q)) n := by
    rw [← groupHomology.map_comp, ← groupHomology.map_comp]
    apply groupHomology.map_congr
    · ext g; rfl
    · apply LinearMap.ext; intro z; simp [point,permutationIso,TransitiveInduction.pointMap,TransitiveInduction.trivialMap]
  have := TrivialHomology.isIso_equiv (kernelEquivStabilizer f) n
  have := TransitiveInduction.isIso_map_pointMap (G:=G) (1:Q) ht n
  have : IsIso (groupHomology.map f.ker.subtype (point f) n ≫
      groupHomology.map (B:=Rep.of (TransitiveInduction.permutationRep (G:=G) (X:=Q)))
        (MonoidHom.id G) (permutationIso f).hom n) := by
    rw [he]
    infer_instance
  have : IsIso (groupHomology.map
      (B:=Rep.of (TransitiveInduction.permutationRep (G:=G) (X:=Q)))
      (MonoidHom.id G) (permutationIso f).hom n) :=
    inferInstanceAs (IsIso ((groupHomology.functor ℤ G n).mapIso (permutationIso f)).hom)
  exact IsIso.of_isIso_comp_right _
    (groupHomology.map (B:=Rep.of (TransitiveInduction.permutationRep (G:=G) (X:=Q)))
      (MonoidHom.id G) (permutationIso f).hom n)

noncomputable def right (q : Q) : regular f ⟶ regular f :=
  Rep.ofHom ⟨MonoidAlgebra.mapDomainLinearMap ℤ ℤ (·*q),by
    intro g
    apply MonoidAlgebra.lhom_ext'
    intro x
    apply LinearMap.ext
    intro z
    simp [Representation.leftRegular, mul_assoc]⟩

@[simp] lemma right_single (q x : Q) (z : ℤ) :
    (right f q).hom (MonoidAlgebra.single x z)=MonoidAlgebra.single (x*q) z := by
  simp [right]

noncomputable def conjugate (g : G) : f.ker ≃* f.ker :=
  (MulAut.conjNormal g : f.ker ≃* f.ker)

lemma right_homology_identity (hf : Function.Surjective f) (n : ℕ)
    (hact : ∀g:G,TrivialHomology.map (conjugate f g).toMonoidHom n=𝟙 _) (q : Q) :
    (groupHomology.functor ℤ G n).map (right f q)=𝟙 _ := by
  obtain ⟨g,rfl⟩ := hf q
  have := isIso_point f hf n
  apply (cancel_epi (groupHomology.map f.ker.subtype (point f) n)).mp
  change _ = groupHomology.map f.ker.subtype (point f) n ≫ 𝟙 (groupHomology (regular f) n)
  rw [Category.comp_id]
  have hc := HomologyConjugation.map_after_conjugation f.ker.subtype (point f) g n
  have he :
      groupHomology.map ((MulAut.conj g).toMonoidHom.comp f.ker.subtype)
        (point f ≫ (Rep.resFunctor f.ker.subtype).map
          (HomologyConjugation.conjugationCoeff g (regular f))) n =
      TrivialHomology.map (conjugate f g).toMonoidHom n ≫
        groupHomology.map f.ker.subtype (point f) n ≫
        (groupHomology.functor ℤ G n).map (right f (f g)) := by
    dsimp only [groupHomology.functor]
    rw [← groupHomology.map_comp, ← groupHomology.map_comp]
    apply groupHomology.map_congr
    · ext h; rfl
    · apply LinearMap.ext
      intro z
      simp [point,right,TransitiveInduction.trivialMap,
        HomologyConjugation.conjugationCoeff,regular,Representation.ofMulAction_def]
  rw [he,hact,Category.id_comp] at hc
  exact hc

lemma H1_isZero (hf : Function.Surjective f)
    (hz : IsZero (groupHomology (Rep.trivial ℤ f.ker ℤ) 1)) :
    IsZero (groupHomology (regular f) 1) := by
  have := isIso_point f hf 1
  exact hz.of_iso (asIso (groupHomology.map f.ker.subtype (point f) 1)).symm

lemma H2_finite_of_regular (hf : Function.Surjective f)
    [Module.Finite ℤ (groupHomology (regular f) 2)] :
    Module.Finite ℤ (groupHomology (Rep.trivial ℤ f.ker ℤ) 2) := by
  have := isIso_point f hf 2
  exact Module.Finite.of_injective (groupHomology.map f.ker.subtype (point f) 2).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)

end QuotientRegular

end

section

open Classical CategoryTheory CategoryTheory.Limits Representation Finsupp
namespace FiniteFreeRep

attribute [local instance 1200] Rep.hV2
variable {k Q : Type} [CommRing k] [Group Q]

noncomputable def incl (A : Rep.{0} k Q) {n : ℕ} (i : Fin n) : A ⟶ Rep.finsupp (Fin n) A :=
  Rep.ofHom ⟨Finsupp.lsingle i,by
    intro g
    apply LinearMap.ext
    intro x
    simp⟩

noncomputable def proj (A : Rep.{0} k Q) {n : ℕ} (i : Fin n) : Rep.finsupp (Fin n) A ⟶ A :=
  Rep.ofHom ⟨Finsupp.lapply i,by
    intro g
    apply Finsupp.lhom_ext
    intro j x
    by_cases h : i=j
    · subst j; simp
    · simp [h]⟩

lemma sum_proj_incl (A : Rep.{0} k Q) (n : ℕ) :
    ∑ i:Fin n,proj A i ≫ incl A i=𝟙 (Rep.finsupp (Fin n) A) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply Finsupp.lhom_ext
  intro i x
  simp [Rep.sum_hom, incl,proj,Representation.IntertwiningMap.sum_apply]

lemma functor_isZero (F : Rep.{0} k Q ⥤ ModuleCat k) [F.Additive]
    (A : Rep.{0} k Q) (h : IsZero (F.obj A)) (n : ℕ) : IsZero (F.obj (Rep.finsupp (Fin n) A)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  rw [← F.map_id, ← sum_proj_incl,F.map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [F.map_comp,h.eq_zero_of_tgt (F.map (proj A i)),zero_comp]

lemma functor_finite [IsNoetherianRing k] (F : Rep.{0} k Q ⥤ ModuleCat k) [F.Additive]
    (A : Rep.{0} k Q) [Module.Finite k (F.obj A)] (n : ℕ) :
    Module.Finite k (F.obj (Rep.finsupp (Fin n) A)) := by
  let φ : F.obj (Rep.finsupp (Fin n) A) →ₗ[k] (Fin n → F.obj A) :=
    LinearMap.pi (fun i => (F.map (proj A i)).hom)
  apply Module.Finite.of_injective φ
  apply (LinearMap.ker_eq_bot).mp
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hp : ∀i:Fin n,(F.map (proj A i)).hom x=0 := fun i => congrFun hx i
  have he : ∑ i:Fin n,(F.map (proj A i) ≫ F.map (incl A i))=𝟙 _ := by
    simp only [← F.map_comp, ← F.map_sum,sum_proj_incl,F.map_id]
  have ht := congrArg (fun t => t.hom x) he
  simpa [hp] using ht.symm

instance finite_free (n : ℕ) :
    Module.Finite (MonoidAlgebra k Q) (Rep.free k Q (Fin n)).ρ.asModule :=
  Module.Finite.of_basis (Representation.freeAsModuleBasis k Q (Fin n))

lemma exists_cover (A : Rep.{0} k Q)
    [Module.Finite (MonoidAlgebra k Q) A.ρ.asModule] :
    ∃n:ℕ,∃e:Rep.free k Q (Fin n) ⟶ A,Epi e := by
  obtain ⟨n,φ,hφ⟩ := Module.Finite.exists_fin' (MonoidAlgebra k Q) A.ρ.asModule
  let ψ : (Rep.free k Q (Fin n)).ρ.asModule →ₗ[MonoidAlgebra k Q] A.ρ.asModule :=
    φ.comp ((Finsupp.linearEquivFunOnFinite (MonoidAlgebra k Q) (MonoidAlgebra k Q) (Fin n)).toLinearMap.comp
      (Representation.finsuppLEquivFreeAsModule k Q (Fin n)).symm.toLinearMap)
  have hψ : Function.Surjective ψ := hφ.comp
    ((Finsupp.linearEquivFunOnFinite (MonoidAlgebra k Q) (MonoidAlgebra k Q) (Fin n)).surjective.comp
      (Representation.finsuppLEquivFreeAsModule k Q (Fin n)).symm.surjective)
  let p : Rep.toModuleMonoidAlgebra.obj (Rep.free k Q (Fin n)) ⟶ Rep.toModuleMonoidAlgebra.obj A :=
    ModuleCat.ofHom ψ
  have : Epi p := (ModuleCat.epi_iff_surjective _).mpr hψ
  let e : Rep.free k Q (Fin n) ⟶ A :=
    (Rep.unitIso _).hom ≫ Rep.ofModuleMonoidAlgebra.map p ≫ (Rep.unitIso _).inv
  exact ⟨n,e,by dsimp only [e]; infer_instance⟩

lemma finite_kernel {A B : Rep.{0} k Q} (d : A ⟶ B)
    [IsNoetherianRing (MonoidAlgebra k Q)]
    [Module.Finite (MonoidAlgebra k Q) A.ρ.asModule] :
    Module.Finite (MonoidAlgebra k Q) (kernel d).ρ.asModule := by
  have : Module.Finite (MonoidAlgebra k Q) (Rep.toModuleMonoidAlgebra.obj A) :=
    ‹Module.Finite (MonoidAlgebra k Q) A.ρ.asModule›
  let p := Rep.toModuleMonoidAlgebra.map (kernel.ι d)
  have : Mono p := inferInstanceAs (Mono (Rep.toModuleMonoidAlgebra.map (kernel.ι d)))
  exact Module.Finite.of_injective p.hom ((ModuleCat.mono_iff_injective _).mp inferInstance)

end FiniteFreeRep

end

end

end OAI
