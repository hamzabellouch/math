import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.AlternatingH2
import OAI.GroupTheory.SimpleAmenable.Homology.QuotientRegular

namespace OAI

section

section

open Classical CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
open SimpleAmenable
namespace QuotientRegular

attribute [local instance 1200] Rep.hV2
variable {G Q : Type} [Group G] [Group Q]

noncomputable def augment : Rep.leftRegular ℤ Q ⟶ Rep.trivial ℤ Q ℤ :=
  Rep.ofHom ⟨(MonoidAlgebra.lift ℤ ℤ Q (1:Q →* ℤ)).toLinearMap,by
    intro g
    apply MonoidAlgebra.lhom_ext'
    intro q
    apply LinearMap.ext
    intro z
    simp⟩

@[simp] lemma augment_single (q:Q) (z:ℤ) :
    (augment (Q:=Q)).hom (MonoidAlgebra.single q z)=z := by
  simp [augment,MonoidAlgebra.lift_single]

instance augment_epi : Epi (augment (Q:=Q)) := by
  apply ConcreteCategory.epi_of_surjective
  intro z
  exact ⟨MonoidAlgebra.single 1 z,augment_single 1 z⟩

lemma regular_ext {A : Rep ℤ Q} (t u : Rep.leftRegular ℤ Q ⟶ A)
    (h : t.hom (MonoidAlgebra.single 1 1)=u.hom (MonoidAlgebra.single 1 1)) : t=u := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro q
  apply LinearMap.ext
  intro z
  have ht := congrArg (fun T => T (MonoidAlgebra.single 1 1)) (t.hom.isIntertwining' q)
  have hu := congrArg (fun T => T (MonoidAlgebra.single 1 1)) (u.hom.isIntertwining' q)
  have hv : t.hom (MonoidAlgebra.single q 1)=u.hom (MonoidAlgebra.single q 1) := by
    change t.hom ((Rep.leftRegular ℤ Q).ρ q (MonoidAlgebra.single 1 1)) = A.ρ q (t.hom (MonoidAlgebra.single 1 1)) at ht
    change u.hom ((Rep.leftRegular ℤ Q).ρ q (MonoidAlgebra.single 1 1)) = A.ρ q (u.hom (MonoidAlgebra.single 1 1)) at hu
    rw [h] at ht
    simpa using ht.trans hu.symm
  change t.hom (MonoidAlgebra.single q z)=u.hom (MonoidAlgebra.single q z)
  have he : MonoidAlgebra.single q z = z • (MonoidAlgebra.single q 1 : MonoidAlgebra ℤ Q) := by simp
  rw [he]
  change t.hom.toLinearMap _ = u.hom.toLinearMap _
  rw [LinearMap.map_smul,LinearMap.map_smul]
  exact congrArg _ hv

lemma regular_sum_right (t : Rep.leftRegular ℤ Q ⟶ Rep.leftRegular ℤ Q) :
    t = ∑q∈(t.hom (MonoidAlgebra.single 1 1)).coeff.support,
      (t.hom (MonoidAlgebra.single 1 1)).coeff q • right (MonoidHom.id Q) q := by
  apply regular_ext
  simp only [Rep.sum_hom,Rep.zsmul_hom,Representation.IntertwiningMap.sum_apply,
    Representation.IntertwiningMap.smul_apply]
  change _ = ∑q∈(t.hom (MonoidAlgebra.single 1 1)).coeff.support,
    (t.hom (MonoidAlgebra.single 1 1)).coeff q •
      (right (MonoidHom.id Q) q).hom (MonoidAlgebra.single 1 1)
  have hr (q:Q) : (right (MonoidHom.id Q) q).hom (MonoidAlgebra.single 1 1)=
      MonoidAlgebra.single q 1 := by simpa using right_single (MonoidHom.id Q) q 1 1
  simp only [hr,MonoidAlgebra.smul_single,smul_eq_mul,mul_one]
  simpa only [Finsupp.sum] using
    (MonoidAlgebra.sum_coeff_single (t.hom (MonoidAlgebra.single 1 1))).symm

lemma map_regular_zero (f : G →* Q) (hf : Function.Surjective f) (n : ℕ)
    (hact : ∀g:G,TrivialHomology.map (conjugate f g).toMonoidHom n=𝟙 _)
    (t : Rep.leftRegular ℤ Q ⟶ Rep.leftRegular ℤ Q) (ht : t ≫ augment=0) :
    (groupHomology.functor ℤ G n).map ((Rep.resFunctor f).map t)=0 := by
  let F := Rep.resFunctor f ⋙ groupHomology.functor ℤ G n
  have ha : ∑q∈(t.hom (MonoidAlgebra.single 1 1)).coeff.support,
      (t.hom (MonoidAlgebra.single 1 1)).coeff q=0 := by
    have hh := congrArg (fun s => s.hom (MonoidAlgebra.single 1 1)) ht
    simpa [augment,MonoidAlgebra.lift_apply,Finsupp.sum] using hh
  change F.map t=0
  rw [regular_sum_right t,F.map_sum]
  simp_rw [F.map_zsmul]
  have hr : ∀q:Q,F.map (right (MonoidHom.id Q) q)=𝟙 _ := fun q =>
    right_homology_identity f hf n hact q
  simp_rw [hr]
  rw [← Finset.sum_smul,ha,zero_smul]

lemma map_free_zero (f : G →* Q) (hf : Function.Surjective f) (n : ℕ)
    (hact : ∀g:G,TrivialHomology.map (conjugate f g).toMonoidHom n=𝟙 _)
    (k : ℕ) (t : Rep.free ℤ Q (Fin k) ⟶ Rep.leftRegular ℤ Q) (ht : t ≫ augment=0) :
    (groupHomology.functor ℤ G n).map ((Rep.resFunctor f).map t)=0 := by
  let F := Rep.resFunctor f ⋙ groupHomology.functor ℤ G n
  have hi : ∀i:Fin k,F.map (FiniteFreeRep.incl (Rep.leftRegular ℤ Q) i ≫ t)=0 := by
    intro i
    exact map_regular_zero f hf n hact _ (by rw [Category.assoc,ht,comp_zero])
  change F.map t=0
  rw [← Category.id_comp t,← FiniteFreeRep.sum_proj_incl (Rep.leftRegular ℤ Q) k,
    Preadditive.sum_comp,F.map_sum]
  apply Finset.sum_eq_zero
  intro i hi'
  rw [Category.assoc,F.map_comp,hi,comp_zero]

end QuotientRegular

end

section

open Classical CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
open SimpleAmenable
namespace QuotientRegular

attribute [local instance 1200] Rep.hV2
variable {G Q : Type} [Group G] [Group Q]

instance finite_regular_module :
    Module.Finite (MonoidAlgebra ℤ Q) (Rep.leftRegular ℤ Q).ρ.asModule := by
  let p : Rep.free ℤ Q (Fin 1) ⟶ Rep.leftRegular ℤ Q := FiniteFreeRep.proj (Rep.leftRegular ℤ Q) (n:=1) 0
  have : Epi p := ConcreteCategory.epi_of_surjective p (by
    intro x
    exact ⟨Finsupp.single 0 x,by simp [p,FiniteFreeRep.proj]⟩)
  let q := Rep.toModuleMonoidAlgebra.map p
  have : Epi q := inferInstanceAs (Epi (Rep.toModuleMonoidAlgebra.map p))
  have : Module.Finite (MonoidAlgebra ℤ Q)
      (Rep.toModuleMonoidAlgebra.obj (Rep.free ℤ Q (Fin 1))) :=
    inferInstanceAs (Module.Finite (MonoidAlgebra ℤ Q) (Rep.free ℤ Q (Fin 1)).ρ.asModule)
  exact Module.Finite.of_surjective q.hom ((ModuleCat.epi_iff_surjective _).mp inferInstance)

lemma H0_finite (f : G →* Q) (hf : Function.Surjective f) :
    Module.Finite ℤ (groupHomology (regular f) 0) := by
  have : Module.Finite ℤ (groupHomology (Rep.trivial ℤ f.ker ℤ) 0) :=
    Module.Finite.of_surjective
      (groupHomology.H0IsoOfIsTrivial (Rep.trivial ℤ f.ker ℤ)).inv.hom
      (groupHomology.H0IsoOfIsTrivial (Rep.trivial ℤ f.ker ℤ)).toLinearEquiv.symm.surjective
  have := isIso_point f hf 0
  exact Module.Finite.of_surjective (groupHomology.map f.ker.subtype (point f) 0).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

lemma finite_kernel_H2 (f : G →* Q) (hf : Function.Surjective f)
    [IsNoetherianRing (MonoidAlgebra ℤ Q)]
    [Module.Finite ℤ (groupHomology (Rep.trivial ℤ G ℤ) 2)]
    (hz : IsZero (groupHomology (Rep.trivial ℤ f.ker ℤ) 1))
    (hact : ∀g:G,TrivialHomology.map (conjugate f g).toMonoidHom 2=𝟙 _) :
    Module.Finite ℤ (groupHomology (Rep.trivial ℤ f.ker ℤ) 2) := by
  let ε := augment (Q:=Q)
  have : Module.Finite (MonoidAlgebra ℤ Q) (kernel ε).ρ.asModule :=
    FiniteFreeRep.finite_kernel ε
  obtain ⟨n₂,e₂,he₂⟩ := FiniteFreeRep.exists_cover (kernel ε)
  let := he₂
  have : Module.Finite (MonoidAlgebra ℤ Q) (kernel e₂).ρ.asModule :=
    FiniteFreeRep.finite_kernel e₂
  obtain ⟨n₃,e₃,he₃⟩ := FiniteFreeRep.exists_cover (kernel e₂)
  let := he₃
  have : Module.Finite (MonoidAlgebra ℤ Q) (kernel e₃).ρ.asModule :=
    FiniteFreeRep.finite_kernel e₃
  obtain ⟨n₄,e₄,he₄⟩ := FiniteFreeRep.exists_cover (kernel e₃)
  let := he₄
  let T : Rep.{0} ℤ Q ⥤ Rep.{0} ℤ G := Rep.resFunctor f
  let F₀ := T ⋙ groupHomology.functor ℤ G 0
  let F₁ := T ⋙ groupHomology.functor ℤ G 1
  have : Module.Finite ℤ (F₀.obj (Rep.leftRegular ℤ Q)) := H0_finite f hf
  have : Module.Finite ℤ (groupHomology (T.obj (Rep.free ℤ Q (Fin n₄))) 0) :=
    FiniteFreeRep.functor_finite F₀ (Rep.leftRegular ℤ Q) n₄
  have hz₃ : IsZero (groupHomology (T.obj (Rep.free ℤ Q (Fin n₃))) 1) :=
    FiniteFreeRep.functor_isZero F₁ (Rep.leftRegular ℤ Q) (H1_isZero f hf hz) n₃
  have hd : BoundedHomologyEdge.Hmap 2 (T.map e₂ ≫ T.map (kernel.ι ε))=0 := by
    rw [← T.map_comp]
    exact map_free_zero f hf 2 hact n₂ (e₂ ≫ kernel.ι ε)
      (by rw [Category.assoc,kernel.condition,comp_zero])
  let e₀ : Rep.trivial ℤ G ℤ ≅ T.obj (Rep.trivial ℤ Q ℤ) :=
    Rep.mkIso (.mk (LinearEquiv.refl ℤ ℤ) (by intro g; rfl))
  let eH := (groupHomology.functor ℤ G 2).mapIso e₀
  have : Module.Finite ℤ ((groupHomology.functor ℤ G 2).obj (Rep.trivial ℤ G ℤ)) :=
    inferInstanceAs (Module.Finite ℤ (groupHomology (Rep.trivial ℤ G ℤ) 2))
  have : Module.Finite ℤ (groupHomology (T.obj (Rep.trivial ℤ Q ℤ)) 2) :=
    Module.Finite.of_surjective eH.hom.hom eH.toLinearEquiv.surjective
  have : Epi (T.map e₄) := (Rep.epi_iff_surjective _).mpr
    ((Rep.epi_iff_surjective e₄).mp he₄)
  have : Module.Finite ℤ (groupHomology (regular f) 2) :=
    FiniteHomologyReturn.finite_H2
      ((Rep.shortExact_res f).mpr (BoundedHomologyEdge.kernel_shortExact ε))
      ((Rep.shortExact_res f).mpr (BoundedHomologyEdge.kernel_shortExact e₂))
      ((Rep.shortExact_res f).mpr (BoundedHomologyEdge.kernel_shortExact e₃))
      (T.map e₄) hz₃ hd
  exact H2_finite_of_regular f hf

end QuotientRegular

end

end

end OAI
