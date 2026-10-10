import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.BarSegal
import OAI.GroupTheory.SimpleAmenable.Simplicial.TrajectoryFinite

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace BarFinitePower
open IntervalBar IntervalBar.Diagram FreeChains

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
noncomputable def singleRowComparison (p:ℕ) :
    bar (C:=Diagram C (Fin (p+1))) ⟶ (power (Fin p)).obj (bar (C:=C)) :=
  barMap (eval p) ≫ singlePowerComparison (Fin p)
lemma singleRowComparison_isIso (p n:ℕ) :
    IsIso (SSet.homologyMap (singleRowComparison (C:=C) p) Z n) := by
  rw [singleRowComparison,SSet.homologyMap_comp]
  have := barMap_homology_isIso (eval (C:=C) p) n
  have := singlePowerComparison_homology_isIso (C:=C) (Fin p) n
  infer_instance
noncomputable def doubleRowComparison (p:ℕ) :
    bar₂ (C:=Diagram C (Fin (p+1))) ⟶ (power (Fin p)).obj (bar₂ (C:=C)) :=
  bar₂Map (eval p) ≫ doublePowerComparison (Fin p)
lemma doubleRowComparison_isIso (p n:ℕ) :
    IsIso (SSet.homologyMap (doubleRowComparison (C:=C) p) Z n) := by
  rw [doubleRowComparison,SSet.homologyMap_comp]
  have := bar₂Map_homology_isIso (eval (C:=C) p) n
  have := doublePowerComparison_homology_isIso (C:=C) (Fin p) n
  infer_instance
lemma singleRow_finite (p n:ℕ)
    (h:∀i,i≤n → Module.Finite ℤ ((bar (C:=C)).homology Z i : A)) :
    Module.Finite ℤ ((bar (C:=Diagram C (Fin (p+1)))).homology Z n : A) := by
  have := finite_power (bar (C:=C)) (Fin p) n h
  have := singleRowComparison_isIso (C:=C) p n
  exact Module.Finite.equiv (asIso (SSet.homologyMap (singleRowComparison (C:=C) p) Z n)).symm.toLinearEquiv
lemma doubleRow_finite (p n:ℕ)
    (h:∀i,i≤n → Module.Finite ℤ ((bar₂ (C:=C)).homology Z i : A)) :
    Module.Finite ℤ ((bar₂ (C:=Diagram C (Fin (p+1)))).homology Z n : A) := by
  have := finite_power (bar₂ (C:=C)) (Fin p) n h
  have := doubleRowComparison_isIso (C:=C) p n
  exact Module.Finite.equiv (asIso (SSet.homologyMap (doubleRowComparison (C:=C) p) Z n)).symm.toLinearEquiv
noncomputable def firstRowHomologyIso (n:ℕ) :
    ((bar (C:=Diagram C (Fin 2))).homology Z n : A) ≅ (bar (C:=C)).homology Z n := by
  haveI := singleRowComparison_isIso (C:=C) 1 n
  exact asIso (SSet.homologyMap (singleRowComparison (C:=C) 1) Z n) ≪≫
    (SSet.homologyFunctor Z n).mapIso (powerOneIso (bar (C:=C)))
noncomputable def firstDoubleRowHomologyIso (n:ℕ) :
    ((bar₂ (C:=Diagram C (Fin 2))).homology Z n : A) ≅ (bar₂ (C:=C)).homology Z n := by
  haveI := doubleRowComparison_isIso (C:=C) 1 n
  exact asIso (SSet.homologyMap (doubleRowComparison (C:=C) 1) Z n) ≪≫
    (SSet.homologyFunctor Z n).mapIso (powerOneIso (bar₂ (C:=C)))
end BarFinitePower

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram
open FreeChains BarFinitePower SimplicialDiagonal

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
lemma bar₂_finite_reverse (r:ℕ)
    (hf:∀n,n≤r+1 → Module.Finite ℤ ((bar₂ (C:=C)).homology Z n : A)) :
    ∀q,q≤r → Module.Finite ℤ ((bar (C:=C)).homology Z q : A) := by
  have h := finite_reverse (rows₂ (C:=C)) r (fun _=>bar_connected _) zero_bar_acyclic
    (fun q _=>rows₂_segal_homology_isIso q) (fun q h p=>by
      apply singleRow_finite p q
      intro i hi
      have : Module.Finite ℤ ((bar (C:=Diagram C (Fin 2))).homology Z i:A) := h i hi
      exact Module.Finite.equiv (firstRowHomologyIso (C:=C) i).toLinearEquiv) hf
  intro q hq
  have : Module.Finite ℤ ((bar (C:=Diagram C (Fin 2))).homology Z q:A) := h q hq
  exact Module.Finite.equiv (firstRowHomologyIso (C:=C) q).toLinearEquiv
lemma bar₃_finite_reverse (r:ℕ)
    (hf:∀n,n≤r+1 → Module.Finite ℤ ((bar₃ (C:=C)).homology Z n : A)) :
    ∀q,q≤r → Module.Finite ℤ ((bar₂ (C:=C)).homology Z q : A) := by
  have h := finite_reverse (rows₃ (C:=C)) r (fun _=>bar₂_connected)
    (fun q hq=>by
      change IsZero (SSet.homology (C:=A) (bar₂ (C:=Diagram C (Fin 1))) Z q)
      exact bar₂_acyclic (fun _ _=>inferInstance) q hq)
    (fun q _=>rows₃_segal_homology_isIso q) (fun q h p=>by
      apply doubleRow_finite p q
      intro i hi
      have : Module.Finite ℤ ((bar₂ (C:=Diagram C (Fin 2))).homology Z i:A) := h i hi
      exact Module.Finite.equiv (firstDoubleRowHomologyIso (C:=C) i).toLinearEquiv) hf
  intro q hq
  have : Module.Finite ℤ ((bar₂ (C:=Diagram C (Fin 2))).homology Z q:A) := h q hq
  exact Module.Finite.equiv (firstDoubleRowHomologyIso (C:=C) q).toLinearEquiv
lemma bar_finite_of_triple
    (hf:∀n,n≤5 → Module.Finite ℤ ((bar₃ (C:=C)).homology Z n : A)) :
    ∀q,q≤3 → Module.Finite ℤ ((bar (C:=C)).homology Z q : A) :=
  bar₂_finite_reverse 3 (bar₃_finite_reverse 4 hf)
end IntervalBar.Diagram

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite
namespace NerveComponents
open FreeChains

variable {C D:Type} [Groupoid.{0} C] [Groupoid.{0} D]
noncomputable def toSkeletonπ : (nerve C).π₀ → Skeleton C :=
  SSet.π₀.lift (fun x=>toSkeleton (nerveEquiv x)) (fun {_ _} e=>congr_toSkeleton_of_iso (asIso (nerve.homEquiv e)))
noncomputable def fromSkeletonπ (p:Skeleton C) : (nerve C).π₀ :=
  SSet.π₀.mk (nerveEquiv.symm ((fromSkeleton C).obj p))
lemma roundtrip (x:(nerve C).π₀) : fromSkeletonπ (toSkeletonπ x)=x := by
  obtain ⟨x,rfl⟩ := SSet.π₀.mk_surjective x
  have e : (fromSkeleton C).obj (toSkeleton (nerveEquiv x)) ≅ nerveEquiv x :=
    Skeleton.isoOfEq (toSkeleton_fromSkeleton_obj _)
  exact (SSet.π₀.sound (nerve.edgeMk e.hom)).trans (by erw [Equiv.symm_apply_apply])
noncomputable def componentEquiv : (nerve C).π₀ ≃ Skeleton C where
  toFun := toSkeletonπ
  invFun := fromSkeletonπ
  left_inv := roundtrip
  right_inv p := toSkeleton_fromSkeleton_obj p
noncomputable def map (F:C⥤D) : Skeleton C → Skeleton D :=
  Quotient.lift (fun x=>toSkeleton (F.obj x)) (by rintro x y ⟨e⟩; exact congr_toSkeleton_of_iso (F.mapIso e))
@[simp] lemma map_mk (F:C⥤D) (x:C) : map F (toSkeleton x)=toSkeleton (F.obj x) := rfl
lemma naturality (F:C⥤D) (x:(nerve C).π₀) :
    toSkeletonπ (SSet.mapπ₀ (nerveMap F) x)=map F (toSkeletonπ x) := by
  obtain ⟨x,rfl⟩ := SSet.π₀.mk_surjective x
  rfl
noncomputable def zeroIso : (nerve C).homology Z 0 ≅ (ModuleCat.free ℤ).obj (Skeleton C) :=
  (nerve C).homology₀Iso Z ≪≫ FreeChains.iso _ ≪≫ (ModuleCat.free ℤ).mapIso (Equiv.toIso componentEquiv)
noncomputable def vertex (x:C) : Z ⟶ (nerve C).homology Z 0 :=
  ( (nerve C).chainComplex Z).liftCycles ((nerve C).ιChainComplex (nerveEquiv.symm x)) 0 (by simp) (by simp) ≫
    ((nerve C).chainComplex Z).homologyπ 0
@[reassoc (attr:=simp)] lemma vertex_zeroIso (x:C) : vertex x ≫ (zeroIso (C:=C)).hom =
    ModuleCat.ofHom (Finsupp.lsingle (toSkeleton x)) := by
  dsimp only [vertex,zeroIso,Iso.trans_hom]
  simp only [Category.assoc]
  erw [SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom_assoc]
  change Sigma.ι (fun _:(nerve C).π₀=>Z) (SSet.π₀.mk (nerveEquiv.symm x)) ≫
    FreeChains.forward _ ≫ (ModuleCat.free ℤ).map (↾componentEquiv)=_
  rw [FreeChains.ι_forward_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  exact ModuleCat.free_map_apply _ _
lemma vertex_natural (F:C⥤D) (x:C) : vertex x ≫ SSet.homologyMap (nerveMap F) Z 0=vertex (F.obj x) := by
  dsimp only [vertex,SSet.homologyMap]
  rw [Category.assoc,HomologicalComplex.homologyπ_naturality,←Category.assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap]
  erw [SSet.ι_chainComplexMap_f]
  have he : (nerveMap F).app (op ⦋0⦌) (nerveEquiv.symm x)=nerveEquiv.symm (F.obj x) :=
    ComposableArrows.ext₀ rfl
  rw [he]
lemma hom_ext {M:A} {f g:(nerve C).homology Z 0 ⟶ M}
    (h:∀x:C,vertex x ≫ f=vertex x ≫ g) : f=g := by
  apply (cancel_epi (zeroIso (C:=C)).inv).mp
  apply ModuleCat.free_hom_ext
  intro p
  obtain ⟨x,rfl⟩ := Quotient.exists_rep p
  have hh:=congrArg (fun k:Z⟶M=>k (1:ℤ)) (h x)
  have hv : ModuleCat.ofHom (Finsupp.lsingle (toSkeleton x)) ≫ (zeroIso (C:=C)).inv=vertex x := by
    erw [←vertex_zeroIso,Category.assoc,Iso.hom_inv_id,Category.comp_id]
  have ht:=congrArg (fun k:Z⟶(nerve C).homology Z 0=>k (1:ℤ)) hv
  change f ((zeroIso (C:=C)).inv (ModuleCat.freeMk (toSkeleton x))) =
    g ((zeroIso (C:=C)).inv (ModuleCat.freeMk (toSkeleton x)))
  change (zeroIso (C:=C)).inv (ModuleCat.freeMk (toSkeleton x))=vertex x (1:ℤ) at ht
  rw [ht]
  exact hh
lemma zeroIso_natural (F:C⥤D) : SSet.homologyMap (nerveMap F) Z 0 ≫ (zeroIso (C:=D)).hom =
    (zeroIso (C:=C)).hom ≫ (ModuleCat.free ℤ).map (↾(map F)) := by
  apply hom_ext; intro x
  rw [←Category.assoc,vertex_natural,vertex_zeroIso,vertex_zeroIso_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change ModuleCat.freeMk (toSkeleton (F.obj x)) =
    (ModuleCat.free ℤ).map (↾(map F)) (ModuleCat.freeMk (toSkeleton x))
  exact (ModuleCat.free_map_apply (R:=ℤ) (↾(map F)) (toSkeleton x)).symm
end NerveComponents

end

end OAI
