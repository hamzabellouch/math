import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.HomologyAdditive

namespace OAI

section

open Classical CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable

attribute [local instance 1200] Rep.hV2

namespace TrivialHomology
variable {G H K : Type} [Group G] [Group H] [Group K]
noncomputable abbrev map (f : G →* H) (q : ℕ) :=
  groupHomology.map f (TransitiveInduction.trivialMap f) q

@[simp] lemma map_id (q : ℕ) : map (MonoidHom.id G) q=𝟙 _ := by
  exact groupHomology.map_id (A:=Rep.trivial ℤ G ℤ) (n:=q)

lemma map_comp (f : G →* H) (g : H →* K) (q : ℕ) :
    map (g.comp f) q = map f q ≫ map g q := by
  exact groupHomology.map_comp f g (TransitiveInduction.trivialMap f)
    (TransitiveInduction.trivialMap g) q

lemma map_congr (f g : G →* H) (h : f=g) (q : ℕ) : map f q=map g q := by rw [h]

lemma isIso_equiv (e : G ≃* H) (q : ℕ) : IsIso (map e.toMonoidHom q) := by
  refine ⟨⟨map e.symm.toMonoidHom q,?_,?_⟩⟩
  · rw [← map_comp]
    have he : e.symm.toMonoidHom.comp e.toMonoidHom=MonoidHom.id G := by ext; simp
    rw [he, map_id]
  · rw [← map_comp]
    have he : e.toMonoidHom.comp e.symm.toMonoidHom=MonoidHom.id H := by ext; simp
    rw [he, map_id]
end TrivialHomology

namespace PolygonPlacement.Configuration
instance empty_subsingleton (a m : ℕ) : Subsingleton (Configuration a m 0) :=
  ⟨fun _ _ => ext (fun index => Fin.elim0 index)⟩

noncomputable def empty (a m : ℕ) : Configuration a m 0 := standardLE a m 0 (by omega)

noncomputable def emptyIso (a m : ℕ) : column a m 0 ≅ Rep.trivial ℤ (polygonFullGroup a m) ℤ :=
  Rep.mkIso (Representation.Equiv.mk (Finsupp.uniqueLinearEquiv ℤ ℤ (empty a m)) (by
    intro g
    apply Finsupp.lhom_ext
    intro x z
    change (TransitiveInduction.permutationRep g (single x z)) (empty a m)=
      (single x z) (empty a m)
    rw [TransitiveInduction.permutationRep_single]
    congr 2
    exact Subsingleton.elim _ _))

@[simp] lemma emptyIso_single (a m : ℕ) (x : Configuration a m 0) (z : ℤ) :
    (emptyIso a m).hom.hom (single x z)=z := by
  change (single x z) (empty a m)=z
  simp [Subsingleton.elim (empty a m) x]
lemma augmentation_pointMap {a m : ℕ} (f : Configuration a m 1) (q : ℕ) :
    groupHomology.map (MulAction.stabilizer (polygonFullGroup a m) f).subtype
      (TransitiveInduction.pointMap f) q ≫
      (groupHomology.functor ℤ (polygonFullGroup a m) q).map (boundary a m 0) ≫
      (groupHomology.functor ℤ (polygonFullGroup a m) q).map (emptyIso a m).hom =
    TrivialHomology.map (MulAction.stabilizer (polygonFullGroup a m) f).subtype q := by
  erw [← Functor.map_comp]
  erw [groupHomology.functor_map, ← groupHomology.map_comp]
  apply groupHomology.map_congr
  · rfl
  · apply LinearMap.ext
    intro z
    change (emptyIso a m).hom.hom ((boundary a m 0).hom (single f z))=z
    rw [boundary_zero_eq_face]
    dsimp only [faceHom]
    rw [TransitiveInduction.equivariantMap_single, emptyIso_single]
lemma stabilizer_H1_isIso (a m : ℕ) (hm : 33 ≤ m) (f : Configuration a m 1) :
    IsIso (TrivialHomology.map (MulAction.stabilizer (polygonFullGroup a m) f).subtype 1) := by
  have first := TransitiveInduction.isIso_map_pointMap f (fun g => transitive f g (by omega)) 1
  have second := boundary_zero_H1_isIso a m hm
  have third : IsIso ((groupHomology.functor ℤ (polygonFullGroup a m) 1).map
      (emptyIso a m).hom) := inferInstance
  rw [← augmentation_pointMap f 1]
  have composite := IsIso.comp_isIso' first (IsIso.comp_isIso' second third)
  exact composite

noncomputable def standardStabilizerEquiv (a p n : ℕ) :
    polygonFullGroup a n ≃* MulAction.stabilizer (polygonFullGroup a (p+n)) (standard a p n) :=
  (PolygonTracks.stabilizerEquiv a p n).trans (MulEquiv.subgroupCongr (stabilizer_standard a p n).symm)

lemma standardStabilizerEquiv_subtype (a p n : ℕ) :
    (MulAction.stabilizer (polygonFullGroup a (p+n)) (standard a p n)).subtype.comp
      (standardStabilizerEquiv a p n).toMonoidHom = PolygonTracks.stabilize a p n := rfl

lemma stabilize_H1_isIso (a n : ℕ) (hn : 32 ≤ n) :
    IsIso (TrivialHomology.map (PolygonTracks.stabilize a 1 n) 1) := by
  rw [← standardStabilizerEquiv_subtype a 1 n, TrivialHomology.map_comp]
  have := TrivialHomology.isIso_equiv (standardStabilizerEquiv a 1 n) 1
  have := stabilizer_H1_isIso a (1+n) (by omega) (standard a 1 n)
  infer_instance

end PolygonPlacement.Configuration
end SimpleAmenable

end

open Classical CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.TrivialHomology

attribute [local instance 1200] Rep.hV2
variable {G H : Type} [Group G] [Group H]

noncomputable def abelianizationEquiv (G : Type) [Group G] :
    groupHomology.H1 (Rep.trivial ℤ G ℤ) ≃+ Additive (Abelianization G) :=
  (groupHomology.H1AddEquivOfIsTrivial (Rep.trivial ℤ G ℤ)).trans
    (TensorProduct.rid ℤ (Additive (Abelianization G))).toAddEquiv

noncomputable def cycle (g : G) : groupHomology.H1 (Rep.trivial ℤ G ℤ) :=
  groupHomology.H1π _ ((groupHomology.cycles₁IsoOfIsTrivial _).inv (single g (1:ℤ)))

@[simp] lemma abelianizationEquiv_cycle (g : G) :
    abelianizationEquiv G (cycle g)=Additive.ofMul (Abelianization.of g) := by
  change (TensorProduct.rid ℤ (Additive (Abelianization G)))
    ((groupHomology.H1AddEquivOfIsTrivial (Rep.trivial ℤ G ℤ))
      (groupHomology.H1π _ ((groupHomology.cycles₁IsoOfIsTrivial _).inv (single g (1:ℤ))))) = _
  rw [groupHomology.H1AddEquivOfIsTrivial_single, TensorProduct.rid_tmul]
  simp

lemma cycle_map (f : G →* H) (g : G) : map f 1 (cycle g)=cycle (f g) := by
  unfold cycle
  rw [groupHomology.H1π_comp_map_apply]
  congr 1
  apply Subtype.ext
  change groupHomology.chainsMap₁ f (TransitiveInduction.trivialMap f) (single g (1:ℤ))=
    single (f g) (1:ℤ)
  simp [groupHomology.chainsMap₁, TransitiveInduction.trivialMap]

lemma cycle_eq_zero_iff (g : G) : cycle g=0 ↔ g∈_root_.commutator G := by
  rw [← (abelianizationEquiv G).map_eq_zero_iff, abelianizationEquiv_cycle]
  change Abelianization.of g=1 ↔ _
  change g∈(Abelianization.of : G →* Abelianization G).ker ↔ _
  rw [Abelianization.ker_of]

lemma commutator_comap_of_mono (f : G →* H) [Mono (map f 1)] :
    (_root_.commutator H).comap f=_root_.commutator G := by
  ext g
  change f g∈_root_.commutator H ↔ g∈_root_.commutator G
  rw [← cycle_eq_zero_iff, ← cycle_eq_zero_iff, ← cycle_map]
  exact (ModuleCat.mono_iff_injective (map f 1)).mp inferInstance |>.eq_iff' (map_zero _)

lemma H1_isZero_of_perfect [Group.IsPerfect G] :
    IsZero (groupHomology.H1 (Rep.trivial ℤ G ℤ)) := by
  have : Group.IsPerfect (Abelianization G) := Group.IsPerfect.ofSurjective
    (f:=Abelianization.of) (QuotientGroup.mk'_surjective (_root_.commutator G))
  have : Subsingleton (Abelianization G) := inferInstance
  have : Subsingleton (groupHomology.H1 (Rep.trivial ℤ G ℤ)) :=
    (abelianizationEquiv G).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _
end SimpleAmenable.TrivialHomology

end OAI
