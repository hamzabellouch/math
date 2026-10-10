import Mathlib
import OAI.CategoryTheory.Thomason.SimplexColimits

namespace OAI

/-! Finite Chains. -/

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory NormalizedChains OmegaCategory DirectedComplex
variable {P : Type u} [PartialOrder P]

structure FiniteVertexChain (P : Type u) [PartialOrder P] where
  vertices : Set P
  finite : vertices.Finite
  total : ∀ a ∈ vertices, ∀ b ∈ vertices, a ≤ b ∨ b ≤ a

namespace FiniteVertexChain
variable (S : FiniteVertexChain P)

@[instance_reducible] noncomputable def linearOrder : LinearOrder S.vertices := by
  classical
  exact {
    toPartialOrder := inferInstance
    le_total := fun a b => S.total a.val a.property b.val b.property
    toDecidableLE := Classical.decRel _ }

instance finiteType : Finite S.vertices := S.finite.to_subtype

abbrev inclusion : S.vertices →o P := (OrderEmbedding.subtype S.vertices).toOrderHom

def inter (T : FiniteVertexChain P) : FiniteVertexChain P where
  vertices := S.vertices ∩ T.vertices
  finite := S.finite.inter_of_left T.vertices
  total := fun a ha b hb => S.total a ha.1 b hb.1

def subInclusion (T : FiniteVertexChain P) (h : S.vertices ⊆ T.vertices) :
    S.vertices →o T.vertices where
  toFun a := ⟨a.val, h a.property⟩
  monotone' := fun _ _ h => h

abbrev Supports (x : Table (complex P)) : Prop :=
  ∀ p b, (x.row p b).val ∈ supportedOn S.vertices

lemma supports_inter (T : FiniteVertexChain P) (x : Table (complex P))
    (hS : S.Supports x) (hT : T.Supports x) : (S.inter T).Supports x := by
  intro p b
  rw [mem_supportedOn_iff]
  intro w hw a ha
  exact ⟨(mem_supportedOn_iff _ _).mp (hS p b) w hw a ha,
    (mem_supportedOn_iff _ _).mp (hT p b) w hw a ha⟩

noncomputable instance tableMap_isIso : IsIso (posetCategorificationTableMap S.vertices) := by
  let := S.linearOrder
  exact posetCategorificationTableMap_finiteLinear_isIso_all S.vertices

noncomputable def lift : (complex S.vertices).nu ⟶ categorification.obj (nerve P) :=
  inv (posetCategorificationTableMap S.vertices) ≫
    categorification.map (CategoryTheory.nerveMap S.inclusion.monotone.functor)

lemma lift_comp_tableMap : S.lift ≫ posetCategorificationTableMap P = (complexMap S.inclusion).nu := by
  unfold lift
  rw [Category.assoc, posetCategorificationTableMap_natural, IsIso.inv_hom_id_assoc]

lemma lift_natural (T : FiniteVertexChain P) (h : S.vertices ⊆ T.vertices) :
    (complexMap (S.subInclusion T h)).nu ≫ T.lift = S.lift := by
  apply (cancel_epi (posetCategorificationTableMap S.vertices)).mp
  rw [← Category.assoc, ← posetCategorificationTableMap_natural, lift, Category.assoc,
    IsIso.hom_inv_id_assoc]
  unfold lift
  rw [IsIso.hom_inv_id_assoc, ← categorification.map_comp]
  congr 1

lemma table_subInclusion_restrict (T : FiniteVertexChain P) (h : S.vertices ⊆ T.vertices)
    (x : Table (complex P)) (hxS : S.Supports x) (hxT : T.Supports x) :
    (complexMap (S.subInclusion T h)).table (restrictTable S.vertices x hxS) =
      restrictTable T.vertices x hxT := by
  apply table_map_orderEmbedding_injective (OrderEmbedding.subtype T.vertices)
  have hcomp : T.inclusion.comp (S.subInclusion T h) = S.inclusion := rfl
  change (DirectedComplex.Hom.comp (complexMap (S.subInclusion T h))
    (complexMap T.inclusion)).table _ = (complexMap T.inclusion).table _
  rw [← complexMap_comp, hcomp, table_map_restrictTable, table_map_restrictTable]

noncomputable def liftAt (x : Table (complex P)) (hx : S.Supports x) :
    (categorification.obj (nerve P)).Cell := S.lift.map (restrictTable S.vertices x hx)

lemma liftAt_natural (T : FiniteVertexChain P) (h : S.vertices ⊆ T.vertices)
    (x : Table (complex P)) (hxS : S.Supports x) (hxT : T.Supports x) :
    S.liftAt x hxS = T.liftAt x hxT := by
  have he := congrArg (fun F => F.map (restrictTable S.vertices x hxS)) (S.lift_natural T h)
  change T.lift.map ((complexMap (S.subInclusion T h)).table _) = S.liftAt x hxS at he
  rw [S.table_subInclusion_restrict T h x hxS hxT] at he
  exact he.symm

lemma liftAt_independent (T : FiniteVertexChain P) (x : Table (complex P))
    (hxS : S.Supports x) (hxT : T.Supports x) : S.liftAt x hxS = T.liftAt x hxT := by
  have hU := S.supports_inter T x hxS hxT
  exact ((S.inter T).liftAt_natural S Set.inter_subset_left x hU hxS).symm.trans
    ((S.inter T).liftAt_natural T Set.inter_subset_right x hU hxT)

lemma liftAt_table (x : Table (complex P)) (hx : S.Supports x) :
    (posetCategorificationTableMap P).map (S.liftAt x hx) = x := by
  have he := congrArg (fun F => F.map (restrictTable S.vertices x hx)) S.lift_comp_tableMap
  exact he.trans (table_map_restrictTable S.vertices x hx)

lemma restrict_truncate (x : Table (complex P)) (hx : S.Supports x) (k : ℕ) (e : Bool)
    (ht : S.Supports (Table.truncate k e x)) :
    restrictTable S.vertices (Table.truncate k e x) ht =
      Table.truncate k e (restrictTable S.vertices x hx) := by
  apply table_map_orderEmbedding_injective (OrderEmbedding.subtype S.vertices)
  rw [table_map_restrictTable, DirectedComplex.Hom.table_truncate, table_map_restrictTable]

lemma restrict_composable (k : ℕ) (x y : Table (complex P))
    (h : Table.truncate k true x = Table.truncate k false y)
    (hx : S.Supports x) (hy : S.Supports y) :
    Table.truncate k true (restrictTable S.vertices x hx) =
      Table.truncate k false (restrictTable S.vertices y hy) := by
  apply table_map_orderEmbedding_injective (OrderEmbedding.subtype S.vertices)
  rw [DirectedComplex.Hom.table_truncate, DirectedComplex.Hom.table_truncate,
    table_map_restrictTable, table_map_restrictTable, h]

lemma restrict_comp (k : ℕ) (x y : Table (complex P))
    (h : Table.truncate k true x = Table.truncate k false y)
    (hx : S.Supports x) (hy : S.Supports y) (hz : S.Supports (Table.comp k x y h)) :
    restrictTable S.vertices (Table.comp k x y h) hz =
      Table.comp k (restrictTable S.vertices x hx) (restrictTable S.vertices y hy)
        (S.restrict_composable k x y h hx hy) := by
  apply table_map_orderEmbedding_injective (OrderEmbedding.subtype S.vertices)
  rw [table_map_restrictTable]
  have he := (complexMap S.inclusion).table_comp k _ _
    (S.restrict_composable k x y h hx hy) (by
      rw [table_map_restrictTable, table_map_restrictTable]; exact h)
  dsimp only [inclusion] at he
  apply Eq.trans ?_ he.symm
  ext p b
  simp only [Table.comp_row]
  rw [table_map_restrictTable S.vertices x hx, table_map_restrictTable S.vertices y hy]

end FiniteVertexChain

noncomputable def tableChainSupport (x : Table (complex P)) : FiniteVertexChain P :=
  let h := table_finite_chain_support x
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1⟩

lemma tableChainSupport_supports (x : Table (complex P)) : (tableChainSupport x).Supports x :=
  (table_finite_chain_support x).choose_spec.2.2

noncomputable def posetTableInverseMap (x : Table (complex P)) :
    (categorification.obj (nerve P)).Cell :=
  (tableChainSupport x).liftAt x (tableChainSupport_supports x)

lemma posetTableInverseMap_eq (S : FiniteVertexChain P) (x : Table (complex P)) (hx : S.Supports x) :
    posetTableInverseMap x = S.liftAt x hx :=
  (tableChainSupport x).liftAt_independent S x (tableChainSupport_supports x) hx

noncomputable def posetTableInverse (P : Type u) [PartialOrder P] :
    (complex P).nu ⟶ categorification.obj (nerve P) where
  map := posetTableInverseMap
  map_source k x := by
    let S := tableChainSupport x
    have hx : S.Supports x := tableChainSupport_supports x
    have ht : S.Supports (Table.truncate k false x) := table_truncate_supported S.vertices x hx k false
    change posetTableInverseMap (Table.truncate k false x) = _
    rw [posetTableInverseMap_eq S x hx, posetTableInverseMap_eq S _ ht]
    unfold FiniteVertexChain.liftAt
    rw [S.restrict_truncate x hx k false ht]
    exact S.lift.map_source k _
  map_target k x := by
    let S := tableChainSupport x
    have hx : S.Supports x := tableChainSupport_supports x
    have ht : S.Supports (Table.truncate k true x) := table_truncate_supported S.vertices x hx k true
    change posetTableInverseMap (Table.truncate k true x) = _
    rw [posetTableInverseMap_eq S x hx, posetTableInverseMap_eq S _ ht]
    unfold FiniteVertexChain.liftAt
    rw [S.restrict_truncate x hx k true ht]
    exact S.lift.map_target k _
  map_comp k x y h h' := by
    let S := tableChainSupport (Table.comp k x y h)
    have hz : S.Supports (Table.comp k x y h) := tableChainSupport_supports _
    obtain ⟨hx,hy⟩ := table_comp_supported_factors S.vertices k x y h hz
    change posetTableInverseMap (Table.comp k x y h) = _
    revert h'
    rw [posetTableInverseMap_eq S x hx, posetTableInverseMap_eq S y hy,
      posetTableInverseMap_eq S _ hz]
    intro h'
    unfold FiniteVertexChain.liftAt at h' ⊢
    rw [S.restrict_comp k x y h hx hy hz]
    exact S.lift.map_comp k _ _ (S.restrict_composable k x y h hx hy) h'

lemma posetTableInverse_comp_tableMap (P : Type u) [PartialOrder P] :
    posetTableInverse P ≫ posetCategorificationTableMap P = 𝟙 _ := by
  apply OmegaCategory.Functor.ext
  funext x
  exact (tableChainSupport x).liftAt_table x (tableChainSupport_supports x)

lemma posetTableInverse_on_chain (S : FiniteVertexChain P) :
    (complexMap S.inclusion).nu ≫ posetTableInverse P = S.lift := by
  apply OmegaCategory.Functor.ext
  funext x
  have hx : S.Supports ((complexMap S.inclusion).table x) := by
    intro p b
    exact map_mem_supportedOn S.vertices (x.row p b).val
  change posetTableInverseMap ((complexMap S.inclusion).table x) = S.lift.map x
  rw [posetTableInverseMap_eq S _ hx]
  unfold FiniteVertexChain.liftAt
  congr 1
  apply table_map_orderEmbedding_injective (OrderEmbedding.subtype S.vertices)
  exact table_map_restrictTable S.vertices _ hx

noncomputable def finiteRangeChain {Q : Type u} [LinearOrder Q] [Finite Q]
    (f : Q →o P) : FiniteVertexChain P where
  vertices := Set.range f
  finite := Set.finite_range f
  total := by
    rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩
    exact (le_total a b).imp (fun h => f.monotone h) (fun h => f.monotone h)

def finiteRangeFactor {Q : Type u} [LinearOrder Q] [Finite Q] (f : Q →o P) :
    Q →o (finiteRangeChain f).vertices where
  toFun a := ⟨f a, a, rfl⟩
  monotone' := f.monotone

attribute [local instance] posetCategorificationTableMap_finiteLinear_isIso_all

lemma posetTableInverse_finite_natural {Q : Type u} [LinearOrder Q] [Finite Q]
    (f : Q →o P) :
    (complexMap f).nu ≫ posetTableInverse P =
      inv (posetCategorificationTableMap Q) ≫
        categorification.map (CategoryTheory.nerveMap f.monotone.functor) := by
  let S := finiteRangeChain f
  let g := finiteRangeFactor f
  have hf : S.inclusion.comp g = f := rfl
  rw [← hf, complexMap_comp]
  change ((complexMap g).nu : (complex Q).nu ⟶ (complex S.vertices).nu) ≫
    ((complexMap S.inclusion).nu ≫ posetTableInverse P) = _
  rw [posetTableInverse_on_chain]
  apply (cancel_epi (posetCategorificationTableMap Q)).mp
  rw [← Category.assoc, ← posetCategorificationTableMap_natural]
  unfold FiniteVertexChain.lift
  rw [Category.assoc, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id_assoc,
    ← categorification.map_comp]
  rfl

lemma posetCategorificationTableMap_comp_inverse (P : Type u) [PartialOrder P] :
    posetCategorificationTableMap P ≫ posetTableInverse P = 𝟙 _ := by
  apply (posetSimplexIsColimit P).hom_ext
  intro s
  change categorification.map (CategoryTheory.nerveMap (simplexVertexOrder s).monotone.functor) ≫
    (posetCategorificationTableMap P ≫ posetTableInverse P) =
    categorification.map (CategoryTheory.nerveMap (simplexVertexOrder s).monotone.functor) ≫ 𝟙 _
  rw [← Category.assoc, posetCategorificationTableMap_natural, Category.assoc,
    posetTableInverse_finite_natural]
  rw [IsIso.hom_inv_id_assoc, Category.comp_id]

noncomputable instance posetCategorificationTableMap_isIso (P : Type u) [PartialOrder P] :
    IsIso (posetCategorificationTableMap P) :=
  ⟨⟨posetTableInverse P, posetCategorificationTableMap_comp_inverse P,
    posetTableInverse_comp_tableMap P⟩⟩

end Thomason

end

end OAI
