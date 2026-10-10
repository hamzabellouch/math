import Mathlib
import OAI.GroupTheory.FiniteType.TwistedBrinPattern

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin.GermBrick
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma restricts_iff_chart {b c : GermBrick ρ} (h : LocalEmbedding ρ) (hb : mk ρ h = b) :
    Restricts ρ c b ↔ ∃ p : Prefix S, c = mk ρ (LocalEmbedding.comp ρ h (LocalEmbedding.ofPrefix ρ p)) := by
  constructor
  · rintro ⟨k,p,hk,rfl⟩
    obtain ⟨a,rfl⟩ := (mk_eq_iff ρ k h).mp (hk.symm.trans hb.symm)
    refine ⟨p.permute (ρ a),?_⟩
    rw [LocalEmbedding.comp_assoc,LocalEmbedding.global_ofPrefix,
      ← LocalEmbedding.comp_assoc,mk_gauge]
  · rintro ⟨p,rfl⟩
    exact ⟨h,p,hb.symm,rfl⟩

lemma eq_of_common_restriction_of_region_eq {b c d : GermBrick ρ}
    (hc : Restricts ρ c b) (hd : Restricts ρ d b) (he : region ρ c = region ρ d) : c = d := by
  obtain ⟨p,rfl⟩ := (restricts_iff_chart ρ (representative ρ b) (mk_representative ρ b)).mp hc
  obtain ⟨q,rfl⟩ := (restricts_iff_chart ρ (representative ρ b) (mk_representative ρ b)).mp hd
  have hpq : p.brick = q.brick := by
    change Set.range ((representative ρ b) ∘ p.chart) =
      Set.range ((representative ρ b) ∘ q.chart) at he
    rw [Set.range_comp,Set.range_comp] at he
    exact (Set.image_injective.mpr (representative ρ b).injective) he
  rw [Prefix.brick_injective hpq]

end TwistedBrin.GermBrick

namespace TwistedBrin.Basis
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

noncomputable def descendants (C : Basis ρ) (d : GermBrick ρ) : Finset C := by
  classical
  exact Finset.univ.filter (fun c => GermBrick.region ρ c.val ⊆ GermBrick.region ρ d)

lemma mem_descendants (C : Basis ρ) (d : GermBrick ρ) (c : C) :
    c ∈ descendants ρ C d ↔ GermBrick.region ρ c.val ⊆ GermBrick.region ρ d := by
  classical
  simp [descendants]

lemma region_iff_descendants {D C : Basis ρ} (hDC : D ≤ C) (d : D) (x : Box S) :
    x ∈ GermBrick.region ρ d.val ↔
    ∃ c : C, c ∈ descendants ρ C d.val ∧ x ∈ GermBrick.region ρ c.val := by
  constructor
  · intro hx
    obtain ⟨c,hc,_⟩ := C.partition x
    obtain ⟨e,he⟩ := hDC c
    have hxe := GermBrick.region_subset_of_restricts ρ he hc
    have hed : e = d := (D.partition x).unique hxe hx
    subst e
    exact ⟨c,(mem_descendants ρ C d.val c).mpr (GermBrick.region_subset_of_restricts ρ he),hc⟩
  · rintro ⟨c,hc,hx⟩
    exact (mem_descendants ρ C d.val c).mp hc hx

lemma region_eq_of_descendants_eq {D E C : Basis ρ} (hDC : D ≤ C) (hEC : E ≤ C)
    (d : D) (e : E) (he : descendants ρ C d.val = descendants ρ C e.val) :
    GermBrick.region ρ d.val = GermBrick.region ρ e.val := by
  ext x
  rw [region_iff_descendants ρ hDC,region_iff_descendants ρ hEC,he]

lemma germ_eq_of_region_eq_above {B D E : Basis ρ} (hBD : B ≤ D) (hBE : B ≤ E)
    (d : D) (e : E) (he : GermBrick.region ρ d.val = GermBrick.region ρ e.val) : d.val = e.val := by
  obtain ⟨b,hb⟩ := hBD d
  obtain ⟨c,hc⟩ := hBE e
  obtain ⟨x,hx⟩ := GermBrick.region_nonempty ρ d.val
  have hbx := GermBrick.region_subset_of_restricts ρ hb hx
  have hcx := GermBrick.region_subset_of_restricts ρ hc (he ▸ hx)
  have hbc : b = c := (B.partition x).unique hbx hcx
  subst c
  exact GermBrick.eq_of_common_restriction_of_region_eq ρ hb hc he

noncomputable def intervalCode (C D : Basis ρ) : Finset (Finset C) := by
  classical
  exact Finset.univ.image (fun d : D => descendants ρ C d.val)

lemma intervalCode_injective (B C : Basis ρ) :
    Function.Injective (fun D : {D : Basis ρ // B ≤ D ∧ D ≤ C} => intervalCode ρ C D.val) := by
  classical
  have help : ∀ (D E : Basis ρ), B ≤ D → D ≤ C → B ≤ E → E ≤ C →
      intervalCode ρ C D = intervalCode ρ C E → D.pieces ⊆ E.pieces := by
    intro D E hBD hDC hBE hEC he d hd
    have hm : descendants ρ C d ∈ intervalCode ρ C E := by
      rw [← he]
      exact Finset.mem_image.mpr ⟨⟨d,hd⟩,Finset.mem_univ _,rfl⟩
    obtain ⟨e,_,hed⟩ := Finset.mem_image.mp hm
    have hr := region_eq_of_descendants_eq ρ hDC hEC ⟨d,hd⟩ e hed.symm
    have hg := germ_eq_of_region_eq_above ρ hBD hBE ⟨d,hd⟩ e hr
    change d = e.val at hg
    rw [hg]
    exact e.property
  intro D E he
  apply Subtype.ext
  apply Basis.ext
  exact Finset.Subset.antisymm
    (help D.val E.val D.property.1 D.property.2 E.property.1 E.property.2 he)
    (help E.val D.val E.property.1 E.property.2 D.property.1 D.property.2 he.symm)

theorem finite_interval (B C : Basis ρ) : Finite {D : Basis ρ // B ≤ D ∧ D ≤ C} :=
  Finite.of_injective _ (intervalCode_injective ρ B C)

end

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

noncomputable def rankModel (k : ℕ) : Basis ρ := by
  classical
  exact if h : ∃ B : Basis ρ, rank ρ B = k then Classical.choose h else trivial ρ

lemma rank_rankModel (B : Basis ρ) : rank ρ (rankModel ρ (rank ρ B)) = rank ρ B := by
  classical
  simp only [rankModel,dite_eq_left (show ∃ C : Basis ρ, rank ρ C = rank ρ B from ⟨B,rfl⟩)]
  exact Classical.choose_spec (show ∃ C : Basis ρ, rank ρ C = rank ρ B from ⟨B,rfl⟩)

lemma rank_finite_orbit_representatives (n : ℕ) :
    ∃ R : Finset (Basis ρ), ∀ B : Basis ρ, rank ρ B ≤ n →
      ∃ g : localGroup ρ, translate ρ g B ∈ R := by
  classical
  refine ⟨(Finset.range (n+1)).image (rankModel ρ),fun B hB => ?_⟩
  obtain ⟨g,hg⟩ := orbit_of_rank_eq ρ (rank_rankModel ρ B).symm
  refine ⟨g,Finset.mem_image.mpr ⟨rank ρ B,Finset.mem_range.mpr (by omega),?_⟩⟩
  exact hg.symm

lemma twistPieces_translate_self (B : Basis ρ) (a : B → A) :
    translate ρ (twistPiecesHom ρ B a) B = B := by
  exact MulAction.mem_stabilizer_iff.mp
    (rigid_le_vertexStabilizer ρ B (twistPiecesHom_mem_rigidStabilizer ρ B a))

lemma pair_finite_orbit_representatives (h : Oligomorphic ρ) (n : ℕ) :
    ∃ R : Finset (Basis ρ × Basis ρ), ∀ B C : Basis ρ,
      CutRefines ρ B C → rank ρ C ≤ n →
      ∃ g : localGroup ρ, (translate ρ g B,translate ρ g C) ∈ R := by
  classical
  obtain ⟨T,hT⟩ := rank_finite_orbit_representatives ρ n
  choose Q hQ using fun B : Basis ρ => outgoing_finite_orbit_representatives ρ h B n
  let R := T.biUnion (fun B => (Q B).image (fun C => (B,C)))
  refine ⟨R,fun B C hBC hC => ?_⟩
  have hB : rank ρ B ≤ n := (rank_mono ρ (le_of_cutRefines ρ hBC)).trans hC
  obtain ⟨g,hg⟩ := hT B hB
  obtain ⟨a,ha⟩ := hQ (translate ρ g B) (translate ρ g C)
    (translate_cutRefines ρ g hBC) (by simpa only [rank_translate] using hC)
  refine ⟨twistPiecesHom ρ (translate ρ g B) a * g,?_⟩
  rw [translate_mul,translate_mul,twistPieces_translate_self]
  exact Finset.mem_biUnion.mpr ⟨translate ρ g B,hg,Finset.mem_image.mpr ⟨_,ha,rfl⟩⟩

end TwistedBrin.Basis

namespace TwistedBrin.Prefix
variable {S : Type u}

lemma append_left_cancel (p : Prefix S) {q r : Prefix S} (h : p.append q = p.append r) : q = r := by
  apply Prefix.ext
  intro s
  have he := congrArg (fun t : Prefix S => t s) h
  exact List.append_cancel_left he

end TwistedBrin.Prefix

namespace TwistedBrin.Pattern
variable {S : Type u}

lemma root_fixed_of_prefixes_fixed (σ : Equiv.Perm S) (s : S) (P Q : Pattern S)
    (h : ∀ i : Leaves (.split s P Q), (leafPrefix (.split s P Q) i).permute σ =
      leafPrefix (.split s P Q) i) : σ s = s := by
  classical
  by_contra hs
  let x : Box S := fun t => Stream'.const (decide (t = σ s))
  obtain ⟨i,hi,_⟩ := partition (.split s P Q) x
  let p := leafPrefix (.split s P Q) i
  have hp : p s = p (σ s) := by
    have he := congrArg (fun q : Prefix S => q (σ s)) (h i)
    simpa only [Prefix.permute_apply,Equiv.symm_apply_apply] using he
  have hn : 0 < (p s).length := List.length_pos_iff.mpr (split_prefix_nonempty s P Q i)
  have hm := (Prefix.mem_brick_iff_get p x).mp hi
  have hxs := hm s 0 hn
  have hxt := hm (σ s) 0 (by rw [← hp]; exact hn)
  have hh : (p (σ s))[0]'(by rw [← hp]; exact hn) = (p s)[0]'hn := by simp [hp]
  have he := hxs.trans (hxt.trans hh).symm
  simp [x,Stream'.get,Stream'.const,Ne.symm hs] at he

lemma coordinate_rigidity (σ : Equiv.Perm S) (P : Pattern S) :
    (∀ i : Leaves P, (leafPrefix P i).permute σ = leafPrefix P i) ↔
      ∀ s ∈ coordinates P, σ s = s := by
  classical
  induction P with
  | leaf => simp [coordinates,leafPrefix]
  | split s P Q ihP ihQ =>
    constructor
    · intro h
      have hs := root_fixed_of_prefixes_fixed σ s P Q h
      have hP : ∀ i : Leaves P, (leafPrefix P i).permute σ = leafPrefix P i := by
        intro i
        have he := h (.inl i)
        change ((Prefix.cut s false).append (leafPrefix P i)).permute σ =
          (Prefix.cut s false).append (leafPrefix P i) at he
        rw [Prefix.permute_append,Prefix.permute_cut,hs] at he
        exact Prefix.append_left_cancel _ he
      have hQ : ∀ i : Leaves Q, (leafPrefix Q i).permute σ = leafPrefix Q i := by
        intro i
        have he := h (.inr i)
        change ((Prefix.cut s true).append (leafPrefix Q i)).permute σ =
          (Prefix.cut s true).append (leafPrefix Q i) at he
        rw [Prefix.permute_append,Prefix.permute_cut,hs] at he
        exact Prefix.append_left_cancel _ he
      intro t ht
      simp only [coordinates,Finset.mem_insert,Finset.mem_union] at ht
      rcases ht with rfl | ht | ht
      · exact hs
      · exact ihP.mp hP t ht
      · exact ihQ.mp hQ t ht
    · intro h
      have hs : σ s = s := h s (by simp [coordinates])
      have hP := ihP.mpr (fun t ht => h t (by simp [coordinates,ht]))
      have hQ := ihQ.mpr (fun t ht => h t (by simp [coordinates,ht]))
      intro i
      cases i with
      | inl i => simp only [leafPrefix,Prefix.permute_append,Prefix.permute_cut,hs,hP]
      | inr i => simp only [leafPrefix,Prefix.permute_append,Prefix.permute_cut,hs,hQ]

end TwistedBrin.Pattern

namespace TwistedBrin.GermBrick
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma restriction_injective (h : LocalEmbedding ρ) :
    Function.Injective (fun p : Prefix S => mk ρ (LocalEmbedding.comp ρ h (LocalEmbedding.ofPrefix ρ p))) := by
  intro p q he
  have hr := congrArg (region ρ) he
  change Set.range (h ∘ p.chart) = Set.range (h ∘ q.chart) at hr
  rw [Set.range_comp,Set.range_comp] at hr
  exact Prefix.brick_injective ((Set.image_injective.mpr h.injective) hr)

end TwistedBrin.GermBrick

namespace TwistedBrin
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

def pointwiseStabilizer (F : Finset S) : Subgroup A where
  carrier := {a | ∀ s ∈ F, ρ a s = s}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb s hs
    simp only [map_mul,Equiv.Perm.mul_apply,hb s hs,ha s hs]
  inv_mem' := by
    intro a ha s hs
    rw [map_inv]
    exact (ρ a).symm_apply_eq.mpr (ha s hs).symm

namespace Basis

lemma twistPieces_expanded_fixed_iff (B : Basis ρ) (P : B → Pattern S) (a : B → A)
    (i : Σ b : B, Pattern.Leaves (P b)) :
    GermBrick.groupEquiv ρ (twistPiecesHom ρ B a)
      (GermBrick.mk ρ (expandedChart ρ B P i)) =
      GermBrick.mk ρ (expandedChart ρ B P i) ↔
    (Pattern.leafPrefix (P i.1) i.2).permute (ρ (a i.1)) = Pattern.leafPrefix (P i.1) i.2 := by
  rw [twistPieces_expanded_germ]
  change GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ B i.1)
    (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix _ _))) =
    GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ B i.1)
      (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix _ _))) ↔ _
  rw [Pattern.relabel_prefix]
  exact (GermBrick.restriction_injective ρ (chart ρ B i.1)).eq_iff

lemma Forest.twistPieces_mem_rigid_iff {B C : Basis ρ} (F : Forest ρ B C) (a : B → A) :
    twistPiecesHom ρ B a ∈ rigidStabilizer ρ C ↔
      ∀ b : B, a b ∈ pointwiseStabilizer ρ (Pattern.coordinates (F.pattern b)) := by
  constructor
  · intro h b
    apply (Pattern.coordinate_rigidity (ρ (a b)) (F.pattern b)).mp
    intro i
    apply (twistPieces_expanded_fixed_iff ρ B F.pattern a ⟨b,i⟩).mp
    rw [F.chart_eq]
    exact h (F.leaves ⟨b,i⟩)
  · intro h c
    obtain ⟨⟨b,i⟩,rfl⟩ := F.leaves.surjective c
    rw [← F.chart_eq]
    apply (twistPieces_expanded_fixed_iff ρ B F.pattern a ⟨b,i⟩).mpr
    exact (Pattern.coordinate_rigidity (ρ (a b)) (F.pattern b)).mpr (h b) i

noncomputable def Forest.rigidPairHom {B C : Basis ρ} (F : Forest ρ B C) :
    (Π b : B, pointwiseStabilizer ρ (Pattern.coordinates (F.pattern b))) →*
      ↥((rigidStabilizer ρ B ⊓ rigidStabilizer ρ C) : Subgroup (localGroup ρ)) where
  toFun a := ⟨twistPiecesHom ρ B (fun b => (a b).val),
    twistPiecesHom_mem_rigidStabilizer ρ B _,
    (F.twistPieces_mem_rigid_iff ρ _).mpr (fun b => (a b).property)⟩
  map_one' := by
    apply Subtype.ext
    exact (twistPiecesHom ρ B).map_one
  map_mul' a c := by
    apply Subtype.ext
    exact (twistPiecesHom ρ B).map_mul _ _

noncomputable def Forest.rigidPairEquiv (hρ : Function.Injective ρ) {B C : Basis ρ}
    (F : Forest ρ B C) :
    (Π b : B, pointwiseStabilizer ρ (Pattern.coordinates (F.pattern b))) ≃*
      ↥((rigidStabilizer ρ B ⊓ rigidStabilizer ρ C) : Subgroup (localGroup ρ)) :=
  MulEquiv.ofBijective (F.rigidPairHom ρ) ⟨by
    intro a c he
    have hh := twistPiecesHom_injective ρ hρ B (congrArg Subtype.val he)
    funext b
    exact Subtype.ext (congrFun hh b),by
    rintro ⟨g,hgB,hgC⟩
    obtain ⟨a,rfl⟩ := exists_twistPiecesHom_of_mem ρ hgB
    have ha := (F.twistPieces_mem_rigid_iff ρ a).mp hgC
    exact ⟨fun b => ⟨a b,ha b⟩,rfl⟩⟩

end Basis
end TwistedBrin

namespace TwistedBrin.Basis
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

noncomputable def pairStabilizer (B C : Basis ρ) : Subgroup (localGroup ρ) :=
  vertexStabilizer ρ B ⊓ vertexStabilizer ρ C

noncomputable def pairPermutationHom (B C : Basis ρ) :
    pairStabilizer ρ B C →* Equiv.Perm B × Equiv.Perm C :=
  ((vertexPermutationHom ρ B).comp
    (Subgroup.inclusion (show pairStabilizer ρ B C ≤ vertexStabilizer ρ B from inf_le_left))).prod
  ((vertexPermutationHom ρ C).comp
    (Subgroup.inclusion (show pairStabilizer ρ B C ≤ vertexStabilizer ρ C from inf_le_right)))

lemma mem_pairPermutationHom_ker (B C : Basis ρ) (g : pairStabilizer ρ B C) :
    g ∈ (pairPermutationHom ρ B C).ker ↔
      g.val ∈ rigidStabilizer ρ B ∧ g.val ∈ rigidStabilizer ρ C := by
  change ((vertexPermutationHom ρ B) ⟨g.val,g.property.1⟩,
    (vertexPermutationHom ρ C) ⟨g.val,g.property.2⟩) = (1,1) ↔ _
  rw [Prod.mk.injEq]
  exact and_congr (mem_vertexPermutationHom_ker ρ B ⟨g.val,g.property.1⟩)
    (mem_vertexPermutationHom_ker ρ C ⟨g.val,g.property.2⟩)

noncomputable def rigidPairToKernel (B C : Basis ρ) :
    ↥((rigidStabilizer ρ B ⊓ rigidStabilizer ρ C) : Subgroup (localGroup ρ)) →*
      (pairPermutationHom ρ B C).ker where
  toFun g := ⟨⟨g.val,rigid_le_vertexStabilizer ρ B g.property.1,
    rigid_le_vertexStabilizer ρ C g.property.2⟩,
    (mem_pairPermutationHom_ker ρ B C _).mpr g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def rigidPairKernelEquiv (B C : Basis ρ) :
    ↥((rigidStabilizer ρ B ⊓ rigidStabilizer ρ C) : Subgroup (localGroup ρ)) ≃*
      (pairPermutationHom ρ B C).ker :=
  MulEquiv.ofBijective (rigidPairToKernel ρ B C) ⟨by
    intro g h he
    exact Subtype.ext (congrArg (fun k => k.val.val) he),by
    intro g
    exact ⟨⟨g.val.val,(mem_pairPermutationHom_ker ρ B C g.val).mp g.property⟩,rfl⟩⟩

instance pairPermutationHom_ker_finiteIndex (B C : Basis ρ) :
    (pairPermutationHom ρ B C).ker.FiniteIndex := by
  classical
  exact Subgroup.finiteIndex_ker _

noncomputable def Forest.pairKernelEquiv (hρ : Function.Injective ρ) {B C : Basis ρ}
    (F : Forest ρ B C) :
    (Π b : B, pointwiseStabilizer ρ (Pattern.coordinates (F.pattern b))) ≃*
      (pairPermutationHom ρ B C).ker :=
  (F.rigidPairEquiv ρ hρ).trans (rigidPairKernelEquiv ρ B C)

noncomputable def groupEquiv (g : localGroup ρ) : Equiv.Perm (Basis ρ) where
  toFun := translate ρ g
  invFun := translate ρ g⁻¹
  left_inv B := by rw [← translate_mul,inv_mul_cancel,translate_one]
  right_inv B := by rw [← translate_mul,mul_inv_cancel,translate_one]

noncomputable def translateSet (g : localGroup ρ) (c : Finset (Basis ρ)) : Finset (Basis ρ) :=
  c.map (groupEquiv ρ g).toEmbedding

noncomputable def intervalSets (B C : Basis ρ) : Finset (Finset (Basis ρ)) := by
  classical
  letI := finite_interval ρ B C
  letI : Fintype {D : Basis ρ // B ≤ D ∧ D ≤ C} := Fintype.ofFinite _
  let E : Finset (Basis ρ) := Finset.univ.image (fun D : {D : Basis ρ // B ≤ D ∧ D ≤ C} => D.val)
  exact E.powerset

lemma mem_intervalSets_iff (B C : Basis ρ) (c : Finset (Basis ρ)) :
    c ∈ intervalSets ρ B C ↔ ∀ D ∈ c, B ≤ D ∧ D ≤ C := by
  classical
  simp only [intervalSets,Finset.mem_powerset,Finset.subset_iff,Finset.mem_image,
    Finset.mem_univ,true_and]
  constructor
  · intro h D hD
    obtain ⟨E,hE⟩ := h hD
    exact hE ▸ E.property
  · intro h D hD
    exact ⟨⟨D,h D hD⟩,rfl⟩

lemma interval_sets_finite_orbit_representatives (h : Oligomorphic ρ) (n : ℕ) :
    ∃ R : Finset (Finset (Basis ρ)), ∀ (B C : Basis ρ) (c : Finset (Basis ρ)),
      CutRefines ρ B C → rank ρ C ≤ n →
      (∀ D ∈ c, B ≤ D ∧ D ≤ C) →
      ∃ g : localGroup ρ, translateSet ρ g c ∈ R := by
  classical
  obtain ⟨T,hT⟩ := pair_finite_orbit_representatives ρ h n
  refine ⟨T.biUnion (fun p => intervalSets ρ p.1 p.2),fun B C c hBC hC hc => ?_⟩
  obtain ⟨g,hg⟩ := hT B C hBC hC
  refine ⟨g,Finset.mem_biUnion.mpr ⟨_,hg,?_⟩⟩
  apply (mem_intervalSets_iff ρ _ _ _).mpr
  intro D hD
  obtain ⟨E,hE,rfl⟩ := Finset.mem_map.mp hD
  exact ⟨translate_mono ρ g (hc E hE).1,translate_mono ρ g (hc E hE).2⟩

end TwistedBrin.Basis

namespace TwistedBrin.Prefix
variable {S : Type u}

lemma cut_append_cut (s t : S) (hs : s ≠ t) (a b : Bool) :
    (cut s a).append (cut t b) = (cut t b).append (cut s a) := by
  classical
  apply Prefix.ext
  intro r
  by_cases hr : r = s
  · subst r
    simp [hs]
  · by_cases ht : r = t
    · subst r
      simp [hr]
    · simp [hr,ht]

lemma cut_append_commute (s t : S) (hs : s ≠ t) (a b : Bool) (p : Prefix S) :
    (cut s a).append ((cut t b).append p) =
      (cut t b).append ((cut s a).append p) := by
  rw [← append_assoc,cut_append_cut s t hs,append_assoc]

end TwistedBrin.Prefix

namespace TwistedBrin.Pattern
variable {S : Type u}

structure SplitView (P : Pattern S) (s : S) where
  left : Pattern S
  right : Pattern S
  leaves : Leaves (.split s left right) ≃ Leaves P
  prefix_eq : ∀ i, leafPrefix P (leaves i) = leafPrefix (.split s left right) i

private def shuffle {α β γ δ : Type*} : ((α ⊕ γ) ⊕ (β ⊕ δ)) ≃ ((α ⊕ β) ⊕ (γ ⊕ δ)) where
  toFun
    | .inl (.inl a) => .inl (.inl a)
    | .inl (.inr c) => .inr (.inl c)
    | .inr (.inl b) => .inl (.inr b)
    | .inr (.inr d) => .inr (.inr d)
  invFun
    | .inl (.inl a) => .inl (.inl a)
    | .inl (.inr b) => .inr (.inl b)
    | .inr (.inl c) => .inl (.inr c)
    | .inr (.inr d) => .inr (.inr d)
  left_inv := by rintro ((a|c)|(b|d)) <;> rfl
  right_inv := by rintro ((a|b)|(c|d)) <;> rfl

noncomputable def SplitView.commute {P Q : Pattern S} {s t : S} (h : s ≠ t)
    (p : SplitView P s) (q : SplitView Q s) : SplitView (.split t P Q) s where
  left := .split t p.left q.left
  right := .split t p.right q.right
  leaves := shuffle.trans (Equiv.sumCongr p.leaves q.leaves)
  prefix_eq := by
    rintro ((i|i)|(i|i))
    · change (Prefix.cut t false).append (leafPrefix P (p.leaves (.inl i))) = _
      rw [p.prefix_eq (.inl i)]
      exact Prefix.cut_append_commute t s h.symm false false _
    · change (Prefix.cut t true).append (leafPrefix Q (q.leaves (.inl i))) = _
      rw [q.prefix_eq (.inl i)]
      exact Prefix.cut_append_commute t s h.symm true false _
    · change (Prefix.cut t false).append (leafPrefix P (p.leaves (.inr i))) = _
      rw [p.prefix_eq (.inr i)]
      exact Prefix.cut_append_commute t s h.symm false true _
    · change (Prefix.cut t true).append (leafPrefix Q (q.leaves (.inr i))) = _
      rw [q.prefix_eq (.inr i)]
      exact Prefix.cut_append_commute t s h.symm true true _

theorem splitView_exists (P : Pattern S) (s : S)
    (h : ∀ i : Leaves P, leafPrefix P i s ≠ []) : Nonempty (SplitView P s) := by
  induction P with
  | leaf => exact (h () rfl).elim
  | split t P Q ihP ihQ =>
    by_cases hst : s = t
    · subst s
      exact ⟨⟨P,Q,Equiv.refl _,fun _ => rfl⟩⟩
    · have hP : ∀ i : Leaves P, leafPrefix P i s ≠ [] := by
        intro i
        simpa [leafPrefix,Prefix.cut_apply,hst] using h (.inl i)
      have hQ : ∀ i : Leaves Q, leafPrefix Q i s ≠ [] := by
        intro i
        simpa [leafPrefix,Prefix.cut_apply,hst] using h (.inr i)
      obtain ⟨p⟩ := ihP hP
      obtain ⟨q⟩ := ihQ hQ
      exact ⟨p.commute hst q⟩

end TwistedBrin.Pattern

end

end OAI
