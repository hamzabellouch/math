import Mathlib
import OAI.GroupTheory.FiniteType.TwistedBrin

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
namespace TwistedBrin
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace GermBrick

lemma range_chart_restricts (h : LocalEmbedding ρ) (p q : Prefix S) (a : A)
    (he : ∀ y, h (p.chart y) = q.chart (twist ρ a y)) :
    Restricts ρ (mk ρ (LocalEmbedding.ofPrefix ρ q)) (mk ρ h) := by
  refine ⟨h,p,rfl,?_⟩
  have he' : LocalEmbedding.comp ρ h (LocalEmbedding.ofPrefix ρ p) =
      LocalEmbedding.comp ρ (LocalEmbedding.ofPrefix ρ q) (LocalEmbedding.global ρ a) := by
    apply LocalEmbedding.ext
    exact he
  rw [he',mk_gauge]

end GermBrick
namespace Basis

noncomputable def ofPartition {I : Type*} [Fintype I] (p : I → Prefix S)
    (hp : IsPartition p) : Basis ρ := by
  classical
  let j := fun i => GermBrick.mk ρ (LocalEmbedding.ofPrefix ρ (p i))
  exact {
    pieces := Finset.univ.image j
    partition := by
      intro x
      obtain ⟨i,hi,hu⟩ := hp x
      refine ⟨⟨j i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩,hi,?_⟩
      intro b hb
      obtain ⟨k,_,hk⟩ := Finset.mem_image.mp b.property
      apply Subtype.ext
      have hb' : x ∈ (p k).brick := by
        change x ∈ GermBrick.region ρ b.1 at hb
        rwa [← hk] at hb
      exact hk.symm.trans (congrArg j (hu k hb')) }

lemma mem_ofPartition {I : Type*} [Fintype I] (p : I → Prefix S)
    (hp : IsPartition p) (i : I) :
    GermBrick.mk ρ (LocalEmbedding.ofPrefix ρ (p i)) ∈ (ofPartition ρ p hp).pieces := by
  classical
  exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

lemma exists_prefix_of_mem_ofPartition {I : Type*} [Fintype I] (p : I → Prefix S)
    (hp : IsPartition p) (b : ofPartition ρ p hp) :
    ∃ i, b.1 = GermBrick.mk ρ (LocalEmbedding.ofPrefix ρ (p i)) := by
  classical
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp b.property
  exact ⟨i,hi.symm⟩

noncomputable def grid (b : S →₀ ℕ) : Basis ρ :=
  ofPartition ρ (Prefix.gridPrefix b) (Prefix.grid_partition b)

lemma grid_refines_grid {b c : S →₀ ℕ} (hbc : b ≤ c) : Refines ρ (grid ρ b) (grid ρ c) := by
  intro r
  obtain ⟨z,hz⟩ := exists_prefix_of_mem_ofPartition ρ _ _ r
  let x : Box S := (Prefix.gridPrefix c z).chart (fun _ _ => false)
  let w := Prefix.gridPoint b x
  refine ⟨⟨_,mem_ofPartition ρ _ _ w⟩,?_⟩
  rw [hz]
  apply GermBrick.restricts_prefix
  apply Prefix.extends_of_mem_of_length_le (Prefix.mem_gridPrefix b x) (Prefix.chart_mem_brick _ _)
  intro s
  simpa only [Prefix.gridPrefix_length] using hbc s

lemma local_standard_refinement (B : Basis ρ) (x : Box S) :
    ∃ (b : B) (q : Prefix S), x ∈ q.brick ∧
      GermBrick.Restricts ρ (GermBrick.mk ρ (LocalEmbedding.ofPrefix ρ q)) b.1 := by
  obtain ⟨b,hb,_⟩ := B.partition x
  rw [← chart_region ρ B b] at hb
  obtain ⟨y,rfl⟩ := hb
  obtain ⟨p,q,a,hyp,he⟩ := (chart ρ B b).locally_standard y
  refine ⟨b,q,?_,?_⟩
  · obtain ⟨z,rfl⟩ := hyp
    change (chart ρ B b).toFun (p.chart z) ∈ q.brick
    rw [he]
    exact Prefix.chart_mem_brick _ _
  · convert GermBrick.range_chart_restricts ρ (chart ρ B b) p q a he using 1
    exact (GermBrick.mk_representative ρ b.1).symm

lemma has_grid_refinement (B : Basis ρ) : ∃ w : S →₀ ℕ, Refines ρ B (grid ρ w) := by
  classical
  choose b q hx hr using local_standard_refinement ρ B
  have hcover : (Set.univ : Set (Box S)) ⊆ ⋃ x, (q x).brick := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x,hx x⟩
  obtain ⟨I,hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (q x).brick) (fun x => (q x).isOpen_brick) hcover
  have hc : ∀ x, ∃ i ∈ I, x ∈ (q i).brick := by
    intro x
    simpa only [Set.mem_iUnion,exists_prop] using hI (Set.mem_univ x)
  obtain ⟨w,hw⟩ := finite_grid_refinement I q hc
  refine ⟨w,?_⟩
  intro r
  obtain ⟨z,hz⟩ := exists_prefix_of_mem_ofPartition ρ _ _ r
  obtain ⟨i,_,hi⟩ := hw z
  refine ⟨b i,?_⟩
  rw [hz]
  exact GermBrick.restricts_trans ρ (GermBrick.restricts_prefix ρ hi) (hr i)

lemma directed (B C : Basis ρ) : ∃ D : Basis ρ, Refines ρ B D ∧ Refines ρ C D := by
  obtain ⟨b,hb⟩ := has_grid_refinement ρ B
  obtain ⟨c,hc⟩ := has_grid_refinement ρ C
  refine ⟨grid ρ (b+c),refines_trans ρ hb (grid_refines_grid ρ ?_),
    refines_trans ρ hc (grid_refines_grid ρ ?_)⟩
  · intro s
    exact Nat.le_add_right _ _
  · intro s
    exact Nat.le_add_left _ _

end Basis
end TwistedBrin

namespace TwistedBrin.Prefix
variable {S : Type u}

lemma eq_empty_of_brick_univ {p : Prefix S} (hp : p.brick = Set.univ) : p = empty := by
  apply Prefix.ext
  intro s
  cases hs : p s with
  | nil => rfl
  | cons b l =>
    have hm : (fun (_ : S) (_ : ℕ) => !b) ∈ p.brick := hp.symm ▸ Set.mem_univ _
    have h := (mem_brick_iff_get _ _).mp hm s 0 (by simp [hs])
    cases b <;> simp [hs,Stream'.get] at h

end TwistedBrin.Prefix

namespace TwistedBrin
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace GermBrick

lemma eq_of_restricts_of_region_eq {a b : GermBrick ρ} (hab : Restricts ρ a b)
    (he : region ρ a = region ρ b) : a = b := by
  obtain ⟨h,p,rfl,rfl⟩ := hab
  have hp : p.brick = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : h x ∈ region ρ (mk ρ h) := ⟨x,rfl⟩
    rw [← he] at hx
    obtain ⟨y,hy⟩ := hx
    refine ⟨y,?_⟩
    exact h.toEmbedding.injective hy
  rw [Prefix.eq_empty_of_brick_univ hp,LocalEmbedding.ofPrefix_empty,LocalEmbedding.comp_identity]

end GermBrick
namespace Basis

@[ext] lemma ext {B C : Basis ρ} (h : B.pieces = C.pieces) : B = C := by
  cases B; cases C
  simp_all only

lemma eq_of_common_point (B : Basis ρ) {b c : B} {x : Box S}
    (hb : x ∈ GermBrick.region ρ b.1) (hc : x ∈ GermBrick.region ρ c.1) : b = c :=
  (B.partition x).unique hb hc

lemma refines_ancestor_unique {B C : Basis ρ} {c : C} {b b' : B}
    (hb : GermBrick.Restricts ρ c.1 b.1) (hb' : GermBrick.Restricts ρ c.1 b'.1) : b = b' := by
  obtain ⟨x,hx⟩ := GermBrick.region_nonempty ρ c.1
  exact eq_of_common_point ρ B (GermBrick.region_subset_of_restricts ρ hb hx)
    (GermBrick.region_subset_of_restricts ρ hb' hx)

lemma pieces_subset_of_refines_both {B C : Basis ρ} (hBC : Refines ρ B C) (hCB : Refines ρ C B) :
    B.pieces ⊆ C.pieces := by
  intro a ha
  obtain ⟨b,hb⟩ := hCB ⟨a,ha⟩
  obtain ⟨a',ha'⟩ := hBC b
  have haa : (⟨a,ha⟩ : B) = a' :=
    refines_ancestor_unique ρ (GermBrick.restricts_refl ρ a) (GermBrick.restricts_trans ρ hb ha')
  have hae : a = a'.1 := congrArg Subtype.val haa
  have he : GermBrick.region ρ a = GermBrick.region ρ b.1 := by
    apply Set.Subset.antisymm (GermBrick.region_subset_of_restricts ρ hb)
    simpa only [hae] using GermBrick.region_subset_of_restricts ρ ha'
  have heq : a = b.1 := GermBrick.eq_of_restricts_of_region_eq ρ hb he
  rw [heq]
  exact b.property

lemma refines_antisymm {B C : Basis ρ} (hBC : Refines ρ B C) (hCB : Refines ρ C B) : B = C :=
  ext ρ (Finset.Subset.antisymm (pieces_subset_of_refines_both ρ hBC hCB)
    (pieces_subset_of_refines_both ρ hCB hBC))

instance : PartialOrder (Basis ρ) where
  le := Refines ρ
  le_refl := refines_refl ρ
  le_trans := fun _ _ _ => refines_trans ρ
  le_antisymm := fun _ _ => refines_antisymm ρ

lemma le_def (B C : Basis ρ) : B ≤ C ↔ Refines ρ B C := Iff.rfl

noncomputable def ancestor {B C : Basis ρ} (hBC : B ≤ C) (c : C) : B := (hBC c).choose
lemma ancestor_restricts {B C : Basis ρ} (hBC : B ≤ C) (c : C) :
    GermBrick.Restricts ρ c.1 (ancestor ρ hBC c).1 := (hBC c).choose_spec

lemma ancestor_surjective {B C : Basis ρ} (hBC : B ≤ C) : Function.Surjective (ancestor ρ hBC) := by
  intro b
  obtain ⟨x,hx⟩ := GermBrick.region_nonempty ρ b.1
  obtain ⟨c,hc,_⟩ := C.partition x
  refine ⟨c,?_⟩
  exact eq_of_common_point ρ B
    (GermBrick.region_subset_of_restricts ρ (ancestor_restricts ρ hBC c) hc) hx

lemma rank_eq_card (B : Basis ρ) : rank ρ B = Fintype.card B := by
  simp only [rank,Fintype.card_coe]

lemma rank_mono {B C : Basis ρ} (hBC : B ≤ C) : rank ρ B ≤ rank ρ C := by
  rw [rank_eq_card,rank_eq_card]
  exact Fintype.card_le_of_surjective _ (ancestor_surjective ρ hBC)

lemma translate_one (B : Basis ρ) : translate ρ 1 B = B := by
  apply Basis.ext
  change B.pieces.map (GermBrick.groupEquiv ρ 1).toEmbedding = B.pieces
  have h : GermBrick.groupEquiv ρ 1 = 1 := (GermBrick.action ρ).map_one
  rw [h]
  exact Finset.map_refl

lemma translate_mul (g h : localGroup ρ) (B : Basis ρ) :
    translate ρ (g*h) B = translate ρ g (translate ρ h B) := by
  apply Basis.ext
  change B.pieces.map (GermBrick.groupEquiv ρ (g*h)).toEmbedding =
    (B.pieces.map (GermBrick.groupEquiv ρ h).toEmbedding).map (GermBrick.groupEquiv ρ g).toEmbedding
  rw [Finset.map_map]
  congr 1
  apply Function.Embedding.ext
  intro b
  exact congrArg (fun e : Equiv.Perm (GermBrick ρ) => e b) ((GermBrick.action ρ).map_mul g h)

noncomputable instance : MulAction (localGroup ρ) (Basis ρ) where
  smul := translate ρ
  one_smul := translate_one ρ
  mul_smul := translate_mul ρ

lemma translate_mono (g : localGroup ρ) {B C : Basis ρ} (hBC : B ≤ C) :
    translate ρ g B ≤ translate ρ g C := by
  intro c
  obtain ⟨d,hd,hed⟩ := Finset.mem_map.mp c.property
  obtain ⟨b,hb⟩ := hBC ⟨d,hd⟩
  refine ⟨⟨GermBrick.groupEquiv ρ g b.1,Finset.mem_map.mpr ⟨b.1,b.property,rfl⟩⟩,?_⟩
  rw [← hed]
  exact GermBrick.restricts_map ρ _ hb

lemma eq_of_le_of_rank_eq {B C : Basis ρ} (hBC : B ≤ C) (hr : rank ρ B = rank ρ C) : B = C := by
  classical
  have hi : Function.Injective (ancestor ρ hBC) := by
    exact ((Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨ancestor_surjective ρ hBC,by simpa only [rank_eq_card] using hr.symm⟩).injective
  have he (c : C) : c.1 = (ancestor ρ hBC c).1 := by
    apply GermBrick.eq_of_restricts_of_region_eq ρ (ancestor_restricts ρ hBC c)
    apply Set.Subset.antisymm (GermBrick.region_subset_of_restricts ρ (ancestor_restricts ρ hBC c))
    intro x hx
    obtain ⟨d,hd,_⟩ := C.partition x
    have ha : ancestor ρ hBC d = ancestor ρ hBC c := eq_of_common_point ρ B
      (GermBrick.region_subset_of_restricts ρ (ancestor_restricts ρ hBC d) hd) hx
    rwa [hi ha] at hd
  apply refines_antisymm ρ hBC
  intro b
  obtain ⟨c,hc⟩ := ancestor_surjective ρ hBC b
  refine ⟨c,?_⟩
  have hb : c.1 = b.1 := (he c).trans (congrArg Subtype.val hc)
  rw [hb]
  exact GermBrick.restricts_refl ρ _

lemma rank_strictMono : StrictMono (rank ρ) := by
  intro B C h
  apply lt_of_le_of_ne (rank_mono ρ h.le)
  intro he
  exact h.ne (eq_of_le_of_rank_eq ρ h.le he)

end Basis

lemma locallyStandard_of_charts {I : Type*} (k h : I → LocalEmbedding ρ)
    (hk : ∀ x : Box S, ∃ i y, k i y = x) (f : Box S → Box S)
    (hf : ∀ i y, f (k i y) = h i y) : LocallyStandard ρ f := by
  intro x
  obtain ⟨i,y,rfl⟩ := hk x
  obtain ⟨p,q,a,hyp,hk'⟩ := (k i).locally_standard y
  obtain ⟨r,s,b,hyr,hh'⟩ := (h i).locally_standard y
  let v := Prefix.common y p r
  let c := p.suffix v
  let d := r.suffix v
  have hp : p.append c = v := Prefix.append_suffix (Prefix.extends_common_left hyp)
  have hr : r.append d = v := Prefix.append_suffix (Prefix.extends_common_right hyr)
  let q' := q.append (c.permute (ρ a))
  let s' := s.append (d.permute (ρ b))
  have hk_v (z : Box S) : k i (v.chart z) = q'.chart (twist ρ a z) := by
    change (k i).toFun (v.chart z) = _
    rw [← hp,Prefix.chart_append,hk',twist_chart,← Prefix.chart_append]
  have hh_v (z : Box S) : h i (v.chart z) = s'.chart (twist ρ b z) := by
    change (h i).toFun (v.chart z) = _
    rw [← hr,Prefix.chart_append,hh',twist_chart,← Prefix.chart_append]
  have hym : y ∈ v.brick := Prefix.mem_common y p r
  obtain ⟨z,hz⟩ := hym
  refine ⟨q',s',b*a⁻¹,?_,?_⟩
  · rw [← hz,hk_v]
    exact Prefix.chart_mem_brick _ _
  · intro w
    have hw : q'.chart w = k i (v.chart (twist ρ a⁻¹ w)) := by
      rw [hk_v,← twist_mul,mul_inv_cancel,twist_one]
    rw [hw,hf,hh_v,twist_mul]

namespace Basis

noncomputable def transition {B C : Basis ρ} (e : B ≃ C) : Equiv.Perm (Box S) :=
  (equivalence ρ B).symm.trans ((Equiv.prodCongr e (Equiv.refl _)).trans (equivalence ρ C))

lemma transition_chart {B C : Basis ρ} (e : B ≃ C) (b : B) (x : Box S) :
    transition ρ e (chart ρ B b x) = chart ρ C (e b) x := by
  change equivalence ρ C ((Equiv.prodCongr e (Equiv.refl _))
    ((equivalence ρ B).symm (equivalence ρ B (b,x)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

lemma transition_isLocal {B C : Basis ρ} (e : B ≃ C) : IsLocal ρ (transition ρ e) := by
  apply locallyStandard_of_charts ρ (chart ρ B) (fun b => chart ρ C (e b))
  · intro x
    obtain ⟨⟨b,y⟩,hy⟩ := (equivalence ρ B).surjective x
    exact ⟨b,y,hy⟩
  · exact transition_chart ρ e

noncomputable def transitionElement {B C : Basis ρ} (e : B ≃ C) : localGroup ρ :=
  ⟨transition ρ e,transition_isLocal ρ e⟩

lemma transition_germBrick {B C : Basis ρ} (e : B ≃ C) (b : B) :
    GermBrick.groupEquiv ρ (transitionElement ρ e) b.1 = (e b).1 := by
  rw [← GermBrick.mk_representative ρ b.1,← GermBrick.mk_representative ρ (e b).1]
  change GermBrick.mk ρ (LocalEmbedding.comp ρ _ _) = GermBrick.mk ρ _
  congr 1
  apply LocalEmbedding.ext
  exact transition_chart ρ e b

lemma translate_transition {B C : Basis ρ} (e : B ≃ C) :
    translate ρ (transitionElement ρ e) B = C := by
  classical
  apply Basis.ext
  apply Finset.ext
  intro b
  change b ∈ B.pieces.map (GermBrick.groupEquiv ρ (transitionElement ρ e)).toEmbedding ↔ _
  constructor
  · intro hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hb
    change GermBrick.groupEquiv ρ (transitionElement ρ e) a ∈ C.pieces
    rw [transition_germBrick ρ e ⟨a,ha⟩]
    exact (e ⟨a,ha⟩).property
  · intro hb
    obtain ⟨a,ha⟩ := e.surjective ⟨b,hb⟩
    exact Finset.mem_map.mpr ⟨a.1,a.property,(transition_germBrick ρ e a).trans (congrArg Subtype.val ha)⟩

lemma orbit_of_rank_eq {B C : Basis ρ} (hr : rank ρ B = rank ρ C) :
    ∃ g : localGroup ρ, g • B = C := by
  have hc : Fintype.card B = Fintype.card C := by simpa only [rank_eq_card] using hr
  let e := Classical.choice (Fintype.card_eq.mp hc)
  exact ⟨transitionElement ρ e,translate_transition ρ e⟩

end Basis
end

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma twist_injective (hρ : Function.Injective ρ) : Function.Injective (twist ρ) := by
  classical
  intro a b hab
  have he : ρ a⁻¹ = ρ b⁻¹ := by
    apply Equiv.ext
    intro s
    by_contra hn
    let x : Box S := fun t _ => decide (t = ρ a⁻¹ s)
    have hx := congrArg (fun e : Equiv.Perm (Box S) => e x s 0) hab
    change decide (ρ a⁻¹ s = ρ a⁻¹ s) = decide (ρ b⁻¹ s = ρ a⁻¹ s) at hx
    simp only [decide_true] at hx
    exact hn (of_decide_eq_true hx.symm).symm
  exact inv_injective (hρ he)

namespace Basis

noncomputable def twistPieces (B : Basis ρ) (a : B → A) : Equiv.Perm (Box S) :=
  (equivalence ρ B).symm.trans ((Equiv.prodCongrRight fun b => twist ρ (a b)).trans
    (equivalence ρ B))

lemma twistPieces_chart (B : Basis ρ) (a : B → A) (b : B) (x : Box S) :
    twistPieces ρ B a (chart ρ B b x) = chart ρ B b (twist ρ (a b) x) := by
  change equivalence ρ B ((Equiv.prodCongrRight fun b => twist ρ (a b))
    ((equivalence ρ B).symm (equivalence ρ B (b,x)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

lemma twistPieces_isLocal (B : Basis ρ) (a : B → A) : IsLocal ρ (twistPieces ρ B a) := by
  apply locallyStandard_of_charts ρ (chart ρ B)
    (fun b => LocalEmbedding.comp ρ (chart ρ B b) (LocalEmbedding.global ρ (a b)))
  · intro x
    obtain ⟨⟨b,y⟩,hy⟩ := (equivalence ρ B).surjective x
    exact ⟨b,y,hy⟩
  · exact twistPieces_chart ρ B a

noncomputable def twistPiecesHom (B : Basis ρ) : (B → A) →* localGroup ρ where
  toFun a := ⟨twistPieces ρ B a,twistPieces_isLocal ρ B a⟩
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    obtain ⟨⟨b,y⟩,rfl⟩ := (equivalence ρ B).surjective x
    change twistPieces ρ B 1 (chart ρ B b y) = chart ρ B b y
    rw [twistPieces_chart]
    exact congrArg (chart ρ B b) (twist_one ρ y)
  map_mul' a c := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    obtain ⟨⟨b,y⟩,rfl⟩ := (equivalence ρ B).surjective x
    change twistPieces ρ B (a*c) (chart ρ B b y) =
      twistPieces ρ B a (twistPieces ρ B c (chart ρ B b y))
    rw [twistPieces_chart,twistPieces_chart,twistPieces_chart]
    exact congrArg (chart ρ B b) (twist_mul ρ (a b) (c b) y)

lemma twistPiecesHom_injective (hρ : Function.Injective ρ) (B : Basis ρ) :
    Function.Injective (twistPiecesHom ρ B) := by
  intro a c he
  funext b
  apply twist_injective ρ hρ
  apply Equiv.ext
  intro x
  apply (chart ρ B b).toEmbedding.injective
  have hh := congrArg (fun g : localGroup ρ => g.val (chart ρ B b x)) he
  change twistPieces ρ B a (chart ρ B b x) = twistPieces ρ B c (chart ρ B b x) at hh
  simpa only [twistPieces_chart] using hh

def rigidStabilizer (B : Basis ρ) : Subgroup (localGroup ρ) where
  carrier := {g | ∀ b : B, GermBrick.groupEquiv ρ g b.1 = b.1}
  one_mem' := by
    intro b
    have h := (GermBrick.action ρ).map_one
    exact congrArg (fun e : Equiv.Perm (GermBrick ρ) => e b.1) h
  mul_mem' := by
    intro g h hg hh b
    have he := congrArg (fun e : Equiv.Perm (GermBrick ρ) => e b.1) ((GermBrick.action ρ).map_mul g h)
    change GermBrick.groupEquiv ρ (g*h) b.1 = GermBrick.groupEquiv ρ g (GermBrick.groupEquiv ρ h b.1) at he
    rw [he,hh b,hg b]
  inv_mem' := by
    intro g hg b
    apply (GermBrick.groupEquiv ρ g).injective
    rw [hg b]
    have h := (GermBrick.action ρ).map_inv g
    change GermBrick.groupEquiv ρ g ((GermBrick.action ρ) g⁻¹ b.1) = _
    rw [h]
    exact (GermBrick.groupEquiv ρ g).apply_symm_apply _

lemma twistPiecesHom_mem_rigidStabilizer (B : Basis ρ) (a : B → A) :
    twistPiecesHom ρ B a ∈ rigidStabilizer ρ B := by
  intro b
  rw [← GermBrick.mk_representative ρ b.1]
  change GermBrick.mk ρ (LocalEmbedding.comp ρ _ _) = GermBrick.mk ρ _
  apply (GermBrick.mk_eq_iff ρ _ _).mpr
  refine ⟨a b,?_⟩
  apply LocalEmbedding.ext
  exact twistPieces_chart ρ B a b

lemma exists_chart_twist_of_mem_rigidStabilizer {B : Basis ρ} {g : localGroup ρ}
    (hg : g ∈ rigidStabilizer ρ B) (b : B) :
    ∃ a : A, ∀ x, g.val (chart ρ B b x) = chart ρ B b (twist ρ a x) := by
  have hh := hg b
  rw [← GermBrick.mk_representative ρ b.1] at hh
  obtain ⟨a,ha⟩ := (GermBrick.mk_eq_iff ρ _ _).mp hh
  refine ⟨a,fun x => ?_⟩
  exact congrArg (fun f : LocalEmbedding ρ => f x) ha

lemma exists_twistPiecesHom_of_mem {B : Basis ρ} {g : localGroup ρ}
    (hg : g ∈ rigidStabilizer ρ B) : ∃ a : B → A, twistPiecesHom ρ B a = g := by
  choose a ha using exists_chart_twist_of_mem_rigidStabilizer ρ hg
  refine ⟨a,?_⟩
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨⟨b,y⟩,rfl⟩ := (equivalence ρ B).surjective x
  change twistPieces ρ B a (chart ρ B b y) = g.val (chart ρ B b y)
  rw [twistPieces_chart,ha b y]

noncomputable def rigidStabilizerEquiv (hρ : Function.Injective ρ) (B : Basis ρ) :
    (B → A) ≃* rigidStabilizer ρ B :=
  MulEquiv.ofBijective ((twistPiecesHom ρ B).codRestrict _ (twistPiecesHom_mem_rigidStabilizer ρ B))
    ⟨fun _ _ h => twistPiecesHom_injective ρ hρ B (congrArg Subtype.val h),by
      rintro ⟨g,hg⟩
      obtain ⟨a,ha⟩ := exists_twistPiecesHom_of_mem ρ hg
      exact ⟨a,Subtype.ext ha⟩⟩

end Basis
end TwistedBrin

end

end OAI
