import Mathlib
import OAI.GroupTheory.FiniteType.TwistedBrinBasis

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
namespace TwistedBrin.Prefix
variable {S : Type u}
@[simp] lemma permute_empty (σ : Equiv.Perm S) : permute σ empty = empty := by ext; simp
@[simp] lemma permute_append (σ : Equiv.Perm S) (p q : Prefix S) :
    permute σ (p.append q) = (permute σ p).append (permute σ q) := by ext; rfl
@[simp] lemma permute_cut (σ : Equiv.Perm S) (s : S) (b : Bool) :
    permute σ (cut s b) = cut (σ s) b := by
  classical
  apply Prefix.ext
  intro t
  simp only [permute_apply,cut_apply]
  have he : σ.symm t = s ↔ t = σ s := σ.symm_apply_eq
  simp only [he]
end TwistedBrin.Prefix

namespace TwistedBrin.Pattern
variable {S : Type u}

def relabel (σ : Equiv.Perm S) : Pattern S → Pattern S
  | .leaf => .leaf
  | .split s P Q => .split (σ s) (relabel σ P) (relabel σ Q)

def relabelLeaves (σ : Equiv.Perm S) : (P : Pattern S) → Leaves P ≃ Leaves (relabel σ P)
  | .leaf => Equiv.refl _
  | .split _ P Q => Equiv.sumCongr (relabelLeaves σ P) (relabelLeaves σ Q)

lemma relabel_prefix (σ : Equiv.Perm S) (P : Pattern S) (i : Leaves P) :
    leafPrefix (relabel σ P) (relabelLeaves σ P i) = (leafPrefix P i).permute σ := by
  induction P with
  | leaf => simp [relabel,relabelLeaves,leafPrefix]
  | split s P Q ihP ihQ =>
    cases i with
    | inl i =>
      change (Prefix.cut (σ s) false).append _ =
        ((Prefix.cut s false).append (leafPrefix P i)).permute σ
      rw [Prefix.permute_append,Prefix.permute_cut,ihP]
    | inr i =>
      change (Prefix.cut (σ s) true).append _ =
        ((Prefix.cut s true).append (leafPrefix Q i)).permute σ
      rw [Prefix.permute_append,Prefix.permute_cut,ihQ]

def graft : (P : Pattern S) → (Leaves P → Pattern S) → Pattern S
  | .leaf, Q => Q ()
  | .split s P R, Q => .split s (graft P (fun i => Q (.inl i)))
      (graft R (fun i => Q (.inr i)))

def graftLeaves : (P : Pattern S) → (Q : Leaves P → Pattern S) →
    (Σ i : Leaves P, Leaves (Q i)) ≃ Leaves (graft P Q)
  | .leaf, Q => {
      toFun := fun i => by rcases i with ⟨⟨⟩,i⟩; exact i
      invFun := fun i => ⟨(),i⟩
      left_inv := by rintro ⟨⟨⟩,i⟩; rfl
      right_inv := fun _ => rfl }
  | .split _ P R, Q => {
      toFun := fun i => match i with
        | ⟨.inl i,j⟩ => .inl (graftLeaves P (fun i => Q (.inl i)) ⟨i,j⟩)
        | ⟨.inr i,j⟩ => .inr (graftLeaves R (fun i => Q (.inr i)) ⟨i,j⟩)
      invFun := fun i => match i with
        | .inl j => let k := (graftLeaves P (fun i => Q (.inl i))).symm j; ⟨.inl k.1,k.2⟩
        | .inr j => let k := (graftLeaves R (fun i => Q (.inr i))).symm j; ⟨.inr k.1,k.2⟩
      left_inv := by
        rintro ⟨i,j⟩
        cases i with
        | inl i =>
          exact congrArg (fun k : Σ i : Leaves P, Leaves (Q (.inl i)) =>
            (⟨Sum.inl k.1,k.2⟩ : Σ i : Leaves (.split _ P R), Leaves (Q i)))
            ((graftLeaves P (fun i => Q (.inl i))).symm_apply_apply ⟨i,j⟩)
        | inr i =>
          exact congrArg (fun k : Σ i : Leaves R, Leaves (Q (.inr i)) =>
            (⟨Sum.inr k.1,k.2⟩ : Σ i : Leaves (.split _ P R), Leaves (Q i)))
            ((graftLeaves R (fun i => Q (.inr i))).symm_apply_apply ⟨i,j⟩)
      right_inv := by
        intro i
        cases i with
        | inl i =>
          exact congrArg Sum.inl ((graftLeaves P (fun i => Q (.inl i))).apply_symm_apply i)
        | inr i =>
          exact congrArg Sum.inr ((graftLeaves R (fun i => Q (.inr i))).apply_symm_apply i) }

lemma graft_prefix (P : Pattern S) (Q : Leaves P → Pattern S)
    (i : Leaves P) (j : Leaves (Q i)) :
    leafPrefix (graft P Q) (graftLeaves P Q ⟨i,j⟩) =
      (leafPrefix P i).append (leafPrefix (Q i) j) := by
  induction P with
  | leaf => cases i; exact (Prefix.empty_append _).symm
  | split s P R ihP ihR =>
    cases i with
    | inl i =>
      change (Prefix.cut s false).append _ =
        ((Prefix.cut s false).append _).append _
      rw [ihP,Prefix.append_assoc]
    | inr i =>
      change (Prefix.cut s true).append _ =
        ((Prefix.cut s true).append _).append _
      rw [ihR,Prefix.append_assoc]
end TwistedBrin.Pattern

namespace TwistedBrin
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace Basis

structure Forest (B C : Basis ρ) where
  pattern : B → Pattern S
  leaves : (Σ b : B, Pattern.Leaves (pattern b)) ≃ C
  chart_eq : ∀ i, GermBrick.mk ρ (expandedChart ρ B pattern i) = (leaves i).val

namespace Forest
variable {ρ}

abbrev Index {B C : Basis ρ} (F : Forest ρ B C) := Σ b : B, Pattern.Leaves (F.pattern b)

lemma refines {B C : Basis ρ} (F : Forest ρ B C) : B ≤ C := by
  intro c
  obtain ⟨i,rfl⟩ := F.leaves.surjective c
  refine ⟨i.1,chart ρ B i.1,Pattern.leafPrefix (F.pattern i.1) i.2,?_,(F.chart_eq i).symm⟩
  exact (GermBrick.mk_representative ρ i.1.val).symm

noncomputable def refl (B : Basis ρ) : Forest ρ B B where
  pattern := fun _ => .leaf
  leaves := {
    toFun := Sigma.fst
    invFun := fun b => ⟨b,()⟩
    left_inv := by rintro ⟨b,⟨⟩⟩; rfl
    right_inv := fun _ => rfl }
  chart_eq := by
    rintro ⟨b,i⟩
    change GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ B b)
      (LocalEmbedding.ofPrefix ρ Prefix.empty)) = b.val
    simp [chart]

noncomputable def expansion (B : Basis ρ) (P : B → Pattern S) : Forest ρ B (expand ρ B P) := by
  classical
  let f : (Σ b : B, Pattern.Leaves (P b)) → expand ρ B P :=
    fun i => ⟨GermBrick.mk ρ (expandedChart ρ B P i),Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j he
      exact chartPartition_injective ρ _ (expanded_partition ρ B P) (congrArg Subtype.val he)
    · intro c
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp c.property
      exact ⟨i,Subtype.ext hi⟩
  exact ⟨P,Equiv.ofBijective f hf,fun _ => rfl⟩

lemma exists_gauge {B C : Basis ρ} (F : Forest ρ B C) (i : F.Index) :
    ∃ a : A, chart ρ C (F.leaves i) = LocalEmbedding.comp ρ
      (expandedChart ρ B F.pattern i) (LocalEmbedding.global ρ a) := by
  apply (GermBrick.mk_eq_iff ρ _ _).mp
  rw [show GermBrick.mk ρ (chart ρ C (F.leaves i)) = (F.leaves i).val by
    exact GermBrick.mk_representative ρ _]
  exact (F.chart_eq i).symm

noncomputable def gauge {B C : Basis ρ} (F : Forest ρ B C) (i : F.Index) : A :=
  (F.exists_gauge i).choose

lemma gauge_spec {B C : Basis ρ} (F : Forest ρ B C) (i : F.Index) :
    chart ρ C (F.leaves i) = LocalEmbedding.comp ρ
      (expandedChart ρ B F.pattern i) (LocalEmbedding.global ρ (F.gauge i)) :=
  (F.exists_gauge i).choose_spec

noncomputable def compositePattern {B C D : Basis ρ} (F : Forest ρ B C) (K : Forest ρ C D)
    (b : B) : Pattern S :=
  Pattern.graft (F.pattern b) (fun i =>
    Pattern.relabel (ρ (F.gauge ⟨b,i⟩)) (K.pattern (F.leaves ⟨b,i⟩)))

noncomputable def compositeIndex {B C D : Basis ρ} (F : Forest ρ B C) (K : Forest ρ C D) :
    (Σ i : F.Index, Pattern.Leaves (K.pattern (F.leaves i))) ≃
      (Σ b : B, Pattern.Leaves (F.compositePattern K b)) :=
  (Equiv.sigmaCongrRight (fun i => Pattern.relabelLeaves (ρ (F.gauge i))
    (K.pattern (F.leaves i)))).trans
    ((Equiv.sigmaAssoc (fun b i => Pattern.Leaves
      (Pattern.relabel (ρ (F.gauge ⟨b,i⟩)) (K.pattern (F.leaves ⟨b,i⟩))))).trans
    (Equiv.sigmaCongrRight (fun b => Pattern.graftLeaves (F.pattern b)
      (fun i => Pattern.relabel (ρ (F.gauge ⟨b,i⟩)) (K.pattern (F.leaves ⟨b,i⟩))))))

lemma composite_chart {B C D : Basis ρ} (F : Forest ρ B C) (K : Forest ρ C D)
    (i : F.Index) (j : Pattern.Leaves (K.pattern (F.leaves i))) :
    GermBrick.mk ρ (expandedChart ρ B (F.compositePattern K) (F.compositeIndex K ⟨i,j⟩)) =
      GermBrick.mk ρ (expandedChart ρ C K.pattern ⟨F.leaves i,j⟩) := by
  change GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ B i.1)
    (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix _ (Pattern.graftLeaves (F.pattern i.1)
      (fun k => Pattern.relabel (ρ (F.gauge ⟨i.1,k⟩)) (K.pattern (F.leaves ⟨i.1,k⟩)))
      ⟨i.2,Pattern.relabelLeaves (ρ (F.gauge i)) (K.pattern (F.leaves i)) j⟩)))) = _
  rw [Pattern.graft_prefix,Pattern.relabel_prefix,LocalEmbedding.ofPrefix_append]
  change GermBrick.mk ρ _ = GermBrick.mk ρ
    (LocalEmbedding.comp ρ (chart ρ C (F.leaves i))
      (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix (K.pattern (F.leaves i)) j)))
  rw [F.gauge_spec,LocalEmbedding.comp_assoc,LocalEmbedding.global_ofPrefix]
  simp only [← LocalEmbedding.comp_assoc]
  rw [GermBrick.mk_gauge]
  rfl

noncomputable def trans {B C D : Basis ρ} (F : Forest ρ B C) (K : Forest ρ C D) : Forest ρ B D where
  pattern := F.compositePattern K
  leaves := (F.compositeIndex K).symm.trans ((Equiv.sigmaCongrLeft F.leaves).trans K.leaves)
  chart_eq := by
    intro k
    obtain ⟨⟨i,j⟩,rfl⟩ := (F.compositeIndex K).surjective k
    rw [F.composite_chart K i j]
    change GermBrick.mk ρ (expandedChart ρ C K.pattern ⟨F.leaves i,j⟩) =
      (K.leaves (Equiv.sigmaCongrLeft F.leaves
        ((F.compositeIndex K).symm (F.compositeIndex K ⟨i,j⟩)))).val
    rw [Equiv.symm_apply_apply]
    exact K.chart_eq ⟨F.leaves i,j⟩

end Forest

def CutRefines (B C : Basis ρ) : Prop := Nonempty (Forest ρ B C)

lemma cutRefines_refl (B : Basis ρ) : CutRefines ρ B B := ⟨Forest.refl B⟩
lemma cutRefines_trans {B C D : Basis ρ} (hBC : CutRefines ρ B C) (hCD : CutRefines ρ C D) :
    CutRefines ρ B D := by
  obtain ⟨F⟩ := hBC
  obtain ⟨K⟩ := hCD
  exact ⟨F.trans K⟩
lemma cutRefines_antisymm {B C : Basis ρ} (hBC : CutRefines ρ B C) (hCB : CutRefines ρ C B) : B = C :=
  le_antisymm hBC.some.refines hCB.some.refines
lemma le_of_cutRefines {B C : Basis ρ} (h : CutRefines ρ B C) : B ≤ C := h.some.refines

end Basis
end TwistedBrin

namespace TwistedBrin.Pattern
variable {S : Type u}

def uniform : List S → Pattern S
  | [] => .leaf
  | s :: L => .split s (uniform L) (uniform L)

lemma uniform_length [DecidableEq S] (L : List S) (i : Leaves (uniform L)) (s : S) :
    (leafPrefix (uniform L) i s).length = L.count s := by
  induction L with
  | nil => simp [uniform,leafPrefix]
  | cons t L ih =>
    cases i with
    | inl i =>
      change ((Prefix.cut t false).append (leafPrefix (uniform L) i) s).length = _
      rw [Prefix.append_apply,List.length_append,ih]
      by_cases h : t = s
      · subst t; simp [Prefix.cut_apply,Nat.add_comm]
      · simp [Prefix.cut_apply,h,Ne.symm h]
    | inr i =>
      change ((Prefix.cut t true).append (leafPrefix (uniform L) i) s).length = _
      rw [Prefix.append_apply,List.length_append,ih]
      by_cases h : t = s
      · subst t; simp [Prefix.cut_apply,Nat.add_comm]
      · simp [Prefix.cut_apply,h,Ne.symm h]

noncomputable def rectangular (b : S →₀ ℕ) : Pattern S :=
  uniform (Finsupp.toMultiset b).toList

lemma rectangular_length (b : S →₀ ℕ) (i : Leaves (rectangular b)) (s : S) :
    (leafPrefix (rectangular b) i s).length = b s := by
  classical
  have h := uniform_length (Finsupp.toMultiset b).toList i s
  rw [← Multiset.coe_count,Multiset.coe_toList,Finsupp.count_toMultiset] at h
  exact h

end TwistedBrin.Pattern

namespace TwistedBrin.Prefix
variable {S : Type u}

lemma eq_of_mem_of_length_eq {p q : Prefix S} {x : Box S}
    (hp : x ∈ p.brick) (hq : x ∈ q.brick) (hl : ∀ s, (p s).length = (q s).length) : p = q := by
  apply Prefix.ext
  intro s
  rw [← (mem_brick_iff p x).mp hp s,← (mem_brick_iff q x).mp hq s,hl]

lemma eq_gridPrefix_of_lengths {p : Prefix S} {b : S →₀ ℕ} (hl : ∀ s, (p s).length = b s)
    {x : Box S} (hx : x ∈ p.brick) : p = gridPrefix b (gridPoint b x) :=
  eq_of_mem_of_length_eq hx (mem_gridPrefix b x) (fun s => (hl s).trans (gridPrefix_length _ _ _).symm)

end TwistedBrin.Prefix

namespace TwistedBrin.Pattern
variable {S : Type u}

lemma rectangular_prefix (b : S →₀ ℕ) (i : Leaves (rectangular b)) :
    ∃ z : Prefix.Grid b, leafPrefix (rectangular b) i = Prefix.gridPrefix b z :=
  ⟨_,Prefix.eq_gridPrefix_of_lengths (rectangular_length b i)
    (Prefix.chart_mem_brick _ (fun _ _ => false))⟩

lemma exists_rectangular_leaf (b : S →₀ ℕ) (z : Prefix.Grid b) :
    ∃ i : Leaves (rectangular b), leafPrefix (rectangular b) i = Prefix.gridPrefix b z := by
  let x : Box S := (Prefix.gridPrefix b z).chart (fun _ _ => false)
  obtain ⟨i,hi,_⟩ := partition (rectangular b) x
  exact ⟨i,Prefix.eq_of_mem_of_length_eq hi (Prefix.chart_mem_brick _ _)
    (fun s => (rectangular_length b i s).trans (Prefix.gridPrefix_length b z s).symm)⟩

lemma rectangular_pieces (b : S →₀ ℕ) :
    pieces (rectangular b) = (by classical exact Finset.univ.image (Prefix.gridPrefix b)) := by
  classical
  ext p
  rw [mem_pieces,Finset.mem_image]
  constructor
  · rintro ⟨i,rfl⟩
    obtain ⟨z,hz⟩ := rectangular_prefix b i
    exact ⟨z,Finset.mem_univ _,hz.symm⟩
  · rintro ⟨z,_,rfl⟩
    exact exists_rectangular_leaf b z

end TwistedBrin.Pattern

namespace TwistedBrin
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace LocalEmbedding

lemma rectangular_standard (h : LocalEmbedding ρ) :
    ∃ w : S →₀ ℕ, ∀ i : Pattern.Leaves (Pattern.rectangular w),
      ∃ (q : Prefix S) (a : A),
        comp ρ h (ofPrefix ρ (Pattern.leafPrefix (Pattern.rectangular w) i)) =
          comp ρ (ofPrefix ρ q) (global ρ a) := by
  classical
  choose p q a hp he using h.locally_standard
  have hcover : (Set.univ : Set (Box S)) ⊆ ⋃ x, (p x).brick := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x,hp x⟩
  obtain ⟨I,hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (p x).brick) (fun x => (p x).isOpen_brick) hcover
  have hc : ∀ x, ∃ i ∈ I, x ∈ (p i).brick := by
    intro x
    simpa only [Set.mem_iUnion,exists_prop] using hI (Set.mem_univ x)
  obtain ⟨w,hw⟩ := finite_grid_refinement I p hc
  refine ⟨w,?_⟩
  intro j
  obtain ⟨z,hz⟩ := Pattern.rectangular_prefix w j
  obtain ⟨x,_,hx⟩ := hw z
  refine ⟨(q x).append (((p x).suffix (Prefix.gridPrefix w z)).permute (ρ (a x))),a x,?_⟩
  apply LocalEmbedding.ext
  intro y
  change h ((Pattern.leafPrefix (Pattern.rectangular w) j).chart y) = _
  rw [hz]
  nth_rw 1 [← Prefix.append_suffix hx]
  change h (((p x).append ((p x).suffix (Prefix.gridPrefix w z))).chart y) =
    ((q x).append (((p x).suffix (Prefix.gridPrefix w z)).permute (ρ (a x)))).chart
      (twist ρ (a x) y)
  have he' (x y) : h ((p x).chart y) = (q x).chart (twist ρ (a x) y) := he x y
  rw [Prefix.chart_append,he',twist_chart,← Prefix.chart_append]

end LocalEmbedding
namespace Basis
namespace Forest

noncomputable def of_mem {B C : Basis ρ} (P : B → Pattern S)
    (hm : ∀ i, GermBrick.mk ρ (expandedChart ρ B P i) ∈ C.pieces) : Forest ρ B C := by
  classical
  let f : (Σ b : B, Pattern.Leaves (P b)) → C := fun i => ⟨_,hm i⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      exact chartPartition_injective ρ _ (expanded_partition ρ B P) (congrArg Subtype.val hij)
    · intro c
      let x : Box S := chart ρ C c (fun _ _ => false)
      have hc : x ∈ GermBrick.region ρ c.val := by
        rw [← chart_region]
        exact ⟨_,rfl⟩
      obtain ⟨i,hi,_⟩ := expanded_partition ρ B P x
      have hfi : x ∈ GermBrick.region ρ (f i).val := hi
      exact ⟨i,(C.partition x).unique hfi hc⟩
  exact ⟨P,Equiv.ofBijective f hf,fun _ => rfl⟩

end Forest

lemma exists_standard_cut_patterns (B : Basis ρ) :
    ∃ P : B → Pattern S, ∀ i : Σ b : B, Pattern.Leaves (P b),
      ∃ (q : Prefix S) (a : A), expandedChart ρ B P i =
        LocalEmbedding.comp ρ (LocalEmbedding.ofPrefix ρ q) (LocalEmbedding.global ρ a) := by
  choose w hw using fun b : B => LocalEmbedding.rectangular_standard ρ (chart ρ B b)
  exact ⟨fun b => Pattern.rectangular (w b),fun i => hw i.1 i.2⟩

lemma cutRefines_grid_from_patterns (B : Basis ρ) (P : B → Pattern S)
    (q : (Σ b : B, Pattern.Leaves (P b)) → Prefix S)
    (a : (Σ b : B, Pattern.Leaves (P b)) → A)
    (he : ∀ i, expandedChart ρ B P i =
      LocalEmbedding.comp ρ (LocalEmbedding.ofPrefix ρ (q i)) (LocalEmbedding.global ρ (a i)))
    (w : S →₀ ℕ) (hw : ∀ i, (q i).lengths ≤ w) : CutRefines ρ B (grid ρ w) := by
  classical
  let R := fun i : Σ b : B, Pattern.Leaves (P b) =>
    Pattern.rectangular (w - (q i).lengths)
  let Q := fun b : B => Pattern.graft (P b)
    (fun j => Pattern.relabel (ρ (a ⟨b,j⟩)⁻¹) (R ⟨b,j⟩))
  apply Nonempty.intro
  apply Forest.of_mem ρ Q
  rintro ⟨b,k⟩
  obtain ⟨⟨j,l⟩,rfl⟩ := (Pattern.graftLeaves (P b)
    (fun j => Pattern.relabel (ρ (a ⟨b,j⟩)⁻¹) (R ⟨b,j⟩))).surjective k
  obtain ⟨l,rfl⟩ := (Pattern.relabelLeaves (ρ (a ⟨b,j⟩)⁻¹) (R ⟨b,j⟩)).surjective l
  let i : Σ b : B, Pattern.Leaves (P b) := ⟨b,j⟩
  let r := Pattern.leafPrefix (R i) l
  have hlen : ∀ s, ((q i).append r s).length = w s := by
    intro s
    change ((q i s) ++ (Pattern.leafPrefix (Pattern.rectangular (w - (q i).lengths)) l s)).length = w s
    rw [List.length_append,Pattern.rectangular_length,Finsupp.tsub_apply]
    exact Nat.add_sub_of_le (hw i s)
  obtain ⟨z,hz⟩ : ∃ z : Prefix.Grid w, (q i).append r = Prefix.gridPrefix w z :=
    ⟨_,Prefix.eq_gridPrefix_of_lengths hlen (Prefix.chart_mem_brick _ (fun _ _ => false))⟩
  have hc : GermBrick.mk ρ (expandedChart ρ B Q
      ⟨b,Pattern.graftLeaves (P b)
        (fun j => Pattern.relabel (ρ (a ⟨b,j⟩)⁻¹) (R ⟨b,j⟩))
        ⟨j,Pattern.relabelLeaves (ρ (a i)⁻¹) (R i) l⟩⟩) =
      GermBrick.mk ρ (LocalEmbedding.ofPrefix ρ ((q i).append r)) := by
    change GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ B b)
      (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix _ _))) = _
    rw [Pattern.graft_prefix,Pattern.relabel_prefix,LocalEmbedding.ofPrefix_append,
      ← LocalEmbedding.comp_assoc]
    change GermBrick.mk ρ (LocalEmbedding.comp ρ (expandedChart ρ B P i)
      (LocalEmbedding.ofPrefix ρ (r.permute (ρ (a i)⁻¹)))) = _
    rw [he,LocalEmbedding.comp_assoc,LocalEmbedding.global_ofPrefix,twist_prefix_inv,
      ← LocalEmbedding.comp_assoc,← LocalEmbedding.ofPrefix_append,GermBrick.mk_gauge]
  rw [hc,hz]
  exact mem_ofPartition ρ _ _ z

lemma has_cut_grid_refinement (B : Basis ρ) : ∃ w : S →₀ ℕ, CutRefines ρ B (grid ρ w) := by
  classical
  obtain ⟨P,hP⟩ := exists_standard_cut_patterns ρ B
  choose q a he using hP
  let w := ∑ i : Σ b : B, Pattern.Leaves (P b), (q i).lengths
  refine ⟨w,cutRefines_grid_from_patterns ρ B P q a he w ?_⟩
  intro i
  exact Finset.single_le_sum (f := fun i => (q i).lengths)
    (fun _ _ s => Nat.zero_le _) (Finset.mem_univ i)

end Basis
end TwistedBrin

namespace TwistedBrin.Basis
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma cut_grid_cofinal (B : Basis ρ) :
    ∃ w : S →₀ ℕ, ∀ t, w ≤ t → CutRefines ρ B (grid ρ t) := by
  classical
  obtain ⟨P,hP⟩ := exists_standard_cut_patterns ρ B
  choose q a he using hP
  let w := ∑ i : Σ b : B, Pattern.Leaves (P b), (q i).lengths
  refine ⟨w,fun t ht => cutRefines_grid_from_patterns ρ B P q a he t ?_⟩
  intro i
  exact le_trans (Finset.single_le_sum (f := fun i => (q i).lengths)
    (fun _ _ s => Nat.zero_le _) (Finset.mem_univ i)) ht

theorem cut_directed (B C : Basis ρ) :
    ∃ D : Basis ρ, CutRefines ρ B D ∧ CutRefines ρ C D := by
  obtain ⟨b,hb⟩ := cut_grid_cofinal ρ B
  obtain ⟨c,hc⟩ := cut_grid_cofinal ρ C
  exact ⟨grid ρ (b+c),hb _ (fun s => Nat.le_add_right _ _),
    hc _ (fun s => Nat.le_add_left _ _)⟩

end TwistedBrin.Basis

end

end OAI
