import Mathlib
import OAI.Algebra.GroupRing.TreeCentroid

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical BigOperators
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (ha : Function.Involutive α)
    (T : SimpleGraph (Cycle σ)) (hT : T≤graph σ α ha)
    (hz : GenusZero σ α) (ht : T.IsTree)
local notation "β" => subgraphPair σ α ha T hT
local notation "γ" => α*β
local notation "φ" => α*σ
local notation "hγ" => complement_involutive α β ha (subgraphPair_involutive σ α ha T hT)
  (subgraphPair_subpairing σ α ha T hT)
local notation "D" => graph φ γ hγ
local notation "htD" => spanning_cotree_isTree σ α ha T hT hz ht

def homeFace (v : Cycle σ) : Cycle φ := cycle φ (Quotient.out v)

omit [Fintype O] in
lemma home_cycle (v : Cycle σ) : cycle σ (Quotient.out v)=v := Quotient.out_eq v

def vertexSide (active : Finset (Cycle σ)) (d : O) : Finset (Cycle σ) :=
  active.filter (fun v=>homeFace σ α v∈cotreeSide σ α ha T hT hz ht d)

def centralDeleted (active : Finset (Cycle σ)) (root : Cycle σ) (c : Cycle φ) (d : O) :
    Finset (Cycle σ) :=
  active.filter (fun v=>homeFace σ α v=c ∧ v∈fundamentalVertices σ α T ht root d)

def pressure (active : Finset (Cycle σ)) (root : Cycle σ) (c : Cycle φ) (d : O) :
    Finset (Cycle σ) :=
  vertexSide σ α ha T hT hz ht active d ∪ centralDeleted σ α T ht active root c d

lemma pressure_subset (active : Finset (Cycle σ)) (root : Cycle σ) (c : Cycle φ) (d : O) :
    pressure σ α ha T hT hz ht active root c d⊆active :=
  Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)

lemma pressure_cover (active : Finset (Cycle σ)) (root : Cycle σ) (c : Cycle φ) :
    active⊆(members φ c).biUnion (pressure σ α ha T hT hz ht active root c) := by
  intro v hv
  by_cases he : homeFace σ α v=c
  · refine Finset.mem_biUnion.mpr ⟨Quotient.out v,(mem_members φ).mpr he,?_⟩
    apply Finset.mem_union_right
    refine Finset.mem_filter.mpr ⟨hv,he,?_⟩
    apply Finset.mem_union_left
    rw [home_cycle]
    exact TreeCentroid.self_mem_rootPath ht root v
  · have hn := TreeCentroid.next_adj htD (Ne.symm he)
    obtain ⟨_,d,hd,hd'⟩ := hn
    refine Finset.mem_biUnion.mpr ⟨d,(mem_members φ).mpr hd,?_⟩
    apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    refine ⟨hv,?_⟩
    change homeFace σ α v∈TreeCentroid.branch htD (cycle φ d) (cycle φ (γ d))
    rw [hd,hd']
    exact (TreeCentroid.mem_branch htD).mpr ⟨he,rfl⟩

/-- A weighted centroid face and at most three boundary occurrences force one
fundamental separator to remove or put on its small side at least one third
of the active vertices. Active vertices have unit cost; all others have zero. -/
theorem triangular_dart (active : Finset (Cycle σ)) (root : Cycle σ)
    (htri : ∀ c : Cycle φ,(members φ c).card≤3) :
    ∃ c : Cycle φ,∃ d∈members φ c,
      2*(vertexSide σ α ha T hT hz ht active d).card≤active.card ∧
      active.card≤3*(pressure σ α ha T hT hz ht active root c d).card := by
  let weight : Cycle φ→ℕ := fun c=>(active.filter (fun v=>homeFace σ α v=c)).card
  have hsum : ∑ c,weight c=active.card := by
    simpa only [weight,Finset.mem_univ,Finset.filter_true] using
      (Finset.sum_card_fiberwise_eq_card_filter active Finset.univ (homeFace σ α))
  obtain ⟨c,hc⟩ := TreeCentroid.exists_centroid htD weight
  obtain ⟨d,hd,hm⟩ := (members φ c).exists_max_image
    (fun d=>(pressure σ α ha T hT hz ht active root c d).card) (members_nonempty φ c)
  refine ⟨c,d,hd,?_,?_⟩
  · have hh := hc (cycle φ (γ d))
    rw [hsum] at hh
    have hf := Finset.sum_card_fiberwise_eq_card_filter active
      (cotreeSide σ α ha T hT hz ht d) (homeFace σ α)
    have hdc := (mem_members φ).mp hd
    change ∑ f∈cotreeSide σ α ha T hT hz ht d,weight f=
      (vertexSide σ α ha T hT hz ht active d).card at hf
    unfold cotreeSide at hf
    rw [hdc] at hf
    rwa [←hf]
  · have hb := (Finset.card_le_card (pressure_cover σ α ha T hT hz ht active root c)).trans
      (Finset.card_biUnion_le)
    have hm' := Finset.sum_le_sum (fun x hx=>hm x hx)
    have ht' := htri c
    simp only [Finset.sum_const,smul_eq_mul] at hm'
    exact hb.trans (hm'.trans (Nat.mul_le_mul_right _ ht'))

/-- The opposite retained side of a fundamental cut is disjoint from its
pressure set. -/
lemma opposite_disjoint_pressure (active : Finset (Cycle σ)) (root : Cycle σ)
    (c : Cycle φ) (d : O) :
    Disjoint (active.filter (fun v=>v∉fundamentalVertices σ α T ht root d ∧
      homeFace σ α v∉cotreeSide σ α ha T hT hz ht d))
      (pressure σ α ha T hT hz ht active root c d) := by
  apply Finset.disjoint_left.mpr
  intro v hv hp
  obtain ⟨_,hvC,hvS⟩ := Finset.mem_filter.mp hv
  rcases Finset.mem_union.mp hp with hp|hp
  · exact hvS (Finset.mem_filter.mp hp).2
  · exact hvC (Finset.mem_filter.mp hp).2.2

/-- The literal two-root-path separator balances both retained sides in a
triangular genus-zero map. This is the sharp bounded-radius crux; no planar
embedding or separator theorem is imported. -/
theorem triangular_balanced_fundamental (active : Finset (Cycle σ)) (root : Cycle σ)
    (htri : ∀ c : Cycle φ,(members φ c).card≤3) :
    ∃ d : O,
      3*(active.filter (fun v=>v∉fundamentalVertices σ α T ht root d ∧
        homeFace σ α v∈cotreeSide σ α ha T hT hz ht d)).card≤2*active.card ∧
      3*(active.filter (fun v=>v∉fundamentalVertices σ α T ht root d ∧
        homeFace σ α v∉cotreeSide σ α ha T hT hz ht d)).card≤2*active.card := by
  obtain ⟨c,d,_,hsmall,hlarge⟩ := triangular_dart σ α ha T hT hz ht active root htri
  refine ⟨d,?_,?_⟩
  · have hsub : active.filter (fun v=>v∉fundamentalVertices σ α T ht root d ∧
        homeFace σ α v∈cotreeSide σ α ha T hT hz ht d)⊆
        vertexSide σ α ha T hT hz ht active d := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).1,(Finset.mem_filter.mp hv).2.2⟩
    have hh := Finset.card_le_card hsub
    omega
  · have hsub : (active.filter (fun v=>v∉fundamentalVertices σ α T ht root d ∧
        homeFace σ α v∉cotreeSide σ α ha T hT hz ht d)) ∪
        pressure σ α ha T hT hz ht active root c d⊆active :=
      Finset.union_subset (Finset.filter_subset _ _)
        (pressure_subset σ α ha T hT hz ht active root c d)
    have hh := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint (opposite_disjoint_pressure σ α ha T hT hz ht active root c d)] at hh
    omega

end TorsionFreeZeroDivisors.MapEuler

namespace TorsionFreeZeroDivisors.ConedMap

section
open scoped Classical BigOperators
open PermutationCycles MapEuler
variable {O : Type} (σ α : Equiv.Perm O)

/-- Original darts plus one radial pair for each face corner. Radial true is
at the new face center, radial false at the original vertex. -/
abbrev Dart (O : Type) := O ⊕ (O × Bool)
def old (x : O) : Dart O := .inl x
def radial (x : O) : Dart O := .inr (x,false)
def center (x : O) : Dart O := .inr (x,true)

def rotation : Equiv.Perm (Dart O) where
  toFun
    | .inl x => radial x
    | .inr (x,false) => old (σ x)
    | .inr (x,true) => center ((α*σ).symm x)
  invFun
    | .inl x => radial (σ.symm x)
    | .inr (x,false) => old x
    | .inr (x,true) => center ((α*σ) x)
  left_inv := by
    rintro (x|⟨x,b⟩)
    · rfl
    · cases b
      · exact congrArg radial (σ.symm_apply_apply x)
      · exact congrArg center ((α*σ).apply_symm_apply x)
  right_inv := by
    rintro (x|⟨x,b⟩)
    · exact congrArg old (σ.apply_symm_apply x)
    · cases b
      · rfl
      · exact congrArg center ((α*σ).symm_apply_apply x)

def pairing : Equiv.Perm (Dart O) := Equiv.sumCongr α (Equiv.prodCongr (Equiv.refl O) Equiv.boolNot)

@[simp] lemma rotation_old (x : O) : rotation σ α (old x)=radial x := rfl
@[simp] lemma rotation_radial (x : O) : rotation σ α (radial x)=old (σ x) := rfl
@[simp] lemma rotation_center (x : O) : rotation σ α (center x)=center ((α*σ).symm x) := rfl
@[simp] lemma pairing_old (x : O) : pairing α (old x)=old (α x) := rfl
@[simp] lemma pairing_radial (x : O) : pairing α (radial x)=center x := rfl
@[simp] lemma pairing_center (x : O) : pairing α (center x)=radial x := rfl

lemma pairing_involutive (ha : Function.Involutive α) : Function.Involutive (pairing α) := by
  rintro (x|⟨x,b⟩)
  · change old (α (α x))=old x
    rw [ha]
  · cases b <;> rfl

local notation "ρ" => rotation σ α
local notation "π" => pairing α
local notation "φ" => α*σ
local notation "ψ" => π*ρ

@[simp] lemma face_old (x : O) : ψ (old x)=center x := rfl
@[simp] lemma face_center (x : O) : ψ (center x)=radial ((α*σ).symm x) := rfl
@[simp] lemma face_radial (x : O) : ψ (radial x)=old (φ x) := rfl

lemma vertex_radial (x : O) : cycle ρ (radial x)=cycle ρ (old x) := cycle_apply ρ (old x)
lemma vertex_old_apply (x : O) : cycle ρ (old (σ x))=cycle ρ (old x) :=
  (cycle_apply ρ (radial x)).trans (vertex_radial σ α x)
lemma vertex_center_apply (x : O) : cycle ρ (center (φ x))=cycle ρ (center x) := by
  have h := cycle_apply ρ (center (φ x))
  simpa only [rotation_center,Equiv.symm_apply_apply] using h.symm

/-- Literal vertex classification: original vertices and the inserted face centers. -/
def vertexRaw : Dart O → Cycle σ ⊕ Cycle φ
  | .inl x => .inl (cycle σ x)
  | .inr (x,false) => .inl (cycle σ x)
  | .inr (x,true) => .inr (cycle φ x)
lemma vertexRaw_invariant (x : Dart O) : vertexRaw σ α (ρ x)=vertexRaw σ α x := by
  rcases x with x|⟨x,b⟩
  · rfl
  · cases b
    · exact congrArg Sum.inl (cycle_apply σ x)
    · change Sum.inr (cycle φ ((α*σ).symm x))=Sum.inr (cycle φ x)
      rw [←cycle_apply φ ((α*σ).symm x),(α*σ).apply_symm_apply]

variable [Fintype O]

def vertices : Cycle ρ → Cycle σ ⊕ Cycle φ :=
  PermutationCycles.lift ρ (vertexRaw σ α) (vertexRaw_invariant σ α)
def vertexInverse : Cycle σ ⊕ Cycle φ → Cycle ρ
  | .inl v=>PermutationCycles.lift σ (fun x=>cycle ρ (old x)) (vertex_old_apply σ α) v
  | .inr f=>PermutationCycles.lift φ (fun x=>cycle ρ (center x)) (vertex_center_apply σ α) f
lemma vertices_right_inverse : Function.RightInverse (vertexInverse σ α) (vertices σ α) := by
  rintro (v|f)
  · obtain ⟨x,rfl⟩ := cycle_surjective σ v
    rfl
  · obtain ⟨x,rfl⟩ := cycle_surjective φ f
    rfl
lemma vertices_left_inverse : Function.LeftInverse (vertexInverse σ α) (vertices σ α) := by
  intro v
  obtain ⟨x,rfl⟩ := cycle_surjective ρ v
  rcases x with x|⟨x,b⟩
  · rfl
  · cases b
    · exact (vertex_radial σ α x).symm
    · rfl

def vertexEquiv : Cycle ρ≃Cycle σ ⊕ Cycle φ :=
  ⟨vertices σ α,vertexInverse σ α,vertices_left_inverse σ α,vertices_right_inverse σ α⟩

@[simp] lemma vertexEquiv_old (x : O) : vertexEquiv σ α (cycle ρ (old x))=.inl (cycle σ x) := rfl
@[simp] lemma vertexEquiv_radial (x : O) : vertexEquiv σ α (cycle ρ (radial x))=.inl (cycle σ x) := rfl
@[simp] lemma vertexEquiv_center (x : O) : vertexEquiv σ α (cycle ρ (center x))=.inr (cycle φ x) := rfl

/-- Each coned face is the actual three-cycle old--center--radial. -/
def faceRaw : Dart O → O
  | .inl x=>x
  | .inr (x,false)=>φ x
  | .inr (x,true)=>x
omit [Fintype O] in
lemma faceRaw_invariant (x : Dart O) : faceRaw σ α (ψ x)=faceRaw σ α x := by
  rcases x with x|⟨x,b⟩
  · rfl
  · cases b
    · rfl
    · exact (α*σ).apply_symm_apply x

def faces : Cycle ψ→O := PermutationCycles.lift ψ (faceRaw σ α) (faceRaw_invariant σ α)
omit [Fintype O] in
lemma face_cycle_center (x : O) : cycle ψ (center x)=cycle ψ (old x) := cycle_apply ψ (old x)
omit [Fintype O] in
lemma face_cycle_radial (x : O) : cycle ψ (radial x)=cycle ψ (old (φ x)) :=
  (cycle_apply ψ (radial x)).symm
lemma faces_left_inverse : Function.LeftInverse (fun x=>cycle ψ (old x)) (faces σ α) := by
  intro f
  obtain ⟨x,rfl⟩ := cycle_surjective ψ f
  rcases x with x|⟨x,b⟩
  · rfl
  · cases b
    · exact (face_cycle_radial σ α x).symm
    · exact (face_cycle_center σ α x).symm

def faceEquiv : Cycle ψ≃O :=
  ⟨faces σ α,fun x=>cycle ψ (old x),faces_left_inverse σ α,fun _=>rfl⟩

lemma face_members (x : O) : members ψ (cycle ψ (old x))={old x,center x,radial ((α*σ).symm x)} := by
  ext y
  rw [mem_members]
  constructor
  · intro hy
    have hh := congrArg (faceEquiv σ α) hy
    rcases y with y|⟨y,b⟩
    · change y=x at hh
      subst y
      exact Finset.mem_insert_self _ _
    · cases b
      · change φ y=x at hh
        have he : y=(α*σ).symm x := (α*σ).injective (hh.trans ((α*σ).apply_symm_apply x).symm)
        subst y
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      · change y=x at hh
        subst y
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  · intro hy
    simp only [Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with rfl|rfl|rfl
    · rfl
    · exact face_cycle_center σ α x
    · rw [face_cycle_radial,(α*σ).apply_symm_apply]

lemma triangular (f : Cycle ψ) : (members ψ f).card=3 := by
  obtain ⟨x,rfl⟩ := (faceEquiv σ α).symm.surjective f
  change (members ψ (cycle ψ (old x))).card=3
  rw [face_members]
  simp [old,center,radial]

lemma vertex_count : Nat.card (Cycle ρ)=Nat.card (Cycle σ)+Nat.card (Cycle φ) := by
  rw [Nat.card_congr (vertexEquiv σ α),Nat.card_sum]
lemma face_count : Nat.card (Cycle ψ)=Nat.card O := Nat.card_congr (faceEquiv σ α)

end

open scoped Classical
open PermutationCycles MapEuler
variable {O : Type} (σ α : Equiv.Perm O)
local notation "ρ" => rotation σ α
local notation "π" => pairing α
local notation "φ" => α*σ

lemma component_face (x : O) : component σ α ((α*σ) x)=component σ α x :=
  (component_partner σ α (σ x)).trans (component_rotation σ α x)

def componentRaw : Dart O → Component σ α
  | .inl x=>component σ α x
  | .inr (x,_)=>component σ α x
lemma componentRaw_rotation (x : Dart O) : componentRaw σ α (ρ x)=componentRaw σ α x := by
  rcases x with x|⟨x,b⟩
  · rfl
  · cases b
    · exact component_rotation σ α x
    · change component σ α ((α*σ).symm x)=component σ α x
      rw [←component_face σ α ((α*σ).symm x),(α*σ).apply_symm_apply]
lemma componentRaw_pairing (x : Dart O) : componentRaw σ α (π x)=componentRaw σ α x := by
  rcases x with x|⟨x,b⟩
  · exact component_partner σ α x
  · cases b <;> rfl

def componentForward : Component ρ π→ Component σ α :=
  MapEuler.lift ρ π (componentRaw σ α) (componentRaw_rotation σ α) (componentRaw_pairing σ α)
lemma component_radial (x : O) : component ρ π (radial x)=component ρ π (old x) :=
  component_rotation ρ π (old x)
lemma component_center (x : O) : component ρ π (center x)=component ρ π (old x) :=
  (component_partner ρ π (radial x)).trans (component_radial σ α x)
lemma component_old_rotation (x : O) : component ρ π (old (σ x))=component ρ π (old x) :=
  (component_rotation ρ π (radial x)).trans (component_radial σ α x)
lemma component_old_pairing (x : O) : component ρ π (old (α x))=component ρ π (old x) :=
  component_partner ρ π (old x)
def componentInverse : Component σ α→ Component ρ π :=
  MapEuler.lift σ α (fun x=>component ρ π (old x))
    (component_old_rotation σ α) (component_old_pairing σ α)

def componentEquiv : Component ρ π≃Component σ α where
  toFun := componentForward σ α
  invFun := componentInverse σ α
  left_inv := by
    intro c
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
    rcases x with x|⟨x,b⟩
    · rfl
    · cases b
      · exact (component_radial σ α x).symm
      · exact (component_center σ α x).symm
  right_inv := by
    intro c
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
    rfl

variable [Fintype O]

def supportEquiv : ↥(pairing α).support ≃ ↥α.support ⊕ (O×Bool) where
  toFun x := match x with
    | ⟨.inl y,hy⟩=>.inl ⟨y,by
        apply Equiv.Perm.mem_support.mpr
        intro he
        exact Equiv.Perm.mem_support.mp hy (congrArg old he)⟩
    | ⟨.inr y,_⟩=>.inr y
  invFun
    | .inl y=>⟨old y.val,by
        apply Equiv.Perm.mem_support.mpr
        intro he
        exact Equiv.Perm.mem_support.mp y.property (Sum.inl.inj he)⟩
    | .inr (x,b)=>⟨.inr (x,b),by
        apply Equiv.Perm.mem_support.mpr
        cases b <;> simp [pairing,Equiv.sumCongr_apply,Equiv.prodCongr_apply]⟩
  left_inv := by
    rintro ⟨x,hx⟩
    rcases x with x|⟨x,b⟩ <;> rfl
  right_inv := by
    rintro (x|⟨x,b⟩) <;> rfl

lemma support_count : (pairing α).support.card=α.support.card+2*Nat.card O := by
  have h := Fintype.card_congr (supportEquiv α)
  simp only [Fintype.card_coe,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool] at h
  rw [←Nat.card_eq_fintype_card] at h
  omega

omit [Fintype O] in
lemma support_card_nat {X : Type} [Fintype X] [DecidableEq X] (p : Equiv.Perm X) :
    p.support.card=Nat.card {x : X // p x≠x} := by
  rw [←Fintype.card_coe,←Nat.card_eq_fintype_card]
  exact Nat.card_congr
    ⟨fun x=>⟨x.val,Equiv.Perm.mem_support.mp x.property⟩,
     fun x=>⟨x.val,Equiv.Perm.mem_support.mpr x.property⟩,
     fun _=>rfl,fun _=>rfl⟩

/-- Coning all literal face cycles preserves Euler genus zero, with no
geometric embedding premise and without identifying or deleting any original vertex. -/
theorem genusZero (hz : GenusZero σ α) : GenusZero ρ π := by
  classical
  have hv := vertex_count σ α
  have hf := face_count σ α
  have hc := Nat.card_congr (componentEquiv σ α)
  have hs := support_count α
  unfold GenusZero at hz ⊢
  rw [hv,hf,hc]
  simp only [support_card_nat] at hz hs ⊢
  omega

end TorsionFreeZeroDivisors.ConedMap

end

end OAI
