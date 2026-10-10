import Mathlib
import OAI.GroupTheory.FiniteType.TwistedBrinRangeChartRestricts

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
namespace TwistedBrin.Basis
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

noncomputable def vertexStabilizer (B : Basis ρ) : Subgroup (localGroup ρ) :=
  MulAction.stabilizer (localGroup ρ) B

lemma rigid_le_vertexStabilizer (B : Basis ρ) : rigidStabilizer ρ B ≤ vertexStabilizer ρ B := by
  intro g hg
  apply MulAction.mem_stabilizer_iff.mpr
  apply Basis.ext
  change B.pieces.map (GermBrick.groupEquiv ρ g).toEmbedding = B.pieces
  apply Finset.ext
  intro b
  constructor
  · intro hb
    obtain ⟨c,hc,rfl⟩ := Finset.mem_map.mp hb
    change GermBrick.groupEquiv ρ g c ∈ B.pieces
    rw [hg ⟨c,hc⟩]
    exact hc
  · intro hb
    exact Finset.mem_map.mpr ⟨b,hb,hg ⟨b,hb⟩⟩

lemma vertex_mem_iff (B : Basis ρ) (g : vertexStabilizer ρ B) (b : GermBrick ρ) :
    b ∈ B.pieces ↔ GermBrick.groupEquiv ρ g.val b ∈ B.pieces := by
  have he : B.pieces.map (GermBrick.groupEquiv ρ g.val).toEmbedding = B.pieces :=
    congrArg Basis.pieces (MulAction.mem_stabilizer_iff.mp g.property)
  constructor
  · intro hb
    rw [← he]
    exact Finset.mem_map.mpr ⟨b,hb,rfl⟩
  · intro hb
    rw [← he] at hb
    obtain ⟨c,hc,hcb⟩ := Finset.mem_map.mp hb
    have hh : c = b := (GermBrick.groupEquiv ρ g.val).injective hcb
    exact hh ▸ hc

noncomputable def vertexPermutationHom (B : Basis ρ) : vertexStabilizer ρ B →* Equiv.Perm B where
  toFun g := (GermBrick.groupEquiv ρ g.val).subtypeEquiv (vertex_mem_iff ρ B g)
  map_one' := by
    apply Equiv.ext
    intro b
    apply Subtype.ext
    exact congrArg (fun e : Equiv.Perm (GermBrick ρ) => e b.1) ((GermBrick.action ρ).map_one)
  map_mul' g h := by
    apply Equiv.ext
    intro b
    apply Subtype.ext
    exact congrArg (fun e : Equiv.Perm (GermBrick ρ) => e b.1)
      ((GermBrick.action ρ).map_mul g.val h.val)

lemma vertexPermutationHom_apply (B : Basis ρ) (g : vertexStabilizer ρ B) (b : B) :
    ((vertexPermutationHom ρ B g) b).1 = GermBrick.groupEquiv ρ g.val b.1 := rfl

lemma mem_vertexPermutationHom_ker (B : Basis ρ) (g : vertexStabilizer ρ B) :
    g ∈ (vertexPermutationHom ρ B).ker ↔ g.val ∈ rigidStabilizer ρ B := by
  change vertexPermutationHom ρ B g = 1 ↔ ∀ b : B, _
  constructor
  · intro hg b
    exact congrArg (fun e : Equiv.Perm B => (e b).1) hg
  · intro hg
    apply Equiv.ext
    intro b
    exact Subtype.ext (hg b)

noncomputable def twistPiecesToVertex (B : Basis ρ) : (B → A) →* vertexStabilizer ρ B :=
  (twistPiecesHom ρ B).codRestrict _ (fun a => rigid_le_vertexStabilizer ρ B
    (twistPiecesHom_mem_rigidStabilizer ρ B a))

noncomputable def twistPiecesToKernel (B : Basis ρ) : (B → A) →* (vertexPermutationHom ρ B).ker :=
  (twistPiecesToVertex ρ B).codRestrict _ (fun a => (mem_vertexPermutationHom_ker ρ B _).mpr
    (twistPiecesHom_mem_rigidStabilizer ρ B a))

noncomputable def vertexKernelEquiv (hρ : Function.Injective ρ) (B : Basis ρ) :
    (B → A) ≃* (vertexPermutationHom ρ B).ker :=
  MulEquiv.ofBijective (twistPiecesToKernel ρ B) ⟨fun _ _ he =>
    twistPiecesHom_injective ρ hρ B (congrArg (fun x => x.val.val) he), by
      intro g
      have hg := (mem_vertexPermutationHom_ker ρ B g.val).mp g.property
      obtain ⟨a,ha⟩ := exists_twistPiecesHom_of_mem ρ hg
      exact ⟨a,Subtype.ext (Subtype.ext ha)⟩⟩

instance vertexPermutationHom_ker_finiteIndex (B : Basis ρ) :
    (vertexPermutationHom ρ B).ker.FiniteIndex := by
  classical
  exact Subgroup.finiteIndex_ker _

end TwistedBrin.Basis

namespace TwistedBrin.Prefix
variable {S : Type u}
open scoped Classical

noncomputable def cut (s : S) (b : Bool) : Prefix S := by
  classical
  exact ⟨fun t => if t = s then [b] else [],(Set.finite_singleton s).subset (by
    intro t ht
    by_contra hn
    simp only [Set.mem_singleton_iff] at hn
    simp only [Set.mem_ofPred_eq,ite_eq_right hn,ne_eq,not_true_eq_false] at ht)⟩

@[simp] lemma cut_apply (s t : S) (b : Bool) : cut s b t = if t = s then [b] else [] := by
  classical
  rfl

lemma mem_cut_iff (s : S) (b : Bool) (x : Box S) : x ∈ (cut s b).brick ↔ (x s).get 0 = b := by
  classical
  rw [mem_brick_iff_get]
  constructor
  · intro h
    simpa [cut_apply] using h s 0 (by simp)
  · intro h t n hn
    by_cases ht : t = s
    · subst t
      have hn' : n < 1 := by simpa [cut_apply] using hn
      have he : n = 0 := by omega
      subst n
      simpa [cut_apply] using h
    · simp only [cut_apply,ite_eq_right ht,List.length_nil] at hn
      omega

lemma mem_append_iff (p q : Prefix S) (x : Box S) : x ∈ (p.append q).brick ↔
    x ∈ p.brick ∧ p.tail x ∈ q.brick := by
  constructor
  · rintro ⟨y,rfl⟩
    rw [chart_append]
    exact ⟨chart_mem_brick _ _,by rw [tail_chart]; exact chart_mem_brick _ _⟩
  · rintro ⟨hp,y,hy⟩
    refine ⟨y,?_⟩
    rw [chart_append,hy,chart_tail hp]

end TwistedBrin.Prefix

namespace TwistedBrin

inductive Pattern (S : Type u)
  | leaf
  | split (s : S) (left right : Pattern S)

namespace Pattern
variable {S : Type u}

def Leaves : Pattern S → Type
  | .leaf => Unit
  | .split _ P Q => Leaves P ⊕ Leaves Q

instance leavesFintype : (P : Pattern S) → Fintype (Leaves P)
  | .leaf => inferInstanceAs (Fintype Unit)
  | .split _ P Q => by
    letI := leavesFintype P
    letI := leavesFintype Q
    exact inferInstanceAs (Fintype (Leaves P ⊕ Leaves Q))

noncomputable def leafPrefix : (P : Pattern S) → Leaves P → Prefix S
  | .leaf, _ => Prefix.empty
  | .split s P _, .inl i => (Prefix.cut s false).append (leafPrefix P i)
  | .split s _ Q, .inr i => (Prefix.cut s true).append (leafPrefix Q i)

lemma split_prefix_nonempty (s : S) (P Q : Pattern S) (i : Leaves (.split s P Q)) :
    leafPrefix (.split s P Q) i s ≠ [] := by
  classical
  cases i with
  | inl i => simp [leafPrefix]
  | inr i => simp [leafPrefix]

lemma partition (P : Pattern S) : ∀ x : Box S, ∃! i : Leaves P, x ∈ (leafPrefix P i).brick := by
  induction P with
  | leaf =>
    intro x
    exact ⟨(),by simp [leafPrefix],fun i _ => by cases i; rfl⟩
  | split s P Q hP hQ =>
    intro x
    cases hx : (x s).get 0 with
    | false =>
      obtain ⟨i,hi,hu⟩ := hP ((Prefix.cut s false).tail x)
      refine ⟨Sum.inl i,?_,?_⟩
      · exact (Prefix.mem_append_iff _ _ _).mpr ⟨(Prefix.mem_cut_iff _ _ _).mpr hx,hi⟩
      · intro j hj
        cases j with
        | inl j =>
          exact congrArg Sum.inl (hu j ((Prefix.mem_append_iff _ _ _).mp hj).2)
        | inr j =>
          have hf := (Prefix.mem_cut_iff s true x).mp ((Prefix.mem_append_iff _ _ _).mp hj).1
          simp only [hx,Bool.false_eq_true] at hf
    | true =>
      obtain ⟨i,hi,hu⟩ := hQ ((Prefix.cut s true).tail x)
      refine ⟨Sum.inr i,?_,?_⟩
      · exact (Prefix.mem_append_iff _ _ _).mpr ⟨(Prefix.mem_cut_iff _ _ _).mpr hx,hi⟩
      · intro j hj
        cases j with
        | inr j =>
          exact congrArg Sum.inr (hu j ((Prefix.mem_append_iff _ _ _).mp hj).2)
        | inl j =>
          have hf := (Prefix.mem_cut_iff s false x).mp ((Prefix.mem_append_iff _ _ _).mp hj).1
          simp only [hx,Bool.true_eq_false] at hf

lemma leafPrefix_injective (P : Pattern S) : Function.Injective (leafPrefix P) := by
  intro i j hij
  let x : Box S := (leafPrefix P i).chart (fun _ _ => false)
  have hi : x ∈ (leafPrefix P i).brick := Prefix.chart_mem_brick _ _
  have hj : x ∈ (leafPrefix P j).brick := hij ▸ hi
  exact (partition P x).unique hi hj

noncomputable def pieces (P : Pattern S) : Finset (Prefix S) := by
  classical
  exact Finset.univ.image (leafPrefix P)

lemma mem_pieces (P : Pattern S) (p : Prefix S) : p ∈ pieces P ↔ ∃ i, leafPrefix P i = p := by
  classical
  simp only [pieces,Finset.mem_image,Finset.mem_univ,true_and]

lemma pieces_split_nonempty (s : S) (P Q : Pattern S) {p : Prefix S}
    (hp : p ∈ pieces (.split s P Q)) : p s ≠ [] := by
  obtain ⟨i,rfl⟩ := (mem_pieces _ _).mp hp
  exact split_prefix_nonempty s P Q i

end Pattern
end TwistedBrin

namespace TwistedBrin.UnslicedPartition

def data : Fin 5 → Fin 3 → Option Bool :=
  ![![some false,some false,none],![none,some true,some false],
    ![some true,none,some true],![some false,some true,some true],
    ![some true,some false,some false]]

lemma boolean_partition : ∀ x : Fin 3 → Bool, ∃! i : Fin 5,
    ∀ s b, data i s = some b → x s = b := by
  unfold ExistsUnique
  exact @of_decide_eq_true _ Fintype.decidableForallFintype rfl

lemma missing_coordinate : ∀ s : Fin 3, ∃ i : Fin 5, data i s = none := by decide
lemma data_injective : Function.Injective data := by decide

noncomputable def tile (i : Fin 5) : Prefix (Fin 3) where
  word s := (data i s).toList
  finite_support := Set.toFinite _

lemma mem_tile_iff (i : Fin 5) (x : Box (Fin 3)) : x ∈ (tile i).brick ↔
    ∀ s b, data i s = some b → (x s).get 0 = b := by
  rw [Prefix.mem_brick_iff_get]
  constructor
  · intro h s b hb
    have he : tile i s = [b] := by change (data i s).toList = _; rw [hb]; rfl
    simpa only [he,List.getElem_cons_zero] using h s 0 (by simp only [he,List.length_singleton]; omega)
  · intro h s n hn
    cases he : data i s with
    | none =>
      have he' : tile i s = [] := by change (data i s).toList = _; rw [he]; rfl
      simp only [he',List.length_nil] at hn
      omega
    | some b =>
      have he' : tile i s = [b] := by change (data i s).toList = _; rw [he]; rfl
      have hn' : n < 1 := by simpa only [he',List.length_singleton] using hn
      have hz : n = 0 := by omega
      subst n
      simpa only [he',List.getElem_cons_zero] using h s b he

lemma tile_partition : IsPartition tile := by
  intro x
  obtain ⟨i,hi,hu⟩ := boolean_partition (fun s => (x s).get 0)
  exact ⟨i,(mem_tile_iff i x).mpr hi,fun j hj => hu j ((mem_tile_iff j x).mp hj)⟩

noncomputable def pieces : Finset (Prefix (Fin 3)) := by
  classical
  exact Finset.univ.image tile

lemma all_tiles_mem (i : Fin 5) : tile i ∈ pieces := by
  classical
  exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

lemma tile_injective : Function.Injective tile := by
  intro i j hij
  apply data_injective
  funext s
  have hh := congrArg (fun p : Prefix (Fin 3) => p s) hij
  change (data i s).toList = (data j s).toList at hh
  cases hi : data i s <;> cases hj : data j s <;> simp_all

lemma card_pieces : pieces.card = 5 := by
  classical
  rw [pieces,Finset.card_image_of_injective _ tile_injective]
  rfl

lemma no_binary_pattern (P : Pattern (Fin 3)) : Pattern.pieces P ≠ pieces := by
  intro he
  cases P with
  | leaf =>
    have hc := congrArg Finset.card he
    have hl : (Pattern.pieces (Pattern.leaf : Pattern (Fin 3))).card = 1 := by
      classical
      change (Finset.univ.image (fun _ : Unit => (Prefix.empty : Prefix (Fin 3)))).card = 1
      simp
    rw [hl,card_pieces] at hc
    omega
  | split s P Q =>
    obtain ⟨i,hi⟩ := missing_coordinate s
    have hp : tile i ∈ Pattern.pieces (.split s P Q) := he.symm ▸ all_tiles_mem i
    have hn := Pattern.pieces_split_nonempty s P Q hp
    apply hn
    change (data i s).toList = []
    rw [hi]
    rfl

end TwistedBrin.UnslicedPartition

namespace TwistedBrin.Prefix

def inflate {n : ℕ} (p : Prefix (Fin n)) : Prefix ℕ where
  word s := if hs : s < n then p ⟨s,hs⟩ else []
  finite_support := (Finset.range n).finite_toSet.subset (by
    intro s hs
    change s ∈ Finset.range n
    by_contra hn
    have hn' : ¬s < n := by simpa only [Finset.mem_range] using hn
    simp only [Set.mem_ofPred_eq,dite_eq_right hn',ne_eq,not_true_eq_false] at hs)

lemma inflate_apply {n : ℕ} (p : Prefix (Fin n)) (s : ℕ) :
    inflate p s = if hs : s < n then p ⟨s,hs⟩ else [] := rfl

lemma inflate_injective {n : ℕ} : Function.Injective (inflate (n := n)) := by
  intro p q hpq
  apply Prefix.ext
  intro s
  have he := congrArg (fun p : Prefix ℕ => p s.val) hpq
  simpa only [inflate_apply,dite_eq_left s.isLt] using he

lemma mem_inflate_iff {n : ℕ} (p : Prefix (Fin n)) (x : Box ℕ) :
    x ∈ (inflate p).brick ↔ (fun s : Fin n => x s.val) ∈ p.brick := by
  simp only [mem_brick_iff_get]
  constructor
  · intro h s k hk
    have he : inflate p s.val = p s := by rw [inflate_apply,dite_eq_left s.isLt]
    simpa only [he] using h s.val k (by rw [he]; exact hk)
  · intro h s k hk
    by_cases hs : s < n
    · have he : inflate p s = p ⟨s,hs⟩ := by rw [inflate_apply,dite_eq_left hs]
      simpa only [he] using h ⟨s,hs⟩ k (by rwa [he] at hk)
    · have he : inflate p s = [] := by rw [inflate_apply,dite_eq_right hs]
      simp only [he,List.length_nil] at hk
      omega

end TwistedBrin.Prefix

namespace TwistedBrin.UnslicedPartition

noncomputable def infiniteTile (i : Fin 5) : Prefix ℕ := Prefix.inflate (tile i)

lemma infiniteTile_partition : IsPartition infiniteTile := by
  intro x
  obtain ⟨i,hi,hu⟩ := tile_partition (fun s => x s.val)
  exact ⟨i,(Prefix.mem_inflate_iff _ _).mpr hi,fun j hj => hu j ((Prefix.mem_inflate_iff _ _).mp hj)⟩

lemma infiniteTile_injective : Function.Injective infiniteTile :=
  Prefix.inflate_injective.comp tile_injective

lemma infiniteTile_missing (s : ℕ) : ∃ i : Fin 5, infiniteTile i s = [] := by
  by_cases hs : s < 3
  · obtain ⟨i,hi⟩ := missing_coordinate ⟨s,hs⟩
    refine ⟨i,?_⟩
    rw [infiniteTile,Prefix.inflate_apply,dite_eq_left hs]
    change (data i ⟨s,hs⟩).toList = []
    rw [hi]
    rfl
  · exact ⟨0,by rw [infiniteTile,Prefix.inflate_apply,dite_eq_right hs]⟩

noncomputable def infinitePieces : Finset (Prefix ℕ) := by
  classical
  exact Finset.univ.image infiniteTile

lemma infiniteTile_mem (i : Fin 5) : infiniteTile i ∈ infinitePieces := by
  classical
  exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

lemma card_infinitePieces : infinitePieces.card = 5 := by
  classical
  rw [infinitePieces,Finset.card_image_of_injective _ infiniteTile_injective]
  rfl

lemma no_binary_pattern_infinite (P : Pattern ℕ) : Pattern.pieces P ≠ infinitePieces := by
  intro he
  cases P with
  | leaf =>
    have hc := congrArg Finset.card he
    have hl : (Pattern.pieces (Pattern.leaf : Pattern ℕ)).card = 1 := by
      classical
      change (Finset.univ.image (fun _ : Unit => (Prefix.empty : Prefix ℕ))).card = 1
      simp
    rw [hl,card_infinitePieces] at hc
    omega
  | split s P Q =>
    obtain ⟨i,hi⟩ := infiniteTile_missing s
    have hp : infiniteTile i ∈ Pattern.pieces (.split s P Q) := he.symm ▸ infiniteTile_mem i
    exact Pattern.pieces_split_nonempty s P Q hp hi

variable {A : Type v} [Group A] (ρ : A →* Equiv.Perm ℕ)

noncomputable def basis : Basis ρ := Basis.ofPartition ρ infiniteTile infiniteTile_partition

lemma trivial_le_basis : Basis.trivial ρ ≤ basis ρ := by
  intro c
  obtain ⟨i,hi⟩ := Basis.exists_prefix_of_mem_ofPartition ρ _ _ c
  refine ⟨⟨GermBrick.mk ρ (LocalEmbedding.identity ρ),Finset.mem_singleton_self _⟩,?_⟩
  rw [hi]
  refine ⟨LocalEmbedding.identity ρ,infiniteTile i,rfl,?_⟩
  rw [LocalEmbedding.identity_comp]

end TwistedBrin.UnslicedPartition

namespace TwistedBrin
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace Basis

noncomputable def ofChartPartition {I : Type*} [Fintype I]
    (h : I → LocalEmbedding ρ)
    (hp : ∀ x : Box S, ∃! i : I, x ∈ Set.range (h i)) : Basis ρ := by
  classical
  exact {
    pieces := Finset.univ.image (fun i => GermBrick.mk ρ (h i))
    partition := by
      intro x
      obtain ⟨i,hi,hu⟩ := hp x
      refine ⟨⟨_,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩,hi,?_⟩
      intro b hb
      obtain ⟨j,_,hj⟩ := Finset.mem_image.mp b.property
      apply Subtype.ext
      have hjx : x ∈ Set.range (h j) := by
        change x ∈ GermBrick.region ρ b.val at hb
        rwa [← hj] at hb
      exact hj.symm.trans (congrArg (fun i => GermBrick.mk ρ (h i)) (hu j hjx)) }

lemma chartPartition_injective {I : Type*} (h : I → LocalEmbedding ρ)
    (hp : ∀ x : Box S, ∃! i : I, x ∈ Set.range (h i)) :
    Function.Injective (fun i => GermBrick.mk ρ (h i)) := by
  intro i j he
  change GermBrick.mk ρ (h i) = GermBrick.mk ρ (h j) at he
  let x : Box S := h i (fun _ _ => false)
  have hi : x ∈ GermBrick.region ρ (GermBrick.mk ρ (h i)) := ⟨_,rfl⟩
  have hj : x ∈ Set.range (h j) := by
    change x ∈ GermBrick.region ρ (GermBrick.mk ρ (h j))
    rwa [← he]
  exact (hp x).unique hi hj

lemma rank_ofChartPartition {I : Type*} [Fintype I]
    (h : I → LocalEmbedding ρ)
    (hp : ∀ x : Box S, ∃! i : I, x ∈ Set.range (h i)) :
    rank ρ (ofChartPartition ρ h hp) = Fintype.card I := by
  classical
  exact (Finset.card_image_of_injective _ (chartPartition_injective ρ h hp)).trans
    (Finset.card_univ)

noncomputable def expandedChart (B : Basis ρ) (P : B → Pattern S)
    (i : Σ b : B, Pattern.Leaves (P b)) : LocalEmbedding ρ :=
  LocalEmbedding.comp ρ (chart ρ B i.1)
    (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix (P i.1) i.2))

lemma expanded_partition (B : Basis ρ) (P : B → Pattern S) :
    ∀ x : Box S, ∃! i : Σ b : B, Pattern.Leaves (P b),
      x ∈ Set.range (expandedChart ρ B P i) := by
  intro x
  obtain ⟨b,hb,hu⟩ := B.partition x
  rw [← chart_region ρ B b] at hb
  obtain ⟨y,rfl⟩ := hb
  obtain ⟨i,hi,hiu⟩ := Pattern.partition (P b) y
  refine ⟨⟨b,i⟩,?_,?_⟩
  · obtain ⟨z,rfl⟩ := hi
    exact ⟨z,rfl⟩
  · rintro ⟨c,j⟩ ⟨z,hz⟩
    have hc : (chart ρ B b) y ∈ GermBrick.region ρ c.val := by
      rw [← chart_region ρ B c]
      exact ⟨_,hz⟩
    have hb' : (chart ρ B b) y ∈ GermBrick.region ρ b.val := by
      rw [← chart_region ρ B b]
      exact ⟨y,rfl⟩
    have hcb : c = b := hu c hc
    subst c
    have hy : (Pattern.leafPrefix (P b) j).chart z = y :=
      (chart ρ B b).toEmbedding.injective hz
    have hji : j = i := hiu j ⟨z,hy⟩
    subst j
    rfl

noncomputable def expand (B : Basis ρ) (P : B → Pattern S) : Basis ρ :=
  ofChartPartition ρ (expandedChart ρ B P) (expanded_partition ρ B P)

lemma rank_expand (B : Basis ρ) (P : B → Pattern S) :
    rank ρ (expand ρ B P) = ∑ b : B, Fintype.card (Pattern.Leaves (P b)) := by
  rw [expand,rank_ofChartPartition,Fintype.card_sigma]

lemma refines_expand (B : Basis ρ) (P : B → Pattern S) : B ≤ expand ρ B P := by
  classical
  intro c
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp c.property
  refine ⟨i.1,chart ρ B i.1,Pattern.leafPrefix (P i.1) i.2,?_,hi.symm⟩
  exact (GermBrick.mk_representative ρ i.1.val).symm

lemma expand_leaf (B : Basis ρ) : expand ρ B (fun _ => .leaf) = B := by
  apply Basis.ext
  classical
  ext b
  change (b ∈ Finset.univ.image _) ↔ b ∈ B.pieces
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨c,i⟩,rfl⟩
    change GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ B c)
      (LocalEmbedding.ofPrefix ρ Prefix.empty)) ∈ B.pieces
    simp [chart]
  · intro hb
    refine ⟨⟨⟨b,hb⟩,PUnit.unit⟩,?_⟩
    change GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ B ⟨b,hb⟩)
      (LocalEmbedding.ofPrefix ρ Prefix.empty)) = b
    simp [chart]

end Basis
end TwistedBrin

end

end OAI
