import OAI.Combinatorics.ThinTrees.BagGeometry

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset
variable {n m : ℕ} (G : MultiGraph n m)

def inducedEdges (A : Finset (Fin n)) : Finset (Fin m) :=
  univ.filter (fun e => G.left e ∈ A ∧ G.right e ∈ A)

def EdgeConnectedReal (A : Finset (Fin n)) (q : ℝ) : Prop :=
  ∀S : Finset (Fin n), S.Nonempty → S ⊂ A → q ≤ (G.cut (G.inducedEdges A) S).card

lemma mem_inducedEdges (A : Finset (Fin n)) (e : Fin m) :
    e ∈ G.inducedEdges A ↔ G.left e ∈ A ∧ G.right e ∈ A := by simp [inducedEdges]

lemma cut_internal_split {A S : Finset (Fin n)} (hS : S ⊆ A) :
    ((G.inducedEdges A).card : ℝ) = (G.inducedEdges S).card+
      (G.inducedEdges (A\S)).card+(G.cut (G.inducedEdges A) S).card := by
  have heq : G.inducedEdges A = G.inducedEdges S ∪ G.inducedEdges (A\S) ∪ G.cut (G.inducedEdges A) S := by
    ext e
    simp only [mem_union,mem_inducedEdges,cut,mem_filter]
    simp only [mem_sdiff]
    constructor
    · intro h
      by_cases hl : G.left e ∈ S <;> by_cases hr : G.right e ∈ S <;> tauto
    · intro h
      rcases h with ((h | h) | h)
      · exact ⟨hS h.1,hS h.2⟩
      · exact ⟨h.1.1,h.2.1⟩
      · exact h.1
  have hd : Disjoint (G.inducedEdges S) (G.inducedEdges (A\S)) := by
    rw [Finset.disjoint_left]
    intro e he hf
    rw [mem_inducedEdges] at he hf
    exact (mem_sdiff.mp hf.1).2 he.1
  have hd' : Disjoint (G.inducedEdges S ∪ G.inducedEdges (A\S)) (G.cut (G.inducedEdges A) S) := by
    rw [Finset.disjoint_left]
    intro e he hf
    have hc := (mem_filter.mp hf).2
    rcases mem_union.mp he with he | he
    · rw [mem_inducedEdges] at he
      tauto
    · rw [mem_inducedEdges] at he
      have hl := (mem_sdiff.mp he.1).2
      have hr := (mem_sdiff.mp he.2).2
      tauto
  have hc : (G.inducedEdges A).card = (G.inducedEdges S).card+
      (G.inducedEdges (A\S)).card+(G.cut (G.inducedEdges A) S).card := by
    conv_lhs => rw [heq]
    rw [card_union_of_disjoint hd',card_union_of_disjoint hd]
  exact_mod_cast hc

def VertexPartition (A : Finset (Fin n)) (P : Finset (Finset (Fin n))) : Prop :=
  (∀B ∈ P, B.Nonempty ∧ B ⊆ A) ∧
  (P : Set (Finset (Fin n))).Pairwise Disjoint ∧ P.biUnion id = A

lemma vertexPartition_singleton {A : Finset (Fin n)} (hA : A.Nonempty) :
    VertexPartition A {A} := by
  refine ⟨?_,?_,by simp⟩
  · intro B hB
    have heq := mem_singleton.mp hB
    subst B
    exact ⟨hA,Subset.rfl⟩
  · intro B hB C hC hne
    exact (hne ((mem_singleton.mp hB).trans (mem_singleton.mp hC).symm)).elim

lemma vertexPartition_union {A B : Finset (Fin n)} {P Q : Finset (Finset (Fin n))}
    (hP : VertexPartition A P) (hQ : VertexPartition B Q) (hAB : Disjoint A B) :
    VertexPartition (A∪B) (P∪Q) ∧ Disjoint P Q := by
  have hd : ∀S ∈ P, ∀T ∈ Q, Disjoint S T := by
    intro S hS T hT
    exact hAB.mono (hP.1 S hS).2 (hQ.1 T hT).2
  have hPQ : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro S hS hT
    obtain ⟨u,hu⟩ := (hP.1 S hS).1
    exact Finset.disjoint_left.mp (hd S hS S hT) hu hu
  refine ⟨⟨?_,?_,?_⟩,hPQ⟩
  · intro S hS
    rcases mem_union.mp hS with hS | hS
    · exact ⟨(hP.1 S hS).1,((hP.1 S hS).2).trans (subset_union_left)⟩
    · exact ⟨(hQ.1 S hS).1,((hQ.1 S hS).2).trans (subset_union_right)⟩
  · intro S hS T hT hne
    rcases mem_union.mp hS with hS | hS <;> rcases mem_union.mp hT with hT | hT
    · exact hP.2.1 hS hT hne
    · exact hd S hS T hT
    · exact (hd T hT S hS).symm
    · exact hQ.2.1 hS hT hne
  · rw [union_biUnion,hP.2.2,hQ.2.2]

lemma connected_partition (A : Finset (Fin n)) (hA : A.Nonempty) {q : ℝ} (_hq : 0 ≤ q) :
    ∃P : Finset (Finset (Fin n)), VertexPartition A P ∧
      (∀B ∈ P, G.EdgeConnectedReal B q) ∧
      ((G.inducedEdges A).card : ℝ)-(∑B ∈ P, ((G.inducedEdges B).card : ℝ)) ≤ q*((P.card : ℝ)-1) := by
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    by_cases hconn : G.EdgeConnectedReal A q
    · exact ⟨{A},vertexPartition_singleton hA,by simpa,by simp⟩
    · obtain ⟨S,hSne,hSA,hcut⟩ : ∃S, S.Nonempty ∧ S ⊂ A ∧
          ((G.cut (G.inducedEdges A) S).card : ℝ) < q := by
        simp only [EdgeConnectedReal,not_forall,not_le] at hconn
        obtain ⟨S,hSne,hSA,hcut⟩ := hconn
        exact ⟨S,hSne,hSA,hcut⟩
      have hRA : A\S ⊂ A := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨sdiff_subset,?_⟩
        intro heq
        obtain ⟨u,hu⟩ := hSne
        have : u ∈ A\S := heq.symm ▸ hSA.subset hu
        exact (mem_sdiff.mp this).2 hu
      have hRne : (A\S).Nonempty := by
        apply sdiff_nonempty.mpr
        intro hh
        exact (Finset.ssubset_iff_subset_ne.mp hSA).2 (Subset.antisymm hSA.subset hh)
      obtain ⟨P,hP,hPc,hPb⟩ := ih S hSA hSne
      obtain ⟨Q,hQ,hQc,hQb⟩ := ih (A\S) hRA hRne
      obtain ⟨hPQ,hdis⟩ := vertexPartition_union hP hQ (disjoint_sdiff_self_right)
      have hcover : S ∪ (A\S) = A := union_sdiff_of_subset hSA.subset
      rw [hcover] at hPQ
      refine ⟨P∪Q,hPQ,?_,?_⟩
      · intro B hB
        rcases mem_union.mp hB with hB | hB
        · exact hPc B hB
        · exact hQc B hB
      · rw [sum_union hdis,card_union_of_disjoint hdis,Nat.cast_add]
        have he := G.cut_internal_split hSA.subset
        linarith

end
end StrongThinTree.MultiGraph

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset
variable {n m : ℕ} (G : MultiGraph n m)

def endpointMass (A : Finset (Fin n)) (e : Fin m) : ℝ :=
  (if G.left e ∈ A then 1 else 0)+(if G.right e ∈ A then 1 else 0)

def volume (R A : Finset (Fin n)) : ℝ := ∑e ∈ G.inducedEdges R, G.endpointMass A e

lemma partition_point_mass {A : Finset (Fin n)} {P : Finset (Finset (Fin n))}
    (hP : VertexPartition A P) (v : Fin n) :
    (∑B ∈ P, if v ∈ B then (1:ℝ) else 0) = if v ∈ A then (1:ℝ) else 0 := by
  by_cases hv : v ∈ A
  · obtain ⟨B,hB,hvB⟩ := mem_biUnion.mp (hP.2.2.symm ▸ hv)
    rw [ite_eq_left hv,sum_eq_single B]
    · exact ite_eq_left hvB
    · intro C hC hCB
      have hvC : v ∉ C := fun hh => Finset.disjoint_left.mp (hP.2.1 hC hB hCB) hh hvB
      simp [hvC]
    · exact fun hh => (hh hB).elim
  · rw [ite_eq_right hv]
    apply sum_eq_zero
    intro B hB
    exact ite_eq_right (fun hh => hv ((hP.1 B hB).2 hh))

lemma volume_partition {A R : Finset (Fin n)} {P : Finset (Finset (Fin n))}
    (hP : VertexPartition A P) : (∑B ∈ P, G.volume R B) = G.volume R A := by
  simp only [volume]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  simp only [endpointMass,sum_add_distrib]
  rw [partition_point_mass hP,partition_point_mass hP]

lemma volume_eq_boundary {A B : Finset (Fin n)} (hBA : B ⊆ A) :
    G.volume A B = ((G.cut (G.inducedEdges A) B).card : ℝ)+2*(G.inducedEdges B).card := by
  have hcard (E : Finset (Fin m)) : (E.card : ℝ) = ∑e : Fin m, if e ∈ E then (1:ℝ) else 0 := by simp
  rw [hcard,hcard,mul_sum,← sum_add_distrib]
  simp only [volume,inducedEdges,sum_filter]
  apply sum_congr rfl
  intro e he
  simp only [endpointMass,cut,mem_filter,mem_univ,true_and]
  have hl := hBA (x := G.left e)
  have hr := hBA (x := G.right e)
  by_cases hlA : G.left e ∈ A <;> by_cases hrA : G.right e ∈ A <;>
    by_cases hlB : G.left e ∈ B <;> by_cases hrB : G.right e ∈ B <;>
      norm_num [*] at *

lemma cut_complement_in {A B : Finset (Fin n)} (_hBA : B ⊆ A) :
    G.cut (G.inducedEdges A) (A\B) = G.cut (G.inducedEdges A) B := by
  ext e
  simp only [cut,mem_filter,mem_inducedEdges,mem_sdiff]
  tauto

lemma outside_connected_partition {A T : Finset (Fin n)} {k : ℝ}
    (hk : 0 < k) (hconn : G.EdgeConnectedReal A k) (hT : T.Nonempty) (hTA : T ⊂ A) :
    ∃P : Finset (Finset (Fin n)), VertexPartition (A\T) P ∧
      (∀B ∈ P, G.EdgeConnectedReal B (k/4)) ∧
      (P.card : ℝ)*k ≤ 2*(G.cut (G.inducedEdges A) T).card := by
  have hR : (A\T).Nonempty := by
    apply sdiff_nonempty.mpr
    intro hh
    exact (Finset.ssubset_iff_subset_ne.mp hTA).2 (Subset.antisymm hTA.subset hh)
  obtain ⟨P,hP,hPc,hcost⟩ := G.connected_partition (A\T) hR (by positivity : 0 ≤ k/4)
  have hBA : ∀B ∈ P, B ⊆ A := fun B hB => ((hP.1 B hB).2).trans sdiff_subset
  have hcuts : (P.card : ℝ)*k ≤ ∑B ∈ P, ((G.cut (G.inducedEdges A) B).card : ℝ) := by
    calc
      _ = ∑B ∈ P, k := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro B hB
        apply hconn B (hP.1 B hB).1
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hBA B hB,?_⟩
        intro heq
        obtain ⟨v,hv⟩ := hT
        have hh := (hP.1 B hB).2 (heq.symm ▸ hTA.subset hv)
        exact (mem_sdiff.mp hh).2 hv
  have hvol : (∑B ∈ P, ((G.cut (G.inducedEdges A) B).card : ℝ))+
      2*(∑B ∈ P, ((G.inducedEdges B).card : ℝ)) =
      ((G.cut (G.inducedEdges A) T).card : ℝ)+2*(G.inducedEdges (A\T)).card := by
    calc
      _ = ∑B ∈ P, G.volume A B := by
        rw [mul_sum,← sum_add_distrib]
        exact sum_congr rfl (fun B hB => (G.volume_eq_boundary (hBA B hB)).symm)
      _ = G.volume A (A\T) := G.volume_partition hP
      _ = _ := by rw [G.volume_eq_boundary sdiff_subset,G.cut_complement_in hTA.subset]
  refine ⟨P,hP,hPc,?_⟩
  nlinarith

end
end StrongThinTree.MultiGraph

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset

structure Hierarchy (n : ℕ) where
  nodes : Finset (Finset (Fin n))
  nonempty : ∀A ∈ nodes, A.Nonempty
  root_mem : univ ∈ nodes
  singletons : ∀v, {v} ∈ nodes
  laminar : ∀A ∈ nodes, ∀B ∈ nodes, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B
  parent : Finset (Fin n) → Finset (Fin n)
  parent_mem : ∀A ∈ nodes, A ≠ univ → parent A ∈ nodes
  parent_strict : ∀A ∈ nodes, A ≠ univ → A ⊂ parent A
  parent_minimal : ∀A ∈ nodes, A ≠ univ → ∀B ∈ nodes, A ⊂ B → parent A ⊆ B

end
end StrongThinTree.MultiGraph

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} (G : MultiGraph n m)

lemma routed_variation_lower {R L : Finset (Fin n)} {q a b : ℝ}
    (f : Fin n → ℝ) (hab : a ≤ b) (hconn : G.EdgeConnectedReal R q)
    (hu : ∃u ∈ R, u ∈ L ∧ f u ≤ a) (hv : ∃v ∈ R, b ≤ f v)
    (hprotect : ∀e ∈ G.inducedEdges R,
      ((G.left e ∈ L ∧ G.right e ∉ L) ∨ (G.right e ∈ L ∧ G.left e ∉ L)) →
      b ≤ f (G.left e) ∧ b ≤ f (G.right e)) :
    q*(b-a) ≤ ∑e ∈ G.inducedEdges L,
      |clamp a b (f (G.left e))-clamp a b (f (G.right e))| := by
  have hh := cut_range_bound (k := q) (fun e : G.inducedEdges L => G.left e)
    (fun e : G.inducedEdges L => G.right e) (fun v => clamp a b (f v)) hab
  rw [← Finset.sum_coe_sort]
  apply hh
  intro t ht
  let S := R.filter (fun v => v ∈ L ∧ f v < t)
  have hSR : S ⊆ R := filter_subset _ _
  have hSn : S.Nonempty := by
    obtain ⟨u,huR,huL,hu⟩ := hu
    exact ⟨u,mem_filter.mpr ⟨huR,huL,lt_of_le_of_lt hu ht.1⟩⟩
  have hSproper : S ⊂ R := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hSR,?_⟩
    intro heq
    obtain ⟨v,hvR,hv⟩ := hv
    have hh := (mem_filter.mp (heq.symm ▸ hvR)).2.2
    linarith [ht.2]
  have hc := hconn S hSn hSproper
  have hedge : ∀e ∈ G.cut (G.inducedEdges R) S, e ∈ G.inducedEdges L ∧
      ((f (G.left e)<t ∧ ¬ f (G.right e)<t) ∨
       (f (G.right e)<t ∧ ¬f (G.left e)<t)) := by
    intro e he
    obtain ⟨heR,hcut⟩ := mem_filter.mp he
    obtain ⟨hlR,hrR⟩ := (G.mem_inducedEdges _ _).mp heR
    rcases hcut with hcut | hcut
    · have hl := (mem_filter.mp hcut.1).2
      have hrL : G.right e ∈ L := by
        by_contra hh
        have hp := (hprotect e heR (Or.inl ⟨hl.1,hh⟩)).1
        linarith [ht.2,hl.2]
      have hr : ¬f (G.right e)<t := fun hh => hcut.2 (mem_filter.mpr ⟨hrR,hrL,hh⟩)
      exact ⟨(G.mem_inducedEdges _ _).mpr ⟨hl.1,hrL⟩,Or.inl ⟨hl.2,hr⟩⟩
    · have hr := (mem_filter.mp hcut.1).2
      have hlL : G.left e ∈ L := by
        by_contra hh
        have hp := (hprotect e heR (Or.inr ⟨hr.1,hh⟩)).2
        linarith [ht.2,hr.2]
      have hl : ¬f (G.left e)<t := fun hh => hcut.2 (mem_filter.mpr ⟨hlR,hlL,hh⟩)
      exact ⟨(G.mem_inducedEdges _ _).mpr ⟨hlL,hr.1⟩,Or.inr ⟨hr.2,hl⟩⟩
  have hcard : (G.cut (G.inducedEdges R) S).card ≤
      (univ.filter (fun e : G.inducedEdges L =>
      (clamp a b (f (G.left e))<t ∧ ¬clamp a b (f (G.right e))<t) ∨
      (clamp a b (f (G.right e))<t ∧ ¬clamp a b (f (G.left e))<t))).card := by
    let F (e : G.cut (G.inducedEdges R) S) :
        (univ.filter (fun e : G.inducedEdges L =>
          (clamp a b (f (G.left e))<t ∧ ¬clamp a b (f (G.right e))<t) ∨
          (clamp a b (f (G.right e))<t ∧ ¬clamp a b (f (G.left e))<t))) :=
      ⟨⟨e.val,(hedge e.val e.property).1⟩,by
        simp only [mem_filter,mem_univ,true_and,clamp_lt_iff ht]
        exact (hedge e.val e.property).2⟩
    apply Finset.card_le_card_of_injective (f := F)
    intro e f hh
    apply Subtype.ext
    exact congrArg (fun x => x.val.val) hh
  exact hc.trans (by exact_mod_cast hcard)

end
end StrongThinTree.MultiGraph

end

end OAI
