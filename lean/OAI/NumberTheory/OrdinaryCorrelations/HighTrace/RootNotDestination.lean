import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GrowsSingleton

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter

namespace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.GraphKernel.PrimeSystem
open Finset Classical
variable {h ℓ : ℕ}

lemma root_not_destination (w : ClosedLine h ℓ) {e : Fin ℓ} (he : e ∈ w.treeSteps) :
    w.offset e.succ ≠ 0 := by
  intro hz
  exact (mem_filter.mp he).2 0 (Nat.zero_le _) (w.start_zero.trans hz.symm)

lemma vertices_eq_insert_destinations (w : ClosedLine h ℓ) :
    treeVertices w = insert 0 (w.treeSteps.image (fun e => w.offset e.succ)) := by
  ext v
  constructor
  · intro hv
    by_cases hz : v=0
    · simp [hz]
    · obtain ⟨e,he,hev⟩ := has_incoming_edge w v hv hz
      exact mem_insert_of_mem (mem_image.mpr ⟨e,he,hev⟩)
  · intro hv
    rcases mem_insert.mp hv with rfl | hd
    · exact mem_image.mpr ⟨0,mem_univ _,w.start_zero⟩
    · obtain ⟨e,he,rfl⟩ := mem_image.mp hd
      exact endpoint_mem_vertices w e

lemma tree_vertices_card (w : ClosedLine h ℓ) :
    (treeVertices w).card = w.treeSteps.card + 1 := by
  rw [vertices_eq_insert_destinations,card_insert_of_notMem]
  · rw [card_image_iff.mpr (tree_destination_injective w)]
  · rintro hv
    obtain ⟨e,he,hev⟩ := mem_image.mp hv
    exact root_not_destination w he hev

lemma sum_children (w : ClosedLine h ℓ) :
    ∑ v ∈ treeVertices w, w.children v = w.treeSteps.card := by
  rw [← outgoing_card]
  have he : outgoing w (treeVertices w)= w.treeSteps := by
    apply filter_eq_self.mpr
    intro e _
    exact departure_mem_vertices w e
  rw [he]

def leafVertices (w : ClosedLine h ℓ) : Finset ℤ :=
  (treeVertices w).filter (fun v => w.children v=0)

def irregularVertices (w : ClosedLine h ℓ) : Finset ℤ :=
  (treeVertices w).filter (fun v => w.children v≠1)

def returnVertices (w : ClosedLine h ℓ) : Finset ℤ := edgeVertices w (returnSteps w)

def unaryReturnVertices (w : ClosedLine h ℓ) : Finset ℤ :=
  (returnVertices w).filter (fun v => w.children v=1)

lemma leaf_subset_returns (w : ClosedLine h ℓ) :
    leafVertices w ⊆ insert 0 ((returnSteps w).image (fun e => w.offset e.castSucc)) := by
  intro v hv
  obtain ⟨hv,hc⟩ := mem_filter.mp hv
  by_cases hz : v=0
  · simp [hz]
  · obtain ⟨j,hj,hjv⟩ := mem_image.mp hv
    have hjlast : j≠Fin.last ℓ := by
      rintro rfl
      exact hz (hjv.symm.trans w.end_zero)
    obtain ⟨e,rfl⟩ := Fin.eq_castSucc_of_ne_last hjlast
    have he : e ∈ returnSteps w := by
      apply Finset.mem_sdiff.mpr
      refine ⟨mem_univ _,?_⟩
      intro het
      have hh : e ∈ w.treeSteps.filter (fun i => w.offset i.castSucc=v) :=
        mem_filter.mpr ⟨het,hjv⟩
      have hn : (w.treeSteps.filter (fun i => w.offset i.castSucc=v)).Nonempty := ⟨e,hh⟩
      have hn' := card_pos.mpr hn
      change 0 < w.children v at hn'
      omega
    exact mem_insert_of_mem (mem_image.mpr ⟨e,he,hjv⟩)

lemma leaf_card_le (w : ClosedLine h ℓ) :
    (leafVertices w).card ≤ (returnSteps w).card + 1 := by
  calc
    _ ≤ (insert 0 ((returnSteps w).image (fun e => w.offset e.castSucc))).card :=
      card_le_card (leaf_subset_returns w)
    _ ≤ ((returnSteps w).image (fun e => w.offset e.castSucc)).card +1 := card_insert_le _ _
    _ ≤ _ := Nat.add_le_add_right card_image_le 1

lemma irregular_incidence_mass (w : ClosedLine h ℓ) :
    ∑ v ∈ irregularVertices w, (w.children v+1) ≤ 4*(leafVertices w).card := by
  have hd : ∀ d : ℕ, (if d≠1 then d+1 else 0)+3 ≤
      4*(if d=0 then 1 else 0)+3*d := by
    intro d
    by_cases h0 : d=0
    · simp [h0]
    · by_cases h1 : d=1
      · simp [h1]
      · simp only [h0,h1,ne_eq,not_false_eq_true,ite_true,ite_false,mul_zero,zero_add]
        omega
  have hs := sum_le_sum (s := treeVertices w) (fun v _ => hd (w.children v))
  have hz : (∑ v ∈ treeVertices w, if w.children v=0 then 1 else 0) = (leafVertices w).card := by
    simp only [leafVertices,← sum_filter, sum_const,smul_eq_mul,mul_one]
  have hi : (∑ v ∈ treeVertices w, if w.children v≠1 then w.children v+1 else 0) =
      ∑ v ∈ irregularVertices w, (w.children v+1) := by rw [irregularVertices,sum_filter]
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,← mul_sum] at hs
  rw [hz,hi,sum_children] at hs
  have hc := tree_vertices_card w
  simp only [Nat.cast_id] at hs
  omega

def incidentEdges (w : ClosedLine h ℓ) (V : Finset ℤ) : Finset (Fin ℓ) :=
  w.treeSteps.filter (fun e => w.offset e.castSucc ∈ V ∨ w.offset e.succ ∈ V)

lemma incident_card_le (w : ClosedLine h ℓ) (V : Finset ℤ) :
    (incidentEdges w V).card ≤ ∑ v ∈ V, (w.children v+1) := by
  let I := w.treeSteps.filter (fun e => w.offset e.succ ∈ V)
  have hde : incidentEdges w V = outgoing w V ∪ I := by
    ext e
    simp only [incidentEdges,outgoing,I,mem_union,mem_filter]
    tauto
  have hi : I.card ≤ V.card := by
    apply card_le_card_of_injOn (fun e => w.offset e.succ)
    · intro e he
      exact (mem_filter.mp he).2
    · exact (tree_destination_injective w).mono (filter_subset _ _)
  rw [hde,sum_add_distrib,sum_const,nsmul_eq_mul,mul_one,← outgoing_card]
  exact (card_union_le _ _).trans (Nat.add_le_add_left hi _)

lemma return_vertices_card (w : ClosedLine h ℓ) :
    (returnVertices w).card ≤ 2*(returnSteps w).card := by
  unfold returnVertices edgeVertices
  have h₁ := card_image_le (s := returnSteps w) (f := fun e => w.offset e.castSucc)
  have h₂ := card_image_le (s := returnSteps w) (f := fun e => w.offset e.succ)
  exact (card_union_le _ _).trans (by omega)

lemma unary_return_incidence_card (w : ClosedLine h ℓ) :
    (incidentEdges w (unaryReturnVertices w)).card ≤ 4*(returnSteps w).card := by
  have hi := incident_card_le w (unaryReturnVertices w)
  have he : (∑ v ∈ unaryReturnVertices w, (w.children v+1)) =
      2*(unaryReturnVertices w).card := by
    have hh : ∀ v ∈ unaryReturnVertices w, w.children v+1=2 := by
      intro v hv
      rw [(mem_filter.mp hv).2]
    rw [sum_congr rfl hh]
    simp [mul_comm]
  rw [he] at hi
  have hc : (unaryReturnVertices w).card ≤ (returnVertices w).card := card_le_card (filter_subset _ _)
  have hr := return_vertices_card w
  omega

lemma not_noReturnIncidence (w : ClosedLine h ℓ) (v : ℤ) :
    ¬w.NoReturnIncidence v ↔ v ∈ returnVertices w := by
  simp only [ClosedLine.NoReturnIncidence,not_forall,not_and,not_not,
    returnVertices,edgeVertices,mem_union,mem_image,returnSteps,Finset.mem_sdiff,mem_univ,true_and]
  constructor
  · rintro ⟨i,hi,hm⟩
    by_cases hor : w.offset i.castSucc = v
    · exact Or.inl ⟨i,hi,hor⟩
    · exact Or.inr ⟨i,hi,hm hor⟩
  · rintro (⟨i,hi,hv⟩ | ⟨i,hi,hv⟩)
    · exact ⟨i,hi,fun hn => False.elim (hn hv)⟩
    · exact ⟨i,hi,fun _ => hv⟩

theorem bad_edges_le (w : ClosedLine h ℓ) :
    (badEdges w).card ≤ 10*((returnSteps w).card+1) := by
  let R := w.treeSteps.filter (fun e => w.offset e.castSucc=0 ∧ w.children 0=1)
  have hr : R.card ≤ 1 := by
    by_cases h0 : w.children 0=1
    · have he : R = w.treeSteps.filter (fun e => w.offset e.castSucc=0) := by
        ext e
        simp [R,h0]
      rw [he]
      exact h0.le
    · have he : R=∅ := by simp [R,h0]
      simp [he]
  have hb : badEdges w ⊆ incidentEdges w (irregularVertices w) ∪
      incidentEdges w (unaryReturnVertices w) ∪ R := by
    intro e he
    obtain ⟨het,hng⟩ := mem_filter.mp he
    by_cases ho : w.children (w.offset e.castSucc)=1
    swap
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨het,Or.inl
        (mem_filter.mpr ⟨departure_mem_vertices w e,ho⟩)⟩))
    by_cases hd : w.children (w.offset e.succ)=1
    swap
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨het,Or.inr
        (mem_filter.mpr ⟨endpoint_mem_vertices w e,hd⟩)⟩))
    by_cases hz : w.offset e.castSucc=0
    · exact mem_union_right _ (mem_filter.mpr ⟨het,hz,by rwa [hz] at ho⟩)
    have hret : ¬w.NoReturnIncidence (w.offset e.castSucc) ∨
        ¬w.NoReturnIncidence (w.offset e.succ) := by
      by_contra hn
      push Not at hn
      exact hng ⟨het,ho,hd,hz,hn.1,hn.2⟩
    apply mem_union_left _
    apply mem_union_right _
    apply mem_filter.mpr
    refine ⟨het,?_⟩
    rcases hret with hor | hdr
    · exact Or.inl (mem_filter.mpr ⟨(not_noReturnIncidence w _).mp hor,ho⟩)
    · exact Or.inr (mem_filter.mpr ⟨(not_noReturnIncidence w _).mp hdr,hd⟩)
  have hbc := card_le_card hb
  have hu := card_union_le (incidentEdges w (irregularVertices w) ∪
    incidentEdges w (unaryReturnVertices w)) R
  have hu₂ := card_union_le (incidentEdges w (irregularVertices w))
    (incidentEdges w (unaryReturnVertices w))
  have hir := (incident_card_le w (irregularVertices w)).trans (irregular_incidence_mass w)
  have hleaf := leaf_card_le w
  have hreturn := unary_return_incidence_card w
  omega

lemma length_good_bad_return (w : ClosedLine h ℓ) :
    (goodEdges w).card + (badEdges w).card + (returnSteps w).card = ℓ := by
  have hg : (goodEdges w).card + (badEdges w).card = w.treeSteps.card := by
    exact card_filter_add_card_filter_not _
  rw [hg]
  have hc := card_sdiff_add_card_eq_card (subset_univ w.treeSteps)
  simpa only [returnSteps,card_univ,Fintype.card_fin,add_comm] using hc

end OrdinaryCorrelations.NumericalSubtrees

end

end OAI
