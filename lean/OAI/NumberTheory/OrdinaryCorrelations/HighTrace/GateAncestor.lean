import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.MemTakeIndex
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.BelowChain
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.DisjointIntervals
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.IntervalOverlap

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.Rerooting
open Classical Finset SimpleGraph
noncomputable section
variable {V α : Type*} [DecidableEq V] [Fintype α] [DecidableEq α]
variable {G₁ G₂ : SimpleGraph V} {root₁ root₂ : V} {A₁ A₂ : α→Finset V}

abbrev gateAncestor {G : SimpleGraph V} {root : V} {A : α→Finset V}
    (g : ∀ p,Gate G root (A p)) :=
  Ancestor root (fun p => (g p).vertex) (fun p => (g p).path)

lemma reversed_left_injective (hG₂ : G₂.IsAcyclic)
    (g₁ : ∀ p,Gate G₁ root₁ (A₁ p)) (g₂ : ∀ p,Gate G₂ root₂ (A₂ p))
    (hc : Chain (Reverse (gateAncestor g₁) (gateAncestor g₂)) univ) :
    Function.Injective (fun p => (g₂ p).path.length) := by
  intro p q he
  change (g₂ p).path.length=(g₂ q).path.length at he
  by_contra hpq
  rcases hc (mem_univ _) (mem_univ _) hpq with h|h
  · have := ancestor_length_lt hG₂ root₂ _ _ (fun p => (g₂ p).simple) h.2
    omega
  · have := ancestor_length_lt hG₂ root₂ _ _ (fun p => (g₂ p).simple) h.2
    omega

theorem reroot_reverse [Nonempty α] (hG₁ : G₁.IsAcyclic) (hG₂ : G₂.IsAcyclic)
    (g₁ : ∀ p,Gate G₁ root₁ (A₁ p)) (g₂ : ∀ p,Gate G₂ root₂ (A₂ p))
    (hA₂ : ∀ p,ConnectedSet G₂ (A₂ p))
    (hc : Chain (Reverse (gateAncestor g₁) (gateAncestor g₂)) univ)
    (J : ℕ) (hcap : ∀ x y,G₂.Adj x y → (univ.filter (fun p => x ∈ A₂ p ∧ y ∈ A₂ p)).card ≤ J) :
    ∃ (root : V) (g : ∀ p,Gate G₂ root (A₂ p)) (t : Finset α),
      Fintype.card α ≤ (2*J+1)*t.card ∧
      (∃ p,root=(g₂ p).vertex) ∧
      ∀ p ∈ t,∀ q ∈ t,gateAncestor g p q → (g₁ p).path.length<(g₁ q).path.length := by
  obtain ⟨r,hr,hrmax⟩ := exists_max_image univ (fun p => (g₂ p).path.length) univ_nonempty
  let P := (g₂ r).path
  have hP : P.IsPath := (g₂ r).simple
  have hv (p : α) : (g₂ p).vertex ∈ P.support := by
    by_cases hpr : p=r
    · subst p; exact P.end_mem_support
    · rcases hc (mem_univ _) (mem_univ _) hpr with h|h
      · have hlt := ancestor_length_lt hG₂ root₂ _ _ (fun p => (g₂ p).simple) h.2
        have hmax := hrmax p (mem_univ _)
        omega
      · exact h.2.1
  have hne (p : α) : (segmentIndices P (A₂ p)).Nonempty := by
    obtain ⟨i,hi,hil⟩ := Walk.mem_support_iff_exists_getVert.mp (hv p)
    exact ⟨i,(mem_segmentIndices P (A₂ p) i).mpr ⟨hil,hi ▸ (g₂ p).mem⟩⟩
  let left := fun p => (segmentIndices P (A₂ p)).min' (hne p)
  let right := fun p => (segmentIndices P (A₂ p)).max' (hne p)
  have hleft (p : α) : left p=(g₂ p).path.length := by
    have he := (g₂ p).path_unique (leftGate P hP (A₂ p) (hne p)) hG₂ (hA₂ p)
    have hel := congrArg Walk.length he
    simpa only [Walk.length_copy,leftGate_length] using hel.symm
  have hlr (p : α) : left p ≤ right p := min'_le _ _ (max'_mem _ (hne p))
  have hrL (p : α) : right p ≤ P.length :=
    ((mem_segmentIndices P (A₂ p) (right p)).mp (max'_mem _ (hne p))).1
  have hint (p : α) (i : ℕ) : i ∈ segmentIndices P (A₂ p) ↔ left p ≤ i ∧ i ≤ right p :=
    segment_interval hG₂ (hA₂ p) P hP (hne p) i
  have hinj : Function.Injective left := by
    intro p q he
    exact reversed_left_injective hG₂ g₁ g₂ hc (by simpa only [hleft] using he)
  have hJ (i : ℕ) : (univ.filter (fun p => left p ≤ i ∧ i<right p)).card ≤ J := by
    by_cases hi : i<P.length
    · apply (card_le_card ?_).trans (hcap (P.getVert i) (P.getVert (i+1)) (P.adj_getVert_succ hi))
      intro p hp
      obtain ⟨_,hpl,hpr⟩ := mem_filter.mp hp
      have hpA := (mem_segmentIndices P (A₂ p) i).mp ((hint p i).mpr ⟨hpl,hpr.le⟩)
      have hpA' := (mem_segmentIndices P (A₂ p) (i+1)).mp ((hint p (i+1)).mpr ⟨by omega,by omega⟩)
      exact mem_filter.mpr ⟨mem_univ _,hpA.2,hpA'.2⟩
    · have hz : univ.filter (fun p => left p ≤ i ∧ i<right p)=∅ := by
        apply filter_eq_empty_iff.mpr
        intro p hp hh
        have := hrL p
        omega
      simp [hz]
  obtain ⟨t,ht,hcard,hdis⟩ := disjoint_intervals left right (2*J+1) univ
    (fun p _ => hlr p) (interval_overlap univ left right J (fun p _ => hlr p) hinj.injOn hJ)
  let g := fun p => rightGate P hP (A₂ p) (hne p)
  refine ⟨(g₂ r).vertex,g,t,by simpa using hcard,⟨r,rfl⟩,?_⟩
  intro p hp q hq hpq
  have hlt := ancestor_length_lt hG₂ (g₂ r).vertex _ _ (fun p => (g p).simple) hpq
  have hgp (p : α) : (g p).path.length=P.length-right p := rightGate_length P hP (A₂ p) (hne p)
  rw [hgp,hgp] at hlt
  have hrpq : right q<right p := by omega
  have hpneq : p≠q := by intro he; subst q; omega
  have hdis' := hdis hp hq hpneq
  have hlqp : left q<left p := by
    rcases hdis' with hbad|hgood
    · have := hlr q
      omega
    · exact (hlr q).trans_lt hgood
  rcases hc (mem_univ _) (mem_univ _) hpneq with h|h
  · exact ancestor_length_lt hG₁ root₁ _ _ (fun p => (g₁ p).simple) h.1
  · have he := ancestor_length_lt hG₂ root₂ _ _ (fun p => (g₂ p).simple) h.2
    rw [←hleft,←hleft] at he
    omega

end
end OrdinaryCorrelations.Rerooting

end

end OAI
