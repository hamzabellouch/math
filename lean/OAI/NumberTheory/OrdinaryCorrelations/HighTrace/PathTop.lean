import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Directed

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.GraphKernel.PrimeSystem
open Finset Classical
noncomputable section
variable {h ℓ : ℕ}

def pathTop (w : ClosedLine h ℓ) (E : Finset (Fin ℓ)) : ℤ :=
  if he : E.Nonempty then w.offset (E.min' he).castSucc else 0
def pathRank (E : Finset (Fin ℓ)) : ℕ :=
  if he : E.Nonempty then (E.min' he).val else 0
def topMarks (w : ClosedLine h ℓ) (E : Finset (Fin ℓ)) : Finset (Fin ℓ) :=
  E.filter (fun e => w.offset e.castSucc=pathTop w E)

lemma grows_intersect_topMarks (w : ClosedLine h ℓ) {E F : Finset (Fin ℓ)}
    (hne : E.Nonempty) (hnf : F.Nonempty)
    (hE : Grows w (pathTop w E) E) (hF : Grows w (pathTop w F) F)
    (hrank : pathRank F ≤ pathRank E) (e : Fin ℓ) (heE : e ∈ E) (heF : e ∈ F) :
    ∃ j ∈ topMarks w E, j ∈ F := by
  have hmin : F.min' hnf ≤ E.min' hne := by
    apply Fin.le_def.mpr
    simpa only [pathRank,dite_eq_left hne,dite_eq_left hnf] using hrank
  suffices aux : ∀ n, ∀ e : Fin ℓ, e.val=n → e ∈ E → e ∈ F → ∃ j ∈ topMarks w E,j ∈ F by
    exact aux _ e rfl heE heF
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro e hen heE heF
    by_cases ho : w.offset e.castSucc=pathTop w E
    · exact ⟨e,mem_filter.mpr ⟨heE,ho⟩,heF⟩
    obtain ⟨j,hjE,hje,hjv⟩ := (hE.2 e heE).resolve_left ho
    have hnot : w.offset e.castSucc≠pathTop w F := by
      intro heq
      have hv : w.offset j.succ=w.offset (F.min' hnf).castSucc := by
        simpa only [pathTop,dite_eq_left hnf] using hjv.trans heq
      have hjf := incoming_earlier w (hE.1 hjE) hv
      exact (not_lt_of_ge ((min'_le E j hjE).trans' hmin)) hjf
    obtain ⟨k,hkF,_,hkv⟩ := (hF.2 e heF).resolve_left hnot
    have heq : j=k := tree_destination_injective w (hE.1 hjE) (hF.1 hkF) (hjv.trans hkv.symm)
    apply ih j.val (by rw [←hen]; exact Fin.lt_def.mp hje) j rfl hjE
    simpa only [heq] using hkF

theorem chronological_path_hitting (w : ClosedLine h ℓ) (pathFamily : Finset (Finset (Fin ℓ)))
    (hpaths : ∀ E ∈ pathFamily, E.Nonempty ∧ Grows w (pathTop w E) E ∧ (topMarks w E).card ≤ 2) :
    ∃ (𝓠 : Finset (Finset (Fin ℓ))) (H : Finset (Fin ℓ)),
      𝓠 ⊆ pathFamily ∧ (∀ E ∈ 𝓠,∀ F ∈ 𝓠,E≠F → Disjoint E F) ∧ H.card ≤ 2*𝓠.card ∧
      (∀ E ∈ pathFamily, ∃ e ∈ H,e ∈ E) ∧ H ⊆ pathFamily.biUnion id := by
  suffices aux : ∀ n, ∀ pathFamily : Finset (Finset (Fin ℓ)), pathFamily.card=n →
      (∀ E ∈ pathFamily, E.Nonempty ∧ Grows w (pathTop w E) E ∧ (topMarks w E).card ≤ 2) →
      ∃ (𝓠 : Finset (Finset (Fin ℓ))) (H : Finset (Fin ℓ)),
        𝓠 ⊆ pathFamily ∧ (∀ E ∈ 𝓠,∀ F ∈ 𝓠,E≠F → Disjoint E F) ∧ H.card ≤ 2*𝓠.card ∧
        (∀ E ∈ pathFamily,∃ e ∈ H,e ∈ E) ∧ H ⊆ pathFamily.biUnion id by
    exact aux _ pathFamily rfl hpaths
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro pathFamily hcard hpaths
    by_cases hp : pathFamily.Nonempty
    · obtain ⟨E,he,hmax⟩ := exists_max_image pathFamily pathRank hp
      let 𝓡 := pathFamily.filter (fun F => Disjoint E F)
      have hR : 𝓡 ⊆ pathFamily := filter_subset _ _
      have heR : E ∉ 𝓡 := by
        intro heR
        exact (hpaths E he).1.ne_empty (disjoint_self.mp (mem_filter.mp heR).2)
      have hlt : 𝓡.card<n := by
        rw [←hcard]
        exact card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hR,fun hh => heR (hh ▸ he)⟩)
      obtain ⟨𝓠,H,hQ,hdis,hH,hhit,hsub⟩ := ih 𝓡.card hlt 𝓡 rfl (fun F hf => hpaths F (hR hf))
      have heQ : E ∉ 𝓠 := fun hf => heR (hQ hf)
      refine ⟨insert E 𝓠,topMarks w E ∪ H,?_,?_,?_,?_,?_⟩
      · exact insert_subset he (hQ.trans hR)
      · intro F hF G hG hne
        rcases mem_insert.mp hF with hFE | hFQ
        · subst F
          rcases mem_insert.mp hG with hGE | hGQ
          · exact (hne hGE.symm).elim
          · exact (mem_filter.mp (hQ hGQ)).2
        · rcases mem_insert.mp hG with hGE | hGQ
          · subst G
            exact (mem_filter.mp (hQ hFQ)).2.symm
          · exact hdis F hFQ G hGQ hne
      · rw [card_insert_of_notMem heQ]
        exact (card_union_le _ _).trans (by have := (hpaths E he).2.2; omega)
      · intro F hf
        by_cases hd : Disjoint E F
        · obtain ⟨e,heH,heF⟩ := hhit F (mem_filter.mpr ⟨hf,hd⟩)
          exact ⟨e,mem_union_right _ heH,heF⟩
        · obtain ⟨e,heE,heF⟩ := not_disjoint_iff.mp hd
          obtain ⟨j,hj,hjF⟩ := grows_intersect_topMarks w (hpaths E he).1 (hpaths F hf).1
            (hpaths E he).2.1 (hpaths F hf).2.1 (hmax F hf) e heE heF
          exact ⟨j,mem_union_left _ hj,hjF⟩
      · intro e heH
        rcases mem_union.mp heH with heM | heH
        · exact mem_biUnion.mpr ⟨E,he,(mem_filter.mp heM).1⟩
        · obtain ⟨F,hf,heF⟩ := mem_biUnion.mp (hsub heH)
          exact mem_biUnion.mpr ⟨F,hR hf,heF⟩
    · refine ⟨∅,∅,empty_subset _,?_,by simp,?_,empty_subset _⟩
      · simp
      · intro E he
        exact (hp ⟨E,he⟩).elim

end
end OrdinaryCorrelations.NumericalSubtrees

end

end OAI
