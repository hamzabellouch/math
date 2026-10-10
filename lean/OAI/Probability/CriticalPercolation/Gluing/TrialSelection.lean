import Mathlib

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation

theorem separated_subset_of_card {V : Type*} (C : V → V → Prop)
    (hrefl : ∀ v, C v v) (hsymm : ∀ {v w}, C v w → C w v)
    (M N : ℕ) (hM : 0 < M) (S : Finset V)
    (hb : ∀ v∈S, (S.filter (C v)).card ≤ M) (hcard : M*N ≤ S.card) :
    ∃ U ⊆ S, U.card=N ∧ (U : Set V).Pairwise (fun v w => ¬C v w) := by
  induction N generalizing S with
  | zero => exact ⟨∅,Finset.empty_subset _,by simp,by simp⟩
  | succ N ih =>
    have hSpos : 0 < S.card := by nlinarith
    obtain ⟨v,hv⟩ := Finset.card_pos.mp hSpos
    let T := S.filter (fun w => ¬C v w)
    have hT : T ⊆ S := Finset.filter_subset _ _
    have hbT : ∀ w∈T, (T.filter (C w)).card ≤ M := by
      intro w hw
      exact (Finset.card_le_card (Finset.filter_subset_filter _ hT)).trans (hb w (hT hw))
    have hcT : M*N ≤ T.card := by
      have he := S.card_filter_add_card_filter_not (C v)
      have hh := hb v hv
      change M*N ≤ (S.filter (fun w => ¬C v w)).card
      nlinarith
    obtain ⟨U,hUT,hUc,hUp⟩ := ih T hbT hcT
    have hvU : v∉U := by
      intro h
      exact (Finset.mem_filter.mp (hUT h)).2 (hrefl v)
    refine ⟨insert v U,Finset.insert_subset hv (hUT.trans hT),by simp [hvU,hUc],?_⟩
    intro x hx y hy hxy
    simp only [Finset.coe_insert,Set.mem_insert_iff] at hx hy
    rcases hx with rfl|hx  <;> rcases hy with rfl|hy
    · exact (hxy rfl).elim
    · exact (Finset.mem_filter.mp (hUT hy)).2
    · intro h
      exact (Finset.mem_filter.mp (hUT hx)).2 (hsymm h)
    · exact hUp hx hy hxy

theorem exists_weight_interval {V : Type*} (S : Finset V) (s : V → ℝ)
    (hs : ∀ v∈S, s v ≤ 1) (K : ℝ) (hK : 0 ≤ K) (hSK : K ≤ ∑ v∈S, s v) :
    ∃ U ⊆ S, K ≤ ∑ v∈U, s v ∧ (∑ v∈U, s v) ≤ K+1 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨∅,by simp,by simpa using hSK,by simp; linarith⟩
  | @insert v S hv ih =>
    by_cases h : K ≤ ∑ w∈S, s w
    · obtain ⟨U,hU,hlo,hhi⟩ := ih (fun w hw => hs w (Finset.mem_insert_of_mem hw)) h
      exact ⟨U,hU.trans (Finset.subset_insert _ _),hlo,hhi⟩
    · refine ⟨insert v S,Finset.Subset.refl _,hSK,?_⟩
      rw [Finset.sum_insert hv]
      have hh := hs v (Finset.mem_insert_self _ _)
      linarith

theorem separated_weighted_trials {V : Type*} (C : V → V → Prop)
    (hrefl : ∀ v, C v v) (hsymm : ∀ {v w}, C v w → C w v)
    (M N : ℕ) (hM : 0 < M) (S : Finset V)
    (hb : ∀ v∈S, (S.filter (C v)).card ≤ M) (hcard : M*N ≤ S.card)
    (s : V → ℝ) (s₀ K : ℝ) (hK : 0 ≤ K)
    (hs : ∀ v∈S, s₀ ≤ s v ∧ s v ≤ 1) (hN : K ≤ N*s₀) :
    ∃ U ⊆ S, (U : Set V).Pairwise (fun v w => ¬C v w) ∧
      K ≤ ∑ v∈U, s v ∧ (∑ v∈U, s v) ≤ K+1 := by
  obtain ⟨T,hTS,hTc,hTp⟩ := separated_subset_of_card C hrefl hsymm M N hM S hb hcard
  have hKT : K ≤ ∑ v∈T, s v := by
    calc K ≤ N*s₀ := hN
         _ = ∑ _v∈T, s₀ := by simp [hTc]
         _  ≤  _ := Finset.sum_le_sum (fun v hv => (hs v (hTS hv)).1)
  obtain ⟨U,hUT,hlo,hhi⟩ := exists_weight_interval T s (fun v hv => (hs v (hTS hv)).2)
    K hK hKT
  exact ⟨U,hUT.trans hTS,hTp.mono hUT,hlo,hhi⟩

end CriticalPercolation
end
end
end

end OAI
