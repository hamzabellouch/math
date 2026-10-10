import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.State2

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open Sampling
variable {n : ℕ}
structure State (n : ℕ) where
  deleted : Finset (Fin n)
  leaves : List (Fin n×ℚ)
def State.real (s : State n) : Sampling.State (Fin n) :=
  ⟨s.deleted,s.leaves.map (fun z=>(z.1,(z.2:ℝ)))⟩
def tagId (t : Tag (Fin n)) : ℕ := match ofLex t with
  | .inl v=>v.val
  | .inr j=>n+j
lemma tagId_le_iff (t u : Tag (Fin n)) : tagId t≤tagId u ↔ t≤u := by
  cases t using Sum.rec with
  | inl a =>
    cases u using Sum.rec with
    | inl b =>
      change a.val≤b.val ↔ toLex (Sum.inl a:Fin n⊕ℕ)≤toLex (Sum.inl b)
      exact (@Sum.Lex.inl_le_inl_iff (Fin n) ℕ _ _ a b).symm
    | inr b =>
      change a.val≤n+b ↔ toLex (Sum.inl a:Fin n⊕ℕ)≤toLex (Sum.inr b)
      exact iff_of_true (by omega) (Sum.Lex.inl_le_inr a b)
  | inr a =>
    cases u using Sum.rec with
    | inl b =>
      change n+a≤b.val ↔ toLex (Sum.inr a:Fin n⊕ℕ)≤toLex (Sum.inl b)
      exact iff_of_false (by omega) Sum.Lex.not_inr_le_inl
    | inr b =>
      change n+a≤n+b ↔ toLex (Sum.inr a:Fin n⊕ℕ)≤toLex (Sum.inr b)
      rw [Sum.Lex.inr_le_inr_iff]
      omega
lemma tagId_injective : Function.Injective (tagId (n:=n)) := by
  intro t u h
  exact le_antisymm ((tagId_le_iff t u).mp h.le) ((tagId_le_iff u t).mp h.ge)
def tagDistance (δ : Fin n→Fin n→ℚ) (Δ : ℚ) (s : State n) (w : Fin n) (t : Tag (Fin n)) : ℚ :=
  match ofLex t with
  | .inl v=>δ w v
  | .inr 0=>Δ
  | .inr (j+1)=>match s.leaves[j]? with
    | some z=>δ w z.1+z.2
    | none=>Δ
section Metric
variable [PseudoMetricSpace (Fin n)] (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
include hδ in
lemma tagDistance_cast (Δ : ℚ) (s : State n) (w : Fin n) (t : Tag (Fin n)) :
    (tagDistance δ Δ s w t:ℝ)=Sampling.tagDistance (Δ:ℝ) s.real w t := by
  cases ht : ofLex t with
  | inl v=>simp only [tagDistance,Sampling.tagDistance,ht,hδ]
  | inr j=>
    cases j with
    | zero=>simp only [tagDistance,Sampling.tagDistance,ht]
    | succ j=>
      simp only [tagDistance,Sampling.tagDistance,ht,State.real,List.getElem?_map]
      cases hz : s.leaves[j]? <;> simp only [Option.map_none,Option.map_some,Rat.cast_add,hδ]
def key (Δ : ℚ) (s : State n) (w : Fin n) (t : Tag (Fin n)) : ℚ ×ₗ ℕ :=
  toLex (tagDistance δ Δ s w t,tagId t)
include hδ in
lemma key_le_iff (Δ : ℚ) (s : State n) (w : Fin n) (t u : Tag (Fin n)) :
    key δ Δ s w t≤ key δ Δ s w u ↔
      toLex (Sampling.tagDistance (Δ:ℝ) s.real w t,t)≤toLex (Sampling.tagDistance (Δ:ℝ) s.real w u,u) := by
  rw [←tagDistance_cast δ hδ Δ s w t,←tagDistance_cast δ hδ Δ s w u]
  simp only [key,Prod.Lex.le_iff,ofLex_toLex,Rat.cast_lt,Rat.cast_inj,tagId_le_iff]
noncomputable def keys (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) : Finset (ℚ ×ₗ ℕ) :=
  (Sampling.tags S s.real).image (key δ Δ s w)
omit [PseudoMetricSpace (Fin n)] in
lemma keys_nonempty (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) :
    (keys δ S Δ s w).Nonempty := (Sampling.tags_nonempty S s.real).image _
include hδ in
lemma minimum_key (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) :
    (keys δ S Δ s w).min' (keys_nonempty δ S Δ s w)=key δ Δ s w (Sampling.chosen S (Δ:ℝ) s.real w) := by
  apply le_antisymm
  · exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨_,Sampling.chosen_mem S (Δ:ℝ) s.real w,rfl⟩)
  · apply Finset.le_min'
    intro x hx
    obtain ⟨t,ht,rfl⟩:=Finset.mem_image.mp hx
    exact (key_le_iff δ hδ Δ s w _ t).mpr (Sampling.chosen_key_le S (Δ:ℝ) s.real w ht)
include hδ in
lemma minimum_reference (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) :
    ((ofLex ((keys δ S Δ s w).min' (keys_nonempty δ S Δ s w))).1:ℝ)=Sampling.reference S (Δ:ℝ) s.real w := by
  rw [minimum_key δ hδ]
  exact tagDistance_cast δ hδ Δ s w _
end Metric
end MetricKMedianRecovery.RationalSampling

end OAI
