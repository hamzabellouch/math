import Mathlib
import OAI.Combinatorics.KMedian.Preparation.RepresentativeGeometry
import OAI.Combinatorics.KMedian.Optimization.ComputedNearest

namespace OAI


                                               
section
namespace MetricKMedian.Preparation.RationalRepresentatives
open Finset
variable {n : ℕ}

def select (d : Fin n → Fin n → ℚ) (V : Fin n → ℚ) (M : ℚ) :
    ℕ → Finset (Fin n) → Finset (Fin n)
  | 0, _ => ∅
  | k+1, U => if hU : U.Nonempty then
      let s := firstNearest U V hU
      insert s (select d V M k (U.filter (fun j => M*V j < d j s)))
    else ∅

theorem select_spec (d : Fin n → Fin n → ℚ) (V : Fin n → ℚ) (M : ℚ)
    (hd0 : ∀ j, d j j=0) (hds : ∀ i j, d i j=d j i) (hM : 0 ≤ M)
    (k : ℕ) (U : Finset (Fin n)) (hk : U.card ≤ k) (hV : ∀ j ∈ U, 0 ≤ V j) :
    select d V M k U ⊆ U ∧
      (↑(select d V M k U) : Set (Fin n)).Pairwise
        (fun s t => M*max (V s) (V t) < d s t) ∧
      ∀ j ∈ U, ∃ s ∈ select d V M k U, V s ≤ V j ∧ d j s ≤ M*V j := by
  induction k generalizing U with
  | zero =>
      have he : U=∅ := card_eq_zero.mp (Nat.eq_zero_of_le_zero hk)
      simp [select, he]
  | succ k ih =>
      by_cases hU : U.Nonempty
      · let s := firstNearest U V hU
        have hs : s ∈ U := (firstNearest_spec U V hU).1
        have hmin : ∀ j ∈ U, V s ≤ V j := (firstNearest_spec U V hU).2
        let W := U.filter (fun j => M*V j < d j s)
        have hWU : W ⊆ U := filter_subset _ _
        have hsW : s ∉ W := by
          intro hh
          have h := (mem_filter.mp hh).2
          rw [hd0] at h
          exact not_lt_of_ge (mul_nonneg hM (hV s hs)) h
        have hwk : W.card ≤ k := by
          have hproper : W ⊂ U := Finset.ssubset_iff_subset_ne.mpr ⟨hWU, fun he => hsW (he ▸ hs)⟩
          have hc := card_lt_card hproper
          omega
        obtain ⟨hsub,hpair,hcover⟩ := ih W hwk (fun j hj => hV j (hWU hj))
        simp only [select, dite_eq_left hU]
        change insert s (select d V M k W) ⊆ U ∧ _
        refine ⟨insert_subset hs (hsub.trans hWU), ?_, ?_⟩
        · intro a ha b hb hab
          rcases mem_insert.mp ha with rfl | ha
          · have hb' := (mem_insert.mp hb).resolve_left (Ne.symm hab)
            have hbW := hsub hb'
            rw [max_eq_right (hmin b (hWU hbW)),hds]
            exact (mem_filter.mp hbW).2
          · rcases mem_insert.mp hb with rfl | hb
            · have haW := hsub ha
              rw [max_eq_left (hmin a (hWU haW))]
              exact (mem_filter.mp haW).2
            · exact hpair ha hb hab
        · intro j hj
          by_cases hjW : j ∈ W
          · obtain ⟨a,ha,hv,hd⟩ := hcover j hjW
            exact ⟨a,mem_insert_of_mem ha,hv,hd⟩
          · exact ⟨s,mem_insert_self _ _,hmin j hj,
              le_of_not_gt (fun h => hjW (mem_filter.mpr ⟨hj,h⟩))⟩
      · have he := not_nonempty_iff_eq_empty.mp hU
        simp [select, he]

def representatives (d : Fin n → Fin n → ℚ) (V : Fin n → ℚ) (M : ℚ) : Finset (Fin n) :=
  select d V M n univ

theorem representatives_spec (d : Fin n → Fin n → ℚ) (V : Fin n → ℚ) (M : ℚ)
    (hd0 : ∀ j, d j j=0) (hds : ∀ i j, d i j=d j i) (hM : 0 ≤ M)
    (hV : ∀ j, 0 ≤ V j) :
    (↑(representatives d V M) : Set (Fin n)).Pairwise
        (fun s t => M*max (V s) (V t) < d s t) ∧
      ∀ j, ∃ s ∈ representatives d V M, V s ≤ V j ∧ d j s ≤ M*V j := by
  have hh := select_spec d V M hd0 hds hM n univ (by simp) (fun j _ => hV j)
  exact ⟨hh.2.1, fun j => hh.2.2 j (mem_univ _)⟩

end MetricKMedian.Preparation.RationalRepresentatives
end

end OAI
