import OAI.MeasureTheory.Falconer.Recursion.Ledger
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace OAI

namespace PlanarFalconer
open Finset

theorem exists_last_crossing (B : ℕ → ℝ) (N : ℕ) (β : ℝ) (h0 : B 0 ≤ β) :
    ∃ c, c ≤ N ∧ B c ≤ β ∧ ∀ n, c < n → n ≤ N → β < B n := by
  classical
  let s := (Finset.range (N+1)).filter fun n => B n ≤ β
  have hs : s.Nonempty := ⟨0, by simp [s,h0]⟩
  refine ⟨s.max' hs, ?_, ?_, ?_⟩
  · have := (Finset.mem_filter.mp (s.max'_mem hs)).1
    exact Nat.le_of_lt_succ (Finset.mem_range.mp this)
  · exact (Finset.mem_filter.mp (s.max'_mem hs)).2
  · intro n hcn hn
    by_contra h
    have hmem : n ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),not_lt.mp h⟩
    have := s.le_max' n hmem
    omega

theorem last_crossing_tail (B : ℕ → ℝ) {N c : ℕ} {β e : ℝ}
    (hcN : c ≤ N) (hc : B c ≤ β) (hN : β < B N) (he : 0 ≤ e)
    (hlast : ∀ n, c < n → n ≤ N → β < B n)
    (hstep : ∀ n < N, B (n+1) ≤ B n+e) :
    c < N ∧ ∀ n, c ≤ n → n ≤ N → β-e ≤ B n := by
  have hcN' : c < N := by
    by_contra h
    have : c = N := by omega
    subst c
    linarith
  refine ⟨hcN', ?_⟩
  intro n hcn hnN
  by_cases hnc : n = c
  · subst n
    have := hlast (c+1) (by omega) (by omega)
    have := hstep c hcN'
    linarith
  · have := hlast n (by omega) hnN
    linarith

theorem min_step (A B : ℕ → ℝ) {n : ℕ} {e : ℝ}
    (hA : A (n+1) ≤ A n+e) (hB : B (n+1) ≤ B n+e) :
    min (A (n+1)) (B (n+1)) ≤ min (A n) (B n)+e := by
  by_cases h : A n ≤ B n
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans hA
  · rw [min_eq_right (le_of_not_ge h)]
    exact (min_le_right _ _).trans hB

theorem min_height_le (A B : ℕ → ℝ) (c : ℕ) {β d : ℝ}
    (hc : min (A c) (B c) ≤ β)
    (hA : ∀ n ≤ c, -d ≤ A n) (hB : ∀ n ≤ c, -d ≤ B n) :
    min (height A 0 c) (height B 0 c) ≤ β+d := by
  have hminA : -d ≤ intervalMin A 0 c := by
    obtain ⟨i,_,hi,he⟩ := intervalMin_attained A (Nat.zero_le c)
    rw [he]
    exact hA i hi
  have hminB : -d ≤ intervalMin B 0 c := by
    obtain ⟨i,_,hi,he⟩ := intervalMin_attained B (Nat.zero_le c)
    rw [he]
    exact hB i hi
  rcases le_total (A c) (B c) with h | h
  · rw [min_eq_left h] at hc
    apply (min_le_left _ _).trans
    unfold height
    linarith
  · rw [min_eq_right h] at hc
    apply (min_le_right _ _).trans
    unfold height
    linarith

theorem outer_exponent_identity (a₁ a₂ k V₁ V₂ : ℝ) :
    -a₁-a₂+k+((2*a₁-V₁)+(2*a₂-V₂))/2 = k-(V₁+V₂)/2 := by ring

theorem outer_profile_gain (A B : ℕ → ℝ) {c N Q : ℕ} {β d e : ℝ}
    (hQ : 0 < Q) (hw : c+Q ≤ N)
    (hc : min (A c) (B c) ≤ β)
    (hA : ∀ n ≤ c, -d ≤ A n) (hB : ∀ n ≤ c, -d ≤ B n)
    (htail : ∀ n, c ≤ n → n ≤ N → β-e ≤ min (A n) (B n)) :
    -A c-B c+min (height A 0 c) (height B 0 c)+
      ((2*A c-potential A c N Q)+(2*B c-potential B c N Q))/2 ≤
        -β+d+2*e := by
  rw [outer_exponent_identity]
  have hk := min_height_le A B c hc hA hB
  have hVA := potential_lower A hQ hw (fun n hcn hnN =>
    (htail n hcn hnN).trans (min_le_left _ _))
  have hVB := potential_lower B hQ hw (fun n hcn hnN =>
    (htail n hcn hnN).trans (min_le_right _ _))
  linarith

theorem parameter_loss_bound {β κ lam sig : ℝ}
    (hβ : 0 < β) (hκ : 0 < κ) (hκ1 : κ < 1)
    (_hlam : 0 ≤ lam) (hsig : 0 ≤ sig)
    (hsmall : 1000000*κ < β)
    (hratio : 10000000*(lam+sig)/κ < β/100) :
    500*κ + 1000000*(lam+sig)/κ + 4000*(lam+sig) + 5*lam < β/2 := by
  have hr := (div_lt_iff₀ hκ).mp hratio
  have hβκ : β*κ < β := by nlinarith
  have hsum : 1000000000*(lam+sig) < β := by nlinarith
  have hdiv : 1000000*(lam+sig)/κ < β/1000 := by
    apply (div_lt_iff₀ hκ).mpr
    nlinarith
  linarith

theorem entry_depth_bounds (B : ℕ → ℝ) {c N : ℕ} {β δ lam : ℝ}
    (hN : 0 < (N : ℝ)) (hδ : 0 < δ) (hβ : β = δ/10)
    (hlam : lam < δ/1000) (hlarge : 2 ≤ β*(N : ℝ))
    (_hcN : c < N) (hc : B c ≤ β) (hnext : β < B (c+1))
    (hlower : δ*((c : ℝ)/(N : ℝ))-5*lam ≤ B c)
    (hupper : B (c+1) ≤ ((c+1 : ℕ) : ℝ)/(N : ℝ)) :
    β*(N : ℝ)/2 ≤ (c : ℝ) ∧ (c : ℝ) < (N : ℝ)/4 := by
  have hlo : β*(N : ℝ) < (c : ℝ)+1 := by
    have hh := (lt_div_iff₀ hN).mp (hnext.trans_le hupper)
    simpa only [Nat.cast_add,Nat.cast_one] using hh
  have hratio : (c : ℝ)/(N : ℝ) < 1/4 := by nlinarith
  have hhi := (div_lt_iff₀ hN).mp hratio
  constructor <;> nlinarith

end PlanarFalconer

end OAI
