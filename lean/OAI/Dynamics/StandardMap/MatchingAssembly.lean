import OAI.Dynamics.StandardMap.ManyGood

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy

lemma matching_subset (S B : Finset ℕ) (τ ρ : ℕ → ℝ) (N : ℕ) (c : ℝ)
    (hc : 1/2 < c) (hN : 2 ≤ N)
    (hρ : ∀ j, 1 ≤ j → j < N → ρ (j+1)-ρ j ≤ 1) (hρ1 : ρ 1=0)
    (hrange : ∀ j ∈ S, 1 < τ j ∧ τ j ≤ ρ N)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i < j → c*((j:ℝ)-(i:ℝ)) ≤ τ j-τ i)
    (hgood : ∀ i, 2 ≤ i → i ≤ N → i ∉ B → ∀ j, 2 ≤ j → j < i →
      c*((i:ℝ)-(j:ℝ)) ≤ ρ i-ρ j) :
    ∃ (T : Finset ℕ) (f : ℕ → ℕ), T ⊆ S ∧ S.card ≤ 3*T.card+2*B.card+2 ∧
      (∀ i ∈ T, 2 ≤ f i ∧ f i ≤ N ∧ f i ∉ B ∧ |τ i-ρ (f i)| ≤ 1/2) ∧
      (∀ i ∈ T, ∀ j ∈ T, i < j → f i < f j) := by
  classical
  have hex : ∀ i ∈ S, ∃ k, 2 ≤ k ∧ k ≤ N ∧ |τ i-ρ k| ≤ 1/2 := by
    intro i hi
    obtain ⟨k,hk2,hkN,hk⟩:=half_unit_crossing ρ N (τ i) hρ hρ1 (hrange i hi).1 (by omega) (hrange i hi).2
    exact ⟨k,hk2,hkN,by simpa only [abs_sub_comm] using hk⟩
  have hex' : ∀ i, ∃ k, i ∈ S → 2 ≤ k ∧ k ≤ N ∧ |τ i-ρ k| ≤ 1/2 := by
    intro i
    by_cases hi : i ∈ S
    · obtain ⟨k,hk⟩:=hex i hi
      exact ⟨k,fun _ => hk⟩
    · exact ⟨0,fun h => False.elim (hi h)⟩
  choose f hf using hex'
  let R := S.filter fun i => f i ∉ B
  have hR : R ⊆ S := Finset.filter_subset _ _
  have hloss := discard_bad_matches S B τ ρ f c hc hsep (fun i hi => (hf i hi).2.2)
  have hcard := Finset.card_filter_add_card_filter_not (s := S) (fun i => f i ∈ B)
  have horder : ∀ i ∈ R, ∀ j ∈ R, f j ≤ f i → ρ (f j) ≤ ρ (f i) := by
    intro i hi j hj hij
    by_cases he : f j=f i
    · simp [he]
    · have hi' := hf i (hR hi)
      have hj' := hf j (hR hj)
      have hh:=hgood (f i) hi'.1 hi'.2.1 (Finset.mem_filter.mp hi).2
        (f j) hj'.1 (lt_of_le_of_ne hij he)
      have hd : (f j:ℝ) ≤ (f i:ℝ) := by exact_mod_cast hij
      nlinarith
  obtain ⟨T,hTR,hT,hord⟩:=spaced_matched_subset R τ ρ f c hc
    (fun i hi j hj hij => hsep i (hR hi) j (hR hj) hij)
    (fun i hi => (hf i (hR hi)).2.2) horder
  refine ⟨T,f,hTR.trans hR,?_,?_,hord⟩
  · have hdiv : R.card ≤ 3*(R.card/3)+2 := by omega
    dsimp [R] at hT hdiv
    omega
  · intro i hi
    have hi' := hTR hi
    have hh := hf i (hR hi')
    exact ⟨hh.1,hh.2.1,(Finset.mem_filter.mp hi').2,hh.2.2⟩

lemma log_path_bounds (τ : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ i, 1 ≤ i → i < N → τ (i+1)-τ i ≤ 1) (h1 : τ 1=0) :
    ∀ j, 1 ≤ j → j ≤ N → τ N-((N:ℝ)-(j:ℝ)) ≤ τ j ∧ τ j ≤ (j:ℝ)-1 := by
  have hinc : ∀ a b : ℕ, 1 ≤ a → a ≤ b → b ≤ N → τ b-τ a ≤ (b:ℝ)-(a:ℝ) := by
    intro a b ha hab hb
    induction b,hab using Nat.le_induction with
    | base => simp
    | succ b hab ih =>
      have ih' := ih (by omega)
      have hs := hstep b (by omega) (by omega)
      push_cast
      linarith
  intro j hj hjN
  have hleft:=hinc j N hj hjN le_rfl
  have hright:=hinc 1 j (by omega) hj hjN
  rw [h1] at hright
  norm_num at hright
  exact ⟨by linarith,by linarith⟩
end StandardMapEntropy

end OAI
