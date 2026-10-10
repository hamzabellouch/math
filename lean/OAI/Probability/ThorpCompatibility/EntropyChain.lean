import Mathlib
import OAI.Probability.ThorpCompatibility.ConditionalEntropy

namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

lemma entropy_eq_of_fibers (P : Law α) (X : α → β) (Y : α → γ)
    (hf : ∀ a b, X a = X b ↔ Y a = Y b) : (P.map X).entropy = (P.map Y).entropy := by
  have hm (a : α) : (P.map X).mass (X a) = (P.map Y).mass (Y a) := by
    simp only [map]
    apply Finset.sum_congr rfl
    intro b _
    rw [hf b a]
  unfold entropy
  rw [P.mean_map, P.mean_map]
  simp only [Function.comp_def, hm]

lemma condEntropy_chain (P : Law α) (X : α → β) (Y : α → γ) (Z : α → δ) :
    P.condEntropy (fun a => (X a, Y a)) Z =
      P.condEntropy X Z + P.condEntropy Y (fun a => (X a, Z a)) := by
  have h := P.entropy_eq_of_fibers (fun a => ((X a, Y a), Z a))
    (fun a => (Y a, (X a, Z a))) (by intro a b; simp only [Prod.mk.injEq]; tauto)
  simp only [condEntropy]
  rw [h]
  ring

lemma condEntropy_le_entropy (P : Law α) (X : α → β) (Y : α → γ) :
    P.condEntropy X Y ≤ (P.map X).entropy := by
  have h := P.condEntropy_le_prediction X Y (fun _ => P.map X)
    (fun a ha => P.map_mass_pos X ha)
  simpa [entropy, P.mean_map, Function.comp_def] using h

lemma entropy_pair_le (P : Law α) (X : α → β) (Y : α → γ) :
    (P.map (fun a => (X a, Y a))).entropy ≤ (P.map X).entropy + (P.map Y).entropy := by
  have h := P.condEntropy_le_entropy X Y
  unfold condEntropy at h
  linarith

noncomputable def history {n : ℕ} (X : Fin n → α → β) (t : ℕ) (a : α) :
    Fin n → Option β := fun i => if (i : ℕ) < t then some (X i a) else none

omit [Fintype α] [Fintype β] in
lemma history_eq_iff {n : ℕ} (X : Fin n → α → β) (t : ℕ) (a b : α) :
    history X t a = history X t b ↔ ∀ i : Fin n, (i : ℕ) < t → X i a = X i b := by
  constructor
  · intro h i hi
    have he := congrFun h i
    simpa [history, hi] using he
  · intro h
    funext i
    by_cases hi : (i : ℕ) < t
    · simp [history, hi, h i hi]
    · simp [history, hi]

omit [Fintype α] [Fintype β] [Fintype γ] in
lemma history_step_fibers {n : ℕ} (X : Fin n → α → β) (Y : α → γ)
    (i : Fin n) (a b : α) :
    (X i a, (Y a, history X i a)) = (X i b, (Y b, history X i b)) ↔
      (Y a, history X (i + 1) a) = (Y b, history X (i + 1) b) := by
  simp only [Prod.mk.injEq, history_eq_iff]
  constructor
  · rintro ⟨hi, hY, hprev⟩
    refine ⟨hY, fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
    · exact hprev j hlt
    · have he : j = i := Fin.ext heq
      simpa [he] using hi
  · rintro ⟨hY, hprev⟩
    exact ⟨hprev i (Nat.lt_succ_self _), hY,
      fun j hj => hprev j (Nat.lt_succ_of_lt hj)⟩

lemma sum_fin_telescope (n : ℕ) (f : ℕ → ℝ) :
    (∑ i : Fin n, (f (i + 1) - f i)) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    ring

lemma entropy_chain_history {n : ℕ} (P : Law α) (X : Fin n → α → β) (Y : α → γ) :
    (∑ i : Fin n, P.condEntropy (X i) (fun a => (Y a, history X i a))) =
      P.condEntropy (fun a i => X i a) Y := by
  let F : ℕ → ℝ := fun t => (P.map (fun a => (Y a, history X t a))).entropy
  have hs (i : Fin n) :
      P.condEntropy (X i) (fun a => (Y a, history X i a)) = F (i + 1) - F i := by
    unfold condEntropy F
    rw [P.entropy_eq_of_fibers _ _ (history_step_fibers X Y i)]
  simp_rw [hs]
  rw [sum_fin_telescope]
  have hfull : F n = (P.map (fun a => ((fun i => X i a), Y a))).entropy := by
    apply P.entropy_eq_of_fibers
    intro a b
    simp only [Prod.mk.injEq]
    rw [history_eq_iff]
    simp only [funext_iff]
    constructor
    · rintro ⟨hY, hX⟩
      exact ⟨fun i => hX i i.isLt, hY⟩
    · rintro ⟨hX, hY⟩
      exact ⟨hY, fun i _ => hX i⟩
  have hzero : F 0 = (P.map Y).entropy := by
    apply P.entropy_eq_of_fibers
    intro a b
    simp only [Prod.mk.injEq]
    rw [history_eq_iff]
    simp
  rw [hfull, hzero]
  rfl

lemma entropy_chain {n : ℕ} (P : Law α) (X : Fin n → α → β) :
    (∑ i : Fin n, P.condEntropy (X i) (history X i)) =
      (P.map (fun a i => X i a)).entropy := by
  have h := P.entropy_chain_history X (fun _ => ())
  have he (i : Fin n) :
      P.condEntropy (X i) (fun a => ((), history X i a)) =
        P.condEntropy (X i) (history X i) := by
    unfold condEntropy
    have h₁ := P.entropy_eq_of_fibers (fun a => (X i a, ((), history X i a)))
      (fun a => (X i a, history X i a)) (by intro a b; simp)
    have h₂ := P.entropy_eq_of_fibers (fun a => ((), history X i a))
      (history X i) (by intro a b; simp)
    rw [h₁, h₂]
  simp_rw [he] at h
  simpa [P.condEntropy_const] using h

lemma entropy_tuple_le {n : ℕ} (P : Law α) (X : Fin n → α → β) :
    (P.map (fun a i => X i a)).entropy ≤ ∑ i, (P.map (X i)).entropy := by
  rw [← P.entropy_chain X]
  exact Finset.sum_le_sum fun i _ => P.condEntropy_le_entropy (X i) (history X i)

end Law
end ThorpCompatibility

end OAI
