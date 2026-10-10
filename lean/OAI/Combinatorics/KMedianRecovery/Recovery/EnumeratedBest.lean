import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.LocalIndex
import OAI.Combinatorics.KMedianRecovery.Branching.BranchTapeSuccess

namespace OAI

namespace MetricKMedianRecovery.FiniteSampling
variable {I Y : Type*} [Fintype I] [DecidableEq Y]
noncomputable def enumeratedBest (cost : Y → ℝ) (fallback : Y) (entry : I → Y) : Y :=
  Classical.choose (Finset.exists_min_image (insert fallback (Finset.univ.image entry))
    cost (Finset.insert_nonempty _ _))

lemma enumeratedBest_mem (cost : Y → ℝ) (fallback : Y) (entry : I → Y) :
    enumeratedBest cost fallback entry = fallback ∨ ∃ i, enumeratedBest cost fallback entry = entry i := by
  classical
  have hh := (Classical.choose_spec (Finset.exists_min_image
    (insert fallback (Finset.univ.image entry)) cost (Finset.insert_nonempty _ _))).1
  rcases Finset.mem_insert.mp hh with h | h
  · exact Or.inl h
  · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
    exact Or.inr ⟨i,hi.symm⟩

lemma enumeratedBest_le (cost : Y → ℝ) (fallback : Y) (entry : I → Y) :
    cost (enumeratedBest cost fallback entry) ≤ cost fallback ∧
      ∀ i, cost (enumeratedBest cost fallback entry) ≤ cost (entry i) := by
  classical
  have hh := (Classical.choose_spec (Finset.exists_min_image
    (insert fallback (Finset.univ.image entry)) cost (Finset.insert_nonempty _ _))).2
  exact ⟨hh _ (Finset.mem_insert_self _ _),fun i => hh _ (Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩))⟩
end MetricKMedianRecovery.FiniteSampling

namespace MetricKMedianRecovery.Sampling
open Completion Categorical FiniteSampling
variable {V : Type*} [Fintype V] [LinearOrder V] [PseudoMetricSpace V]

noncomputable def completeState (D F S : Finset V) (hSF : S ⊆ F) (hS : S.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ)
    (s : State V) (m : ℕ) (tape : Fin (localTapeBound F m) → Bool) : Finset V := by
  classical
  exact if hs : s.leaves.length ≤ m then
    enumeratedBest (realCost D) S (fun guess : Fin (m+1) × Fin (m+1) × Fin (m+1) =>
      branchTapeOutput D F S hSF hS Δ hΔ hbound s m guess.1 guess.2.1 guess.2.2 hs
        (Nat.le_of_lt_succ guess.1.isLt) tape)
  else S

lemma completeState_feasible (D F S : Finset V) (hSF : S ⊆ F) (hS : S.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ)
    (s : State V) (m : ℕ) (tape : Fin (localTapeBound F m) → Bool) :
    let out := completeState D F S hSF hS Δ hΔ hbound s m tape
    out ⊆ F ∧ out.card ≤ S.card ∧ out.Nonempty ∧ realCost D out ≤ realCost D S := by
  classical
  unfold completeState
  split_ifs with hs
  · have hcost := (enumeratedBest_le (realCost D) S (fun guess : Fin (m+1) × Fin (m+1) × Fin (m+1) =>
      branchTapeOutput D F S hSF hS Δ hΔ hbound s m guess.1 guess.2.1 guess.2.2 hs
        (Nat.le_of_lt_succ guess.1.isLt) tape)).1
    rcases enumeratedBest_mem (realCost D) S (fun guess : Fin (m+1) × Fin (m+1) × Fin (m+1) =>
      branchTapeOutput D F S hSF hS Δ hΔ hbound s m guess.1 guess.2.1 guess.2.2 hs
        (Nat.le_of_lt_succ guess.1.isLt) tape) with h | ⟨guess,h⟩
    · simpa only [h] using And.intro hSF (And.intro (le_refl S.card) (And.intro hS (le_refl (realCost D S))))
    · obtain ⟨hsub,hcard,hne⟩ := branchTapeOutput_feasible D F S hSF hS Δ hΔ hbound s m
        guess.1 guess.2.1 guess.2.2 hs (Nat.le_of_lt_succ guess.1.isLt) tape
      exact ⟨h ▸ hsub,h ▸ hcard,h ▸ hne,hcost⟩
  · exact ⟨hSF,le_refl _,hS,le_refl _⟩

lemma completeState_le (D F S : Finset V) (hSF : S ⊆ F) (hS : S.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ)
    (s : State V) (m : ℕ) (hs : s.leaves.length ≤ m) (b q c : Fin (m+1))
    (tape : Fin (localTapeBound F m) → Bool) :
    realCost D (completeState D F S hSF hS Δ hΔ hbound s m tape) ≤
      realCost D (branchTapeOutput D F S hSF hS Δ hΔ hbound s m b q c hs
        (Nat.le_of_lt_succ b.isLt) tape) := by
  classical
  unfold completeState
  rw [dite_eq_left hs]
  exact (enumeratedBest_le _ _ _).2 (b,q,c)
end MetricKMedianRecovery.Sampling

namespace MetricKMedianRecovery.Sampling.Comparison
open Completion Categorical FiniteSampling
variable {V : Type*} [Fintype V] [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

lemma completeState_success
    (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (s : State V) (hs : C.Correct hD (1/1000000) s) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (hI : C.removalTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    (hN : C.nearTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    (F : Finset V) (hSF : S ⊆ F) (hOF : O ⊆ F) (hS : S.Nonempty)
    (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ) :
    (1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ) ≤
      probability (fun tape : Fin (localTapeBound F C.bad.card) → Bool =>
        realCost D (completeState D F S hSF hS Δ hΔ hbound s C.bad.card tape) ≤
          (197/100:ℝ)*comparisonCost D C.assign) := by
  obtain ⟨b,q,c,hs',hb⟩ := C.branchTape_success hD Δ s hs hΔ hP hm hI hN F hSF hOF hS hbound
  exact hb.trans (probability_mono (fun tape ht =>
    (completeState_le D F S hSF hS Δ hΔ hbound s C.bad.card hs' b q c tape).trans ht))
end MetricKMedianRecovery.Sampling.Comparison

namespace MetricKMedianRecovery.Guided
variable {S A : Type*} [Fintype A]
open scoped Classical

noncomputable def pure (a₀ : A) : Kernel S A := by
  classical
  exact ⟨fun _ a => if a = a₀ then 1 else 0, by intros; split_ifs <;> norm_num, by intros; simp⟩

noncomputable def stoppedKernel (p : Kernel S A) (stop : S → Prop) (a₀ : A) : Kernel S A := by
  classical
  exact ⟨fun s a => if stop s then (pure a₀).weight s a else p.weight s a,
    by intro s a; split_ifs; exact (pure a₀).nonneg s a; exact p.nonneg s a,
    by
      intro state
      by_cases halted : stop state <;> simp only [halted, ite_true, ite_false]
      · exact (pure a₀).total state
      · exact p.total state⟩

noncomputable def stoppedUpdate (f : S → A → S) (stop : S → Prop) (s : S) (a : A) : S :=
  if stop s then s else f s a

noncomputable def hitMass (f : S → A → S) (p : Kernel S A) (stop : S → Prop)
    (n : ℕ) (s : S) : ℝ := eventMass f p.weight n s (Hits f stop n s)

lemma hitMass_zero (f : S → A → S) (p : Kernel S A) (stop : S → Prop) (s : S) :
    hitMass f p stop 0 s = if stop s then 1 else 0 := by
  classical
  by_cases h : stop s <;> simp [hitMass,eventMass,Hits,pathWeight,h]

lemma hitMass_succ (f : S → A → S) (p : Kernel S A) (stop : S → Prop)
    (n : ℕ) (s : S) :
    hitMass f p stop (n+1) s = if stop s then 1 else
      ∑ a : A, p.weight s a*hitMass f p stop n (f s a) := by
  classical
  by_cases hs : stop s
  · simp only [hitMass, eventMass, Hits, hs, true_or, ite_true]
    exact pathWeight_total f p (n+1) s
  · simp only [ite_eq_right hs, hitMass, eventMass]
    rw [sum_fin_succ]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro seed _
    simp only [Hits, hs, false_or, Fin.cons_zero, Fin.tail_cons, pathWeight]
    split_ifs <;> simp

lemma hitMass_eq_of_agree (f g : S → A → S) (p q : Kernel S A) (stop : S → Prop)
    (hf : ∀ s, ¬stop s → ∀ a, f s a = g s a)
    (hp : ∀ s, ¬stop s → ∀ a, p.weight s a = q.weight s a)
    (n : ℕ) (s : S) : hitMass f p stop n s = hitMass g q stop n s := by
  classical
  induction n generalizing s with
  | zero => rw [hitMass_zero,hitMass_zero]
  | succ n ih =>
    rw [hitMass_succ,hitMass_succ]
    split_ifs with hs
    · rfl
    · apply Finset.sum_congr rfl
      intro a _
      rw [hp s hs a,hf s hs a,ih]

lemma hitMass_stopped (f : S → A → S) (p : Kernel S A) (stop : S → Prop)
    (a₀ : A) (n : ℕ) (s : S) :
    hitMass (stoppedUpdate f stop) (stoppedKernel p stop a₀) stop n s =
      hitMass f p stop n s := by
  apply hitMass_eq_of_agree
  · intro s hs a
    simp only [stoppedUpdate,ite_eq_right hs]
  · intro s hs a
    simp only [stoppedKernel,ite_eq_right hs]

variable {I : Type*} [Fintype I]

noncomputable def routed (q : Kernel S I) (route : S → I → A) : Kernel S A := by
  classical
  refine ⟨fun s a => ∑ i : I, if route s i = a then q.weight s i else 0, ?_, ?_⟩
  · intro s a
    exact Finset.sum_nonneg (fun i _ => by split_ifs; exact q.nonneg s i; exact le_rfl)
  · intro s
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact q.total s

lemma routed_at (q : Kernel S I) (route : S → I → A) (s : S)
    (hinj : Function.Injective (route s)) (i : I) :
    (routed q route).weight s (route s i) = q.weight s i := by
  classical
  simp only [routed, hinj.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma routed_pos (q : Kernel S I) (route : S → I → A) (s : S) (a : A)
    (h : 0 < (routed q route).weight s a) : ∃ i, route s i = a ∧ 0 < q.weight s i := by
  classical
  obtain ⟨i,_,hi⟩ := (Finset.sum_pos_iff_of_nonneg
    (show ∀ i ∈ (Finset.univ : Finset I), 0 ≤ if route s i = a then q.weight s i else 0 from
      fun i _ => by split_ifs; exact q.nonneg s i; exact le_rfl)).mp h
  by_cases he : route s i = a
  · exact ⟨i,he,by simpa only [ite_eq_left he] using hi⟩
  · simp only [ite_eq_right he, lt_self_iff_false] at hi

lemma routed_domination (p : Kernel S A) (q : Kernel S I) (route : S → I → A)
    (hinj : ∀ s, Function.Injective (route s)) (loss : S → A → ℝ)
    (hstep : ∀ s i, loss s (route s i)*q.weight s i ≤ p.weight s (route s i))
    (s : S) (a : A) : loss s a*(routed q route).weight s a ≤ p.weight s a := by
  by_cases hq : 0 < (routed q route).weight s a
  · obtain ⟨i,hi,_⟩ := routed_pos q route s a hq
    rw [← hi,routed_at q route s (hinj s) i]
    exact hstep s i
  · have he : (routed q route).weight s a = 0 := le_antisymm (le_of_not_gt hq) ((routed q route).nonneg s a)
    rw [he,mul_zero]
    exact p.nonneg s a

def states (f : S → A → S) : (n : ℕ) → S → (Fin n → A) → Fin (n+1) → S
  | 0, s, _ => fun _ => s
  | n+1, s, seed => Fin.cases s (states f n (f s (seed 0)) (Fin.tail seed))

omit [Fintype A] in
lemma states_zero (f : S → A → S) (n : ℕ) (s : S) (seed : Fin n → A) :
    states f n s seed 0 = s := by
  cases n <;> rfl

omit [Fintype A] in
lemma states_step (f : S → A → S) (n : ℕ) (s : S) (seed : Fin n → A) (i : Fin n) :
    states f n s seed i.succ = f (states f n s seed i.castSucc) (seed i) := by
  induction n generalizing s with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [states,Fin.cases_zero,Fin.cases_succ,Fin.castSucc_zero]
      exact states_zero f n (f s (seed 0)) (Fin.tail seed)
    · simpa only [states,Fin.castSucc_succ,Fin.cases_succ,Fin.tail] using
        ih (f s (seed 0)) (Fin.tail seed) j

omit [Fintype A] in
lemma pathWeight_eq_prod (f : S → A → S) (p : S → A → ℝ)
    (n : ℕ) (s : S) (seed : Fin n → A) :
    pathWeight f p n s seed = ∏ i : Fin n, p (states f n s seed i.castSucc) (seed i) := by
  induction n generalizing s with
  | zero => simp [pathWeight]
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    simpa only [pathWeight,states,Fin.castSucc_succ,Fin.castSucc_zero,Fin.cases_zero,Fin.cases_succ,Fin.tail] using
      congrArg (fun x => p s (seed 0)*x) (ih (f s (seed 0)) (Fin.tail seed))

lemma supported_step (f : S → A → S) (p : Kernel S A)
    (n : ℕ) (s : S) (seed : Fin n → A)
    (hseed : 0 < pathWeight f p.weight n s seed) (i : Fin n) :
    0 < p.weight (states f n s seed i.castSucc) (seed i) := by
  rw [pathWeight_eq_prod] at hseed
  have hh := (Finset.prod_ne_zero_iff).mp (ne_of_gt hseed) i (Finset.mem_univ i)
  exact lt_of_le_of_ne (p.nonneg _ _) (Ne.symm hh)

lemma states_invariant (f : S → A → S) (p : Kernel S A) (Inv : S → Prop)
    (hstep : ∀ s, Inv s → ∀ a, 0 < p.weight s a → Inv (f s a))
    (n : ℕ) (s : S) (hs : Inv s) (seed : Fin n → A)
    (hseed : 0 < pathWeight f p.weight n s seed) (i : Fin (n+1)) :
    Inv (states f n s seed i) := by
  refine Fin.induction ?_ (fun j hj => ?_) i
  · simpa only [states_zero] using hs
  · rw [states_step]
    exact hstep _ hj _ (supported_step f p n s seed hseed j)

end MetricKMedianRecovery.Guided

end OAI
