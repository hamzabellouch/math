import OAI.Computability.PerfectCompleteness.Foundations.DummyEliminationLemmas
import OAI.Computability.PerfectCompleteness.Reduction.TargetGameLemmas

namespace OAI


namespace PerfectCompleteness.ExactConditionalOutput

open scoped BigOperators Classical

noncomputable section

variable {S X : Type*} {E : S → Type*} [∀ s, Fintype (E s)]
  (count : ∀ s, E s → Nat)

def enumeration (s : S) : E s ≃ Fin (Fintype.card (E s)) := Fintype.equivFin _

def copies (s : S) : List (E s) :=
  (List.ofFn fun i : Fin (Fintype.card (E s)) =>
    List.replicate (count s ((enumeration s).symm i)) ((enumeration s).symm i)).flatten

theorem copies_length (s : S) : (copies count s).length = ∑ e, count s e := by
  simp only [copies, List.length_flatten, List.map_ofFn, Function.comp_def,
    List.length_replicate, List.sum_ofFn]
  exact (enumeration s).symm.sum_comp (fun e : E s => count s e)

theorem copies_filter_length (s : S) (keep : E s → Bool) :
    ((copies count s).filter keep).length = ∑ e, if keep e then count s e else 0 := by
  simp only [copies, List.filter_flatten, List.length_flatten, List.map_ofFn,
    List.sum_ofFn]
  calc
    _ = ∑ i : Fin (Fintype.card (E s)),
        if keep ((enumeration s).symm i) then count s ((enumeration s).symm i) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      cases h : keep ((enumeration s).symm i) <;> simp [h]
    _ = _ := (enumeration s).symm.sum_comp
      (fun e : E s => if keep e then count s e else 0)

section Lists

variable {α : Type*} (shape : X → S) (entries : (x : X) → E (shape x) → α)

def localOutput (x : X) : List α := (copies count (shape x)).map (entries x)

def output (xs : List X) : List α := xs.flatMap (localOutput count shape entries)

theorem localOutput_length (D : Nat) (htotal : ∀ s, ∑ e, count s e = D) (x : X) :
    (localOutput count shape entries x).length = D := by
  rw [localOutput, List.length_map, copies_length, htotal]

theorem output_length (D : Nat) (htotal : ∀ s, ∑ e, count s e = D) (xs : List X) :
    (output count shape entries xs).length = D * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change (localOutput count shape entries x ++ output count shape entries xs).length = _
      rw [List.length_append, localOutput_length count shape entries D htotal, ih,
        List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

theorem output_nonempty (D : Nat) (hD : 0 < D) (htotal : ∀ s, ∑ e, count s e = D)
    (xs : List X) (hxs : xs ≠ []) : output count shape entries xs ≠ [] := by
  intro hempty
  have hlength := output_length count shape entries D htotal xs
  have hxpos : 0 < xs.length := by
    cases xs with
    | nil => exact False.elim (hxs rfl)
    | cons x xs => simp
  rw [hempty, List.length_nil] at hlength
  exact (Nat.ne_of_gt (Nat.mul_pos hD hxpos)) hlength.symm

def localCount (accepts : α → Bool) (x : X) : Nat :=
  ∑ e, if accepts (entries x e) then count (shape x) e else 0

theorem localOutput_filter_length (accepts : α → Bool) (x : X) :
    ((localOutput count shape entries x).filter accepts).length =
      localCount count shape entries accepts x := by
  simpa only [localOutput, localCount, List.filter_map, List.length_map, Function.comp_def]
    using copies_filter_length count (shape x) (fun e => accepts (entries x e))

theorem output_filter_length (xs : List X) (accepts : α → Bool) :
    ((output count shape entries xs).filter accepts).length =
      (xs.map (localCount count shape entries accepts)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change ((localOutput count shape entries x ++ output count shape entries xs).filter
        accepts).length = _
      rw [List.filter_append, List.length_append, localOutput_filter_length, ih]
      rfl

def conditionalRate (D : Nat) (accepts : α → Bool) (x : X) : ℝ :=
  ∑ e, if accepts (entries x e) then (count (shape x) e : ℝ) / D else 0

def average (D : Nat) (xs : List X) (accepts : α → Bool) : ℝ :=
  (xs.map (conditionalRate count shape entries D accepts)).sum / xs.length

theorem localCount_div (D : Nat) (accepts : α → Bool) (x : X) :
    (localCount count shape entries accepts x : ℝ) / D =
      conditionalRate count shape entries D accepts x := by
  rw [localCount, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  cases accepts (entries x e) <;> simp

theorem conditionalRate_sum (D : Nat) (xs : List X) (accepts : α → Bool) :
    (xs.map (conditionalRate count shape entries D accepts)).sum =
      ((xs.map (localCount count shape entries accepts)).sum : ℝ) / D := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, Nat.cast_add]
      rw [← localCount_div, ih, add_div]

theorem rate_eq (D : Nat) (htotal : ∀ s, ∑ e, count s e = D)
    (xs : List X) (accepts : α → Bool) :
    (((output count shape entries xs).filter accepts).length : ℝ) /
        (output count shape entries xs).length =
      average count shape entries D xs accepts := by
  rw [output_filter_length, output_length count shape entries D htotal,
    Nat.cast_mul, average, conditionalRate_sum]
  exact div_mul_eq_div_div _ _ _

theorem output_support (xs : List X) (entry : α)
    (hentry : entry ∈ output count shape entries xs) :
    ∃ x ∈ xs, ∃ e : E (shape x), entries x e = entry := by
  obtain ⟨x, hx, hlocal⟩ := List.mem_flatMap.mp hentry
  obtain ⟨e, _, he⟩ := List.mem_map.mp hlocal
  exact ⟨x, hx, e, he⟩

end Lists

section Target

variable {l r q : Nat} (shape : X → S)
  (entries : (x : X) → E (shape x) → Edge l r q)

def construct (D : Nat) (hD : 0 < D) (htotal : ∀ s, ∑ e, count s e = D)
    (xs : List X) (hxs : xs ≠ []) : Instance q where
  leftVertices := l
  rightVertices := r
  edges := output count shape entries xs
  nonempty := output_nonempty count shape entries D hD htotal xs hxs

theorem construct_length (D : Nat) (hD : 0 < D) (htotal : ∀ s, ∑ e, count s e = D)
    (xs : List X) (hxs : xs ≠ []) :
    (construct count shape entries D hD htotal xs hxs).edges.length = D * xs.length :=
  output_length count shape entries D htotal xs

theorem count_eq (D : Nat) (hD : 0 < D) (htotal : ∀ s, ∑ e, count s e = D)
    (xs : List X) (hxs : xs ≠ [])
    (a : Fin l → Fin (2 * q)) (b : Fin r → Fin q) :
    countSatisfied a b (construct count shape entries D hD htotal xs hxs).edges =
      (xs.map (fun x => ∑ e, if (entries x e).satisfied a b then count (shape x) e else 0)).sum := by
  change countSatisfied a b (output count shape entries xs) = _
  rw [RoundedTarget.countSatisfied_eq_filter]
  exact output_filter_length count shape entries xs (fun e => e.satisfied a b)

theorem construct_rate_eq (D : Nat) (hD : 0 < D) (htotal : ∀ s, ∑ e, count s e = D)
    (xs : List X) (hxs : xs ≠ [])
    (a : Fin l → Fin (2 * q)) (b : Fin r → Fin q) :
    (countSatisfied a b (construct count shape entries D hD htotal xs hxs).edges : ℝ) /
        (construct count shape entries D hD htotal xs hxs).edges.length =
      average count shape entries D xs (fun e => e.satisfied a b) := by
  change (countSatisfied a b (output count shape entries xs) : ℝ) /
    (output count shape entries xs).length = _
  rw [RoundedTarget.countSatisfied_eq_filter]
  exact rate_eq count shape entries D htotal xs (fun e => e.satisfied a b)

theorem value_le (D : Nat) (hD : 0 < D) (htotal : ∀ s, ∑ e, count s e = D)
    (xs : List X) (hxs : xs ≠ []) (hq : 0 < q) (bound : ℝ)
    (hsound : ∀ a : Fin l → Fin (2 * q), ∀ b : Fin r → Fin q,
      average count shape entries D xs (fun e => e.satisfied a b) ≤ bound) :
    (construct count shape entries D hD htotal xs hxs).value ≤ bound := by
  obtain ⟨s, hs⟩ := (construct count shape entries D hD htotal xs hxs).maxSatisfied_attained hq
  unfold Instance.value
  rw [← hs]
  exact (construct_rate_eq count shape entries D hD htotal xs hxs s.1 s.2).le.trans
    (hsound s.1 s.2)

theorem perfectlyComplete (D : Nat) (hD : 0 < D) (htotal : ∀ s, ∑ e, count s e = D)
    (xs : List X) (hxs : xs ≠ [])
    (hcomplete : ∃ s : RoundedTarget.EndpointLabeling l r q,
      ∀ x ∈ xs, ∀ e : E (shape x), (entries x e).satisfied s.1 s.2 = true) :
    PerfectlyComplete (construct count shape entries D hD htotal xs hxs) := by
  obtain ⟨s, hs⟩ := hcomplete
  refine ⟨s, ?_⟩
  intro edge hedge
  obtain ⟨x, hx, e, he⟩ := output_support count shape entries xs edge hedge
  rw [← he]
  exact hs x hx e

theorem complete_value_eq_one (D : Nat) (hD : 0 < D) (htotal : ∀ s, ∑ e, count s e = D)
    (xs : List X) (hxs : xs ≠ []) (hq : 0 < q)
    (hcomplete : ∃ s : RoundedTarget.EndpointLabeling l r q,
      ∀ x ∈ xs, ∀ e : E (shape x), (entries x e).satisfied s.1 s.2 = true) :
    (construct count shape entries D hD htotal xs hxs).value = 1 :=
  ((construct count shape entries D hD htotal xs hxs).perfectlyComplete_iff_value_eq_one hq).1
    (perfectlyComplete count shape entries D hD htotal xs hxs hcomplete)

end Target

theorem conditionalRate_uniformization {α : Type*} (w : ∀ s, E s → ℚ)
    (U : ExactRationalMultiplicity.Uniformization w) (shape : X → S)
    (entries : (x : X) → E (shape x) → α) (accepts : α → Bool) (x : X) :
    conditionalRate U.count shape entries U.denominator accepts x =
      ∑ e, if accepts (entries x e) then (w (shape x) e : ℝ) else 0 := by
  apply Finset.sum_congr rfl
  intro e _
  have h := congrArg (fun z : ℚ => (z : ℝ)) (U.fraction (shape x) e)
  simp only [Rat.cast_div, Rat.cast_natCast] at h
  cases accepts (entries x e) <;> simp [h]

end
end PerfectCompleteness.ExactConditionalOutput

end OAI
