import Mathlib
import OAI.Combinatorics.UniformKServer.LinearProgram

namespace OAI

namespace UniformKServer.EffectiveLP

variable {n k H : ℕ} [NeZero k]

theorem labels_inhabited (c : Config n k) (r : Fin n) : (labels c r).Nonempty := by
  unfold labels
  split_ifs with hh
  · obtain ⟨j,hj⟩ := hh
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
  · exact Finset.univ_nonempty

def chosen (c : Config n k) (r : Fin n) : Label c r :=
  ⟨(labels c r).min' (labels_inhabited c r), Finset.min'_mem _ _⟩

def lazyRun (u : Config n k) (w : List (Fin n)) : Config n k :=
  w.foldl (fun c r => step c r (chosen c r)) u

@[simp] theorem lazyRun_nil (u : Config n k) : lazyRun u [] = u := rfl

@[simp] theorem lazyRun_append (u : Config n k) (w : List (Fin n)) (r : Fin n) :
    lazyRun u (w++[r]) = step (lazyRun u w) r (chosen (lazyRun u w) r) := by
  simp [lazyRun, List.foldl_append]

def pureFlow (u : Config n k) : BoundedFlow n k H ℝ where
  mass w c := if c = lazyRun u w.val then 1 else 0
  flow w r c j := if c = lazyRun u w.val.val then (if j = chosen c r then 1 else 0) else 0

theorem pure_nonneg (u : Config n k) :
    (∀ w c, 0 ≤ (pureFlow (H := H) u).mass w c) ∧
    (∀ w r c j, 0 ≤ (pureFlow (H := H) u).flow w r c j) := by
  constructor
  · intro w c; simp only [pureFlow]; split_ifs <;> norm_num
  · intro w r c j; simp only [pureFlow]; split_ifs <;> norm_num

theorem pure_total (u : Config n k) (w : Word n H) :
    ∑ c, (pureFlow u).mass w c = 1 := by
  classical
  simp [pureFlow]

theorem pure_outflow (u : Config n k) (w : Short n H) (r : Fin n) (c : Config n k) :
    ∑ j, (pureFlow u).flow w r c j = (pureFlow u).mass w.val c := by
  classical
  by_cases hc : c = lazyRun u w.val.val <;> simp [pureFlow,hc]

theorem pure_inflow (u : Config n k) (w : Short n H) (r : Fin n) (c' : Config n k) :
    (∑ c, ∑ j, if step c r j = c' then (pureFlow u).flow w r c j else 0) =
      (pureFlow u).mass (extend w r) c' := by
  classical
  have inner (c : Config n k) :
      (∑ j : Label c r, if step c r j = c' then (pureFlow u).flow w r c j else 0) =
      if c = lazyRun u w.val.val then
        (if step c r (chosen c r) = c' then (1:ℝ) else 0) else 0 := by
    by_cases hc : c = lazyRun u w.val.val
    · simp only [pureFlow,hc, ite_true]
      simpa only [← ite_and, and_comm, Finset.mem_univ, ite_true, true_and] using
        (Finset.sum_ite_eq' Finset.univ (chosen c r)
          (fun j => if step c r j = c' then (1:ℝ) else 0))
    · simp [pureFlow,hc]
  simp_rw [inner]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, pureFlow, extend,
    lazyRun_append]
  split_ifs with hh hh' hh'
  · rfl
  · exact (hh' hh.symm).elim
  · exact (hh hh'.symm).elim
  · rfl


omit [NeZero k] in
theorem history_nonneg (d : RationalMetric n) (s : Configuration n k) (h : History n k) :
    0 ≤ costAlong d s h := by
  induction h generalizing s with
  | nil => exact le_rfl
  | cons a h ih => exact add_nonneg (by exact_mod_cast d.nonneg _ _) (ih _)

theorem opt_nonneg (d : RationalMetric n) (s : Configuration n k) (w : List (Fin n)) :
    0 ≤ (OfflineDynamic.optRat d s w : ℝ) := by
  obtain ⟨h,hh,hcost⟩ := OfflineDynamic.optRat_attained d s w
  rw [← hcost]
  exact history_nonneg d s h

omit [NeZero k] in
theorem zero_history_covered (d : RationalMetric n) (h : History n k)
    (s : Configuration n k) (hz : costAlong d s h = 0) :
    ∀ r ∈ h.map Prod.fst, ∃ j, s j = r := by
  induction h generalizing s with
  | nil => simp
  | cons a h ih =>
    rcases a with ⟨r,j⟩
    have hd : (d.distance (s j) r : ℝ) = 0 := by
      have hn := history_nonneg d (serve s r j) h
      have hp : 0 ≤ (d.distance (s j) r : ℝ) := by exact_mod_cast d.nonneg (s j) r
      simp only [costAlong] at hz
      linarith
    have he : s j = r := (d.eq_zero _ _).mp (by exact_mod_cast hd)
    have hs : serve s r j = s := by
      unfold serve
      conv_lhs => arg 3; rw [← he]
      exact Function.update_eq_self _ _
    have ht : costAlong d s h = 0 := by simpa only [costAlong, hd,hs,zero_add] using hz
    intro x hx
    simp only [List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨j,he⟩
    · exact ih s ht x hx

theorem zero_opt_covered (d : RationalMetric n) (s : Configuration n k) (w : List (Fin n))
    (hz : (OfflineDynamic.optRat d s w : ℝ) = 0) :
    ∀ r ∈ w, ∃ j, s j = r := by
  obtain ⟨h,hh,hcost⟩ := OfflineDynamic.optRat_attained d s w
  rw [← hh]
  exact zero_history_covered d h s (hcost.trans hz)

theorem chosen_hit (c : Config n k) (r : Fin n) (hh : ∃ j, c.val j = r) :
    c.val (chosen c r).val = r := by
  have h := (chosen c r).property
  simp only [labels, ite_eq_left hh, Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact h

theorem step_hit (c : Config n k) (r : Fin n) (hh : ∃ j, c.val j = r) :
    step c r (chosen c r) = c := by
  apply Subtype.ext
  change serve c.val r (chosen c r).val = c.val
  unfold serve
  conv_lhs => arg 3; rw [← chosen_hit c r hh]
  exact Function.update_eq_self _ _

theorem lazyRun_covered (u : Config n k) (w : List (Fin n))
    (hh : ∀ r ∈ w, ∃ j, u.val j = r) : lazyRun u w = u := by
  induction w with
  | nil => rfl
  | cons r w ih =>
    have hr := step_hit u r (hh r (by simp))
    change lazyRun (step u r (chosen u r)) w = u
    rw [hr]
    exact ih (fun x hx => hh x (by simp [hx]))

noncomputable def pureCost (d : RationalMetric n) (u : Config n k) (w : List (Fin n)) : ℝ :=
  ∑ i : Fin w.length,
    (d.distance ((lazyRun u (w.take i)).val (chosen (lazyRun u (w.take i)) w[i]).val) w[i] : ℝ)

theorem pureCost_nonneg (d : RationalMetric n) (u : Config n k) (w : List (Fin n)) :
    0 ≤ pureCost d u w := by
  apply Finset.sum_nonneg
  intro i _
  exact_mod_cast d.nonneg _ _

theorem pureCost_zero (d : RationalMetric n) (u : Config n k) (w : List (Fin n))
    (hz : (OfflineDynamic.optRat d u.val w : ℝ) = 0) : pureCost d u w = 0 := by
  have hc := zero_opt_covered d u.val w hz
  apply Finset.sum_eq_zero
  intro i _
  have hp : lazyRun u (w.take i) = u :=
    lazyRun_covered u _ (fun r hr => hc r (List.mem_of_mem_take hr))
  have hi : ∃ j, (lazyRun u (w.take i)).val j = w[i] := by
    rw [hp]
    exact hc w[i] (List.getElem_mem i.isLt)
  rw [chosen_hit _ w[i] hi, (d.eq_zero _ _).mpr rfl, Rat.cast_zero]

theorem pure_cost_eq (d : RationalMetric n) (u : Config n k) (w : Word n H) :
    (∑ i : Fin w.val.length, ∑ c, ∑ j : Label c w.val[i],
      (pureFlow u).flow (prefixNode w i) w.val[i] c j *
        (d.distance (c.val j.val) w.val[i] : ℝ)) = pureCost d u w.val := by
  classical
  unfold pureCost
  apply Finset.sum_congr rfl
  intro i _
  simp only [pureFlow, prefixNode, ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

noncomputable def crudeCoefficient (d : RationalMetric n) (u : Config n k) (H : ℕ) : ℝ :=
  ∑ w : Word n H, pureCost d u w.val / (OfflineDynamic.optRat d u.val w.val : ℝ)

theorem crude_nonneg (d : RationalMetric n) (u : Config n k) : 0 ≤ crudeCoefficient d u H := by
  apply Finset.sum_nonneg
  intro w _
  exact div_nonneg (pureCost_nonneg d u w.val) (opt_nonneg d u.val w.val)

theorem crude_competitive (d : RationalMetric n) (u : Config n k) (w : Word n H) :
    pureCost d u w.val ≤ crudeCoefficient d u H * (OfflineDynamic.optRat d u.val w.val : ℝ) := by
  rcases (opt_nonneg d u.val w.val).eq_or_lt with hz | hp
  · rw [← hz, pureCost_zero d u w.val hz.symm, mul_zero]
  · apply (div_le_iff₀ hp).mp
    exact Finset.single_le_sum
      (fun v _ => div_nonneg (pureCost_nonneg d u v.val) (opt_nonneg d u.val v.val))
      (Finset.mem_univ w)

theorem pure_valid (d : RationalMetric n) (u : Config n k) :
    Valid d u (pureFlow (H := H) u) (crudeCoefficient d u H) := by
  refine ⟨crude_nonneg d u, (pure_nonneg u).1, pure_total u, ?_, (pure_nonneg u).2,
    pure_outflow u, pure_inflow u, ?_⟩
  · intro c
    simp only [pureFlow, rootWord, lazyRun_nil]
    rfl
  · intro w
    rw [pure_cost_eq]
    exact crude_competitive d u w

/-- Unconditional termination, feasibility and exact rational optimality. -/
theorem unconditional_optimization {n k H : ℕ} [NeZero k]
    (d : RationalMetric n) (u : Config n k) :
    ∃ x : Fin (Fintype.card (Variable n k H)+1) → ℚ,
      FourierMotzkin.optimize (Fintype.card (Variable n k H)) (constraints d u) = some x ∧
      Valid d u (ofAssignment (Form.recover x)) (FourierMotzkin.objective x) ∧
      ∀ (F : BoundedFlow n k H ℝ) (a : ℝ), Valid d u F a →
        ((FourierMotzkin.objective x : ℚ) : ℝ) ≤ a := by
  exact rational_attainment d u ⟨pureFlow u, crudeCoefficient d u H, pure_valid d u⟩

end UniformKServer.EffectiveLP

end OAI
