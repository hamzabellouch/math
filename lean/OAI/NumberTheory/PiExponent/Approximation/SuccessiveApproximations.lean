import Mathlib
import OAI.NumberTheory.PiExponent.Approximation.ApproximationSelection

namespace OAI

namespace PiExponent

theorem exists_successive_approximations
    (nu : ℝ) (hnu : 0 < nu)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu))
    (T : List ℝ → ℝ) :
    ∃ p : ℕ → ℤ, ∃ q : ℕ → ℕ, ∀ n,
      2 ≤ q n ∧ p n ≠ 0 ∧
      |Real.pi - (p n : ℝ) / q n| ≤ (q n : ℝ) ^ (-nu) ∧
      1 ≤ Nat.ceil (Real.log (q n)) ∧
      T (((List.range n).reverse).map
        (fun i => ((Nat.ceil (Real.log (q i))) : ℝ))) <
          ((Nat.ceil (Real.log (q n))) : ℝ) := by
  classical
  let wt : ℤ × ℕ → ℝ := fun a => (Nat.ceil (Real.log a.2) : ℝ)
  let Good : ℤ × ℕ → Prop := fun a =>
    2 ≤ a.2 ∧ a.1 ≠ 0 ∧
    |Real.pi - (a.1 : ℝ) / a.2| ≤ (a.2 : ℝ) ^ (-nu) ∧
    1 ≤ Nat.ceil (Real.log a.2)
  have hex (L : List (ℤ × ℕ)) :
      ∃ a : ℤ × ℕ, Good a ∧ T (L.map wt) < wt a := by
    obtain ⟨p, q, hq, hlog, hp, happ⟩ :=
      exists_large_log_approximation nu (max 1 (T (L.map wt))) hnu hbad
    have hceil : Real.log q ≤ (Nat.ceil (Real.log q) : ℝ) := Nat.le_ceil _
    have hone : 1 < (Nat.ceil (Real.log q) : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hlog hceil)
    have hnat : 1 ≤ Nat.ceil (Real.log q) := by exact_mod_cast le_of_lt hone
    exact ⟨(p, q), ⟨hq, hp, happ, hnat⟩,
      lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hlog hceil)⟩
  let next : List (ℤ × ℕ) → ℤ × ℕ := fun L => (hex L).choose
  have hnext (L : List (ℤ × ℕ)) : Good (next L) ∧ T (L.map wt) < wt (next L) :=
    (hex L).choose_spec
  let hist : ℕ → List (ℤ × ℕ) := Nat.rec [] (fun _ L => next L :: L)
  let a : ℕ → ℤ × ℕ := fun n => next (hist n)
  have hhist (n : ℕ) : hist n = (List.range n).reverse.map a := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change a n :: hist n = (List.range (n + 1)).reverse.map a
      rw [ih]
      simp [List.range_succ, List.reverse_append]
  refine ⟨fun n => (a n).1, fun n => (a n).2, fun n => ?_⟩
  have hgood : Good (a n) := (hnext (hist n)).1
  refine ⟨hgood.1, hgood.2.1, hgood.2.2.1, hgood.2.2.2, ?_⟩
  have hbound := (hnext (hist n)).2
  have hmap : (hist n).map wt = (List.range n).reverse.map (wt ∘ a) := by
    rw [hhist, List.map_map]
  rw [hmap] at hbound
  exact hbound

theorem logarithmic_weight_bounds (q : ℕ) (hq : 1 ≤ q) :
    Real.log q ≤ (Nat.ceil (Real.log q) : ℝ) ∧
      (Nat.ceil (Real.log q) : ℝ) < Real.log q + 1 := by
  exact ⟨Nat.le_ceil _, Nat.ceil_lt_add_one (Real.log_nonneg (by exact_mod_cast hq))⟩

theorem approximation_error_at_logarithmic_weight
    (nu : ℝ) (hnu : 0 < nu) (p : ℤ) (q : ℕ) (hq : 1 ≤ q)
    (herror : |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    |Real.pi - (p : ℝ) / q| ≤
      Real.exp (nu - nu * (Nat.ceil (Real.log q) : ℝ)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hw := (logarithmic_weight_bounds q hq).2
  calc
    _ ≤ (q : ℝ) ^ (-nu) := herror
    _ = Real.exp (Real.log q * (-nu)) := Real.rpow_def_of_pos hqpos _
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

noncomputable def normalizedLogWeights (q : ℕ → ℕ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => (Nat.ceil (Real.log (q n)) : ℝ)

@[simp] theorem normalizedLogWeights_zero (q : ℕ → ℕ) :
    normalizedLogWeights q 0 = 1 := rfl

@[simp] theorem normalizedLogWeights_succ (q : ℕ → ℕ) (n : ℕ) :
    normalizedLogWeights q (n + 1) = (Nat.ceil (Real.log (q n)) : ℝ) := rfl

theorem reverse_logWeights_prod (q : ℕ → ℕ) (n : ℕ) :
    (((List.range n).reverse).map
      (fun i => (Nat.ceil (Real.log (q i)) : ℝ))).prod =
      ∏ j ∈ Finset.range (n + 1), normalizedLogWeights q j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.reverse_append]
    simp only [List.reverse_singleton, List.map_append, List.map_singleton,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    rw [Finset.prod_range_succ, ih, normalizedLogWeights_succ]
    exact mul_comm _ _

theorem exists_normalized_selection_of_selector
    (nu X D : ℝ)
    (hselect : ∀ T : List ℝ → ℝ,
      ∃ p : ℕ → ℤ, ∃ q : ℕ → ℕ, ∀ n,
        2 ≤ q n ∧ p n ≠ 0 ∧
        |Real.pi - (p n : ℝ) / q n| ≤ (q n : ℝ) ^ (-nu) ∧
        1 ≤ Nat.ceil (Real.log (q n)) ∧
        T (((List.range n).reverse).map
          (fun i => ((Nat.ceil (Real.log (q i))) : ℝ))) <
            ((Nat.ceil (Real.log (q n))) : ℝ)) :
    ∃ p : ℕ → ℤ, ∃ q : ℕ → ℕ, ∃ x : ℕ → ℝ,
      x 0 = 1 ∧
      (∀ n, x (n + 1) = (Nat.ceil (Real.log (q n)) : ℝ)) ∧
      (∀ n, 2 ≤ q n ∧ p n ≠ 0 ∧
        |Real.pi - (p n : ℝ) / q n| ≤ (q n : ℝ) ^ (-nu) ∧
        1 ≤ Nat.ceil (Real.log (q n)) ∧ X < x (n + 1)) ∧
      (∀ i, 1 ≤ x i) ∧
      (∀ i, 0 < i → D * (∏ j ∈ Finset.range i, x j) < x i) := by
  obtain ⟨p, q, h⟩ := hselect (fun L => max X (D * L.prod))
  refine ⟨p, q, normalizedLogWeights q, rfl, fun _ => rfl, ?_, ?_, ?_⟩
  · intro n
    refine ⟨(h n).1, (h n).2.1, (h n).2.2.1, (h n).2.2.2.1, ?_⟩
    exact lt_of_le_of_lt (le_max_left _ _) (h n).2.2.2.2
  · intro i
    cases i with
    | zero => simp
    | succ n =>
      change (1 : ℝ) ≤ (Nat.ceil (Real.log (q n)) : ℝ)
      exact_mod_cast (h n).2.2.2.1
  · intro i hi
    cases i with
    | zero => omega
    | succ n =>
      have hprod := lt_of_le_of_lt (le_max_right _ _) (h n).2.2.2.2
      rw [reverse_logWeights_prod] at hprod
      exact hprod

theorem exists_normalized_successive_approximations
    (nu X D : ℝ) (hnu : 0 < nu)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    ∃ p : ℕ → ℤ, ∃ q : ℕ → ℕ, ∃ x : ℕ → ℝ,
      x 0 = 1 ∧
      (∀ n, x (n + 1) = (Nat.ceil (Real.log (q n)) : ℝ)) ∧
      (∀ n, 2 ≤ q n ∧ p n ≠ 0 ∧
        |Real.pi - (p n : ℝ) / q n| ≤ (q n : ℝ) ^ (-nu) ∧
        1 ≤ Nat.ceil (Real.log (q n)) ∧ X < x (n + 1)) ∧
      (∀ i, 1 ≤ x i) ∧
      (∀ i, 0 < i → D * (∏ j ∈ Finset.range i, x j) < x i) := by
  exact exists_normalized_selection_of_selector nu X D
    (exists_successive_approximations nu hnu hbad)

end PiExponent

end OAI
