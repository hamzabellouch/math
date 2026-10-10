import OAI.Combinatorics.CliqueFree.EdgeState

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

/-- Whole-graph sets that contain most of the walk. -/
noncomputable def enlarge (G : SimpleGraph V) (w : V → ℝ) (t : ℝ) (A : Finset V) : Finset V :=
  A ∪ univ.filter (fun y ↦ t ≤ mass w (A ∩ neighbors G y))

noncomputable def reach (G : SimpleGraph V) (w : V → ℝ) (t : ℝ) (v : V) : ℕ → Finset V
  | 0 => neighbors G v
  | n+1 => enlarge G w t (reach G w t v n)

lemma subset_enlarge (G : SimpleGraph V) (w : V → ℝ) (t : ℝ) (A : Finset V) :
    A ⊆ enlarge G w t A := subset_union_left

lemma not_mem_enlarge (G : SimpleGraph V) (w : V → ℝ) (t : ℝ) (A : Finset V)
    {y : V} (hy : y ∉ enlarge G w t A) :
    y ∉ A ∧ mass w (A ∩ neighbors G y) < t := by
  simpa [enlarge, not_or, not_le] using hy

lemma enlarge_mass (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {L t : ℝ} (hL : ∀ u, neighborMass G w u ≤ L) (ht : 0 < t) (A : Finset V) :
    mass w (enlarge G w t A) ≤ (1 + L / t) * mass w A := by
  let B := univ.filter (fun y ↦ t ≤ mass w (A ∩ neighbors G y))
  have hm : t * mass w B ≤ L * mass w A := by
    calc
      _ = ∑ y ∈ B, w y * t := by rw [← sum_mul]; exact mul_comm _ _
      _ ≤ ∑ y ∈ B, w y * mass w (A ∩ neighbors G y) := by
        exact sum_le_sum fun y hy ↦ mul_le_mul_of_nonneg_left (mem_filter.1 hy).2 (hw y)
      _ ≤ ∑ y, w y * mass w (A ∩ neighbors G y) := by
        exact sum_le_univ_sum_of_nonneg (fun y ↦ mul_nonneg (hw y) (mass_nonneg hw _))
      _ = crossMass G w univ A := (crossMass_factor G w univ A).symm
      _ = ∑ y ∈ A, w y * neighborMass G w y := crossMass_all_left G w A
      _ ≤ ∑ y ∈ A, w y * L := sum_le_sum fun y _ ↦ mul_le_mul_of_nonneg_left (hL y) (hw y)
      _ = L * mass w A := by rw [← sum_mul]; exact mul_comm _ _
  have hB : mass w B ≤ L / t * mass w A := by
    calc
      _ ≤ L * mass w A / t := (le_div_iff₀ ht).2 (by nlinarith)
      _ = _ := by ring
  have hu := mass_union_le hw A B
  change mass w (A ∪ B) ≤ _
  nlinarith

lemma reach_mass (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {L t : ℝ} (hL0 : 0 ≤ L) (hL : ∀ u, neighborMass G w u ≤ L) (ht : 0 < t)
    (v : V) (n : ℕ) : mass w (reach G w t v n) ≤ (1 + L / t) ^ n * neighborMass G w v := by
  have hfac : 0 ≤ 1 + L / t := by positivity
  induction n with
  | zero => simp [reach, neighborMass]
  | succ n ih =>
    exact (enlarge_mass G hw hL ht _).trans (by
      have h := mul_le_mul_of_nonneg_left ih hfac
      simpa only [pow_succ', mul_assoc] using h)

lemma reach_mass_exp (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {x : ℝ} (hx : 32 ≤ x) (hL : ∀ v, neighborMass G w v ≤ Real.exp x)
    {n : ℕ} (hn : (n : ℝ) ≤ 2 * x) (v : V) :
    mass w (reach G w (Numerical.threshold x) v n) ≤ Real.exp (20 * x ^ 2) := by
  have hx0 : 0 < x := by linarith
  have ht := Numerical.threshold_pos hx0
  have hfac : 0 ≤ 1 + Real.exp x / Numerical.threshold x := by positivity
  have hfacn := pow_le_pow_left₀ hfac (Numerical.growth_factor_le hx) n
  calc
    _ ≤ (1 + Real.exp x / Numerical.threshold x) ^ n * neighborMass G w v :=
      reach_mass G hw (Real.exp_pos x).le hL ht v n
    _ ≤ Real.exp (4 * x) ^ n * Real.exp x :=
      mul_le_mul hfacn (hL v) (neighborMass_nonneg G hw v) (by positivity)
    _ = Real.exp ((n : ℝ) * (4 * x) + x) := by rw [Real.exp_add, Real.exp_nat_mul]
    _ ≤ _ := Real.exp_le_exp.2 (by nlinarith)

lemma growth_le_of_lower {x Y s : ℝ} (hx : 1 ≤ x) (hs : 1 / x ≤ s) :
    growth Y s ≤ s * (Y + Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < s := (one_div_pos.2 hx0).trans_le hs
  have hrec : 1 / s ≤ x := by
    apply (div_le_iff₀ hs0).2
    have h := (div_le_iff₀ hx0).1 hs
    nlinarith
  have hl := Real.log_le_log (one_div_pos.2 hs0) hrec
  have hm : max 0 (Real.log (1 / s)) ≤ Real.log x := max_le (Real.log_nonneg hx) hl
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hm) hs0.le

noncomputable def badSet (G : SimpleGraph V) (w : V → ℝ) (S : V → Finset V)
    (b : ℝ) (v : V) : Finset V :=
  (neighbors G v).filter (fun u ↦ b < mass w (S v ∩ neighbors G u))

lemma badSet_subset (G : SimpleGraph V) (w : V → ℝ) (S : V → Finset V)
    (b : ℝ) (v : V) : badSet G w S b v ⊆ neighbors G v := filter_subset _ _

lemma badSet_mass_bound (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ u, 0 ≤ w u)
    {C Y : ℝ} (hCross : CrossBound G w C) (hY : 1 ≤ Y)
    (S : V → Finset V) (b : ℝ) (v : V)
    (hv : neighborMass G w v ≤ Real.exp Y) (hS : mass w (S v) ≤ Real.exp Y) :
    b * mass w (badSet G w S b v) ≤ C * growth Y (neighborMass G w v) := by
  calc
    _ = ∑ u ∈ badSet G w S b v, w u * b := by rw [← sum_mul]; exact mul_comm _ _
    _ ≤ ∑ u ∈ badSet G w S b v, w u * mass w (S v ∩ neighbors G u) := by
      exact sum_le_sum fun u hu ↦ mul_le_mul_of_nonneg_left ((mem_filter.1 hu).2.le) (hw u)
    _ ≤ ∑ u ∈ neighbors G v, w u * mass w (S v ∩ neighbors G u) := by
      exact sum_le_sum_of_subset_of_nonneg (badSet_subset G w S b v)
        (fun u _ _ ↦ mul_nonneg (hw u) (mass_nonneg hw _))
    _ = crossMass G w (neighbors G v) (S v) := (crossMass_factor _ _ _ _).symm
    _ ≤ _ := hCross Y hY _ _ hv hS

lemma conditional_bad_bound (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ u, 0 ≤ w u)
    {C x k : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x) (hk : 0 ≤ k)
    (hCross : CrossBound G w C) (v : V) (B : Finset V) (hB : B ⊆ neighbors G v)
    (hs : 1 / x ≤ neighborMass G w v) (hL : neighborMass G w v ≤ Real.exp x)
    (hh : neighborMass G w v / x ≤ triangleAt G w v)
    (hb : mass w B ≤ k * neighborMass G w v) :
    crossMass G w B (neighbors G v) ≤
      (2 * C * x ^ 2 * (k + x * Real.exp (-x))) * triangleAt G w v := by
  have hx0 : 0 < x := by linarith
  have hxsv : 1 ≤ x * neighborMass G w v := by
    have := (div_le_iff₀ hx0).1 hs
    nlinarith
  have hhh : neighborMass G w v ≤ x * triangleAt G w v := by
    have := (div_le_iff₀ hx0).1 hh
    nlinarith
  have he : Real.exp (-x) ≤ x * Real.exp (-x) * neighborMass G w v := by
    nlinarith [mul_le_mul_of_nonneg_left hxsv (Real.exp_pos (-x)).le]
  have hf : 0 ≤ 2 * C * x := by positivity
  have hf' : 0 ≤ 2 * C * x * (k + x * Real.exp (-x)) := by positivity
  calc
    _ ≤ C * growth x (mass w B) := hCross x hx _ _ ((mass_mono hw hB).trans hL) hL
    _ ≤ C * (2 * x * (mass w B + Real.exp (-x))) :=
      mul_le_mul_of_nonneg_left (growth_le_twice hx (mass_nonneg hw B)) hC
    _ = (2 * C * x) * (mass w B + Real.exp (-x)) := by ring
    _ ≤ (2 * C * x) * (k * neighborMass G w v +
        x * Real.exp (-x) * neighborMass G w v) :=
      mul_le_mul_of_nonneg_left (add_le_add hb he) hf
    _ = (2 * C * x * (k + x * Real.exp (-x))) * neighborMass G w v := by ring
    _ ≤ (2 * C * x * (k + x * Real.exp (-x))) * (x * triangleAt G w v) :=
      mul_le_mul_of_nonneg_left hhh hf'
    _ = _ := by ring

lemma reach_bad_mass (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ u, 0 ≤ w u)
    {C x : ℝ} (hC : 0 ≤ C) (hCross : CrossBound G w C) (hx : 32 ≤ x)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    {n : ℕ} (hn : (n : ℝ) ≤ 2 * x) {v : V} (hv : (neighbors G v).Nonempty) :
    mass w (badSet G w (fun u ↦ reach G w (Numerical.threshold x) u n) (x ^ 8) v) ≤
      (21 * C / x ^ 6) * neighborMass G w v := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hY : 1 ≤ 20 * x ^ 2 := by nlinarith
  have hxY : x ≤ 20 * x ^ 2 := by nlinarith
  have hs := neighborMass_ge_of_commonMass G hw hc hv
  have hS := reach_mass_exp G hw hx hL hn v
  have hm := badSet_mass_bound G hw hCross hY
    (fun u ↦ reach G w (Numerical.threshold x) u n) (x ^ 8) v
    ((hL v).trans (Real.exp_le_exp.2 hxY)) hS
  have hg := growth_le_of_lower (Y := 20 * x ^ 2) hx1 hs
  have hlog : Real.log x ≤ x ^ 2 := by
    have := Real.log_le_self hx0.le
    nlinarith
  have hgs : growth (20 * x ^ 2) (neighborMass G w v) ≤
      neighborMass G w v * (21 * x ^ 2) := by
    apply hg.trans
    apply mul_le_mul_of_nonneg_left _ (neighborMass_nonneg G hw v)
    linarith
  have hm' := hm.trans (mul_le_mul_of_nonneg_left hgs hC)
  calc
    _ ≤ C * (neighborMass G w v * (21 * x ^ 2)) / x ^ 8 := by
      apply (le_div_iff₀ (pow_pos hx0 8)).2
      nlinarith [hm']
    _ = _ := by field_simp [hx0.ne']

noncomputable def exceptionalConstant (C : ℝ) : ℝ := 42 * C ^ 2 + 2 * C
noncomputable def entropyConstant (C : ℝ) : ℝ := 10 + exceptionalConstant C
noncomputable def smoothingConstant (C : ℝ) : ℝ := 2 * Real.sqrt (entropyConstant C + 1)

lemma exceptionalConstant_nonneg {C : ℝ} (hC : 0 ≤ C) : 0 ≤ exceptionalConstant C := by
  unfold exceptionalConstant
  positivity

lemma reach_bad_cross (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ u, 0 ≤ w u)
    {C x : ℝ} (hC : 0 ≤ C) (hCross : CrossBound G w C) (hx : 32 ≤ x)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    {n : ℕ} (hn : (n : ℝ) ≤ 2 * x) (v : V) :
    crossMass G w (badSet G w (fun u ↦ reach G w (Numerical.threshold x) u n) (x ^ 8) v)
      (neighbors G v) ≤ (exceptionalConstant C / x ^ 4) * triangleAt G w v := by
  have hx0 : 0 < x := by linarith
  by_cases hv : (neighbors G v).Nonempty
  · have hbad := reach_bad_mass G hw hC hCross hx hL hc hn hv
    have hcond := conditional_bad_bound G hw hC (show 1 ≤ x by linarith)
      (show 0 ≤ 21 * C / x ^ 6 by positivity) hCross v _
      (badSet_subset G w _ _ v) (neighborMass_ge_of_commonMass G hw hc hv) (hL v)
      (by simpa only [one_div, div_eq_mul_inv, one_mul, mul_one, mul_comm] using triangleAt_ge_of_commonMass G hw hc v)
      hbad
    have hnum : 2 * C * x ^ 2 * (21 * C / x ^ 6 + x * Real.exp (-x)) ≤
        exceptionalConstant C / x ^ 4 := by
      calc
        _ ≤ 2 * C * x ^ 2 * (21 * C / x ^ 6 + x * (1 / x ^ 7)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (Numerical.exp_neg_le_inv_pow_seven hx) hx0.le)
        _ = _ := by unfold exceptionalConstant; field_simp [hx0.ne']; ring
    exact hcond.trans (mul_le_mul_of_nonneg_right hnum (triangleAt_nonneg G hw v))
  · have he := not_nonempty_iff_eq_empty.1 hv
    simp [badSet, he, crossMass, triangleAt]

end CliqueFreeIndependence.WeightedGraph

end

end OAI
