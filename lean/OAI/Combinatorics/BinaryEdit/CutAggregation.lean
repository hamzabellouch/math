import OAI.Combinatorics.BinaryEdit.Model
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

namespace OAI

/-! Countable-coordinate aggregation in the finite cut representation. -/

noncomputable section

namespace TreeEdit.BinaryLower.CutAggregation

universe u v

lemma summable_L1_abs_sub (f g : TreeEdit.RealL1) :
    Summable (fun n : ℕ => |f n - g n|) := by
  simpa only [ENNReal.toReal_one, Real.rpow_one, lp.coeFn_sub, Pi.sub_apply,
    Real.norm_eq_abs] using (lp.memℓp (f - g)).summable (by simp)

lemma norm_L1_sub (f g : TreeEdit.RealL1) :
    ‖f - g‖ = ∑' n : ℕ, |f n - g n| := by
  simpa only [ENNReal.toReal_one, Real.rpow_one, one_div_one, lp.coeFn_sub,
    Pi.sub_apply, Real.norm_eq_abs] using lp.norm_eq_tsum_rpow (by simp) (f - g)

/-- A nontrivial cut weight is dominated by any coordinate distance across
that cut. This makes the countable grouping legitimate without a finite
support assumption on the image in ℓ₁. -/
lemma scalar_weight_le {S : Type u} {C : Type v} [Fintype C]
    (f : S → ℝ) (U : C → S → ℝ) (a : C → ℝ)
    (ha : ∀ c, 0 ≤ a c)
    (hrep : ∀ x y, |f x - f y| = ∑ c, a c * |U c x - U c y|)
    (c : C) (x y : S) (hxy : |U c x - U c y| = 1) :
    a c ≤ |f x - f y| := by
  classical
  rw [hrep]
  calc
    a c = a c * |U c x - U c y| := by rw [hxy, mul_one]
    _ ≤ ∑ k, a k * |U k x - U k y| :=
      Finset.single_le_sum (fun k _ => mul_nonneg (ha k) (abs_nonneg (U k x - U k y)))
        (Finset.mem_univ c)

/-- Countably many scalar decompositions combine into an actual finite cut
representation of a map into the full absolutely summable sequence space.
Null cuts are permitted, but their coordinate weights must vanish. -/
theorem aggregate {S : Type u} {C : Type v} [Fintype C]
    (F : S → TreeEdit.RealL1) (U : C → S → ℝ) (a : ℕ → C → ℝ)
    (ha : ∀ n c, 0 ≤ a n c)
    (hcut : ∀ c, (∀ n, a n c = 0) ∨ ∃ x y, |U c x - U c y| = 1)
    (hrep : ∀ n x y,
      |F x n - F y n| = ∑ c, a n c * |U c x - U c y|) :
    ∃ A : C → ℝ, (∀ c, 0 ≤ A c) ∧
      (∀ c, A c = ∑' n, a n c) ∧
      (∀ x y, ‖F x - F y‖ = ∑ c, A c * |U c x - U c y|) := by
  classical
  have hs : ∀ c, Summable (fun n => a n c) := by
    intro c
    rcases hcut c with hz | ⟨x, y, hxy⟩
    · simpa only [hz] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
    · exact Summable.of_nonneg_of_le (fun n => ha n c)
        (fun n => scalar_weight_le (fun x => F x n) U (a n) (ha n) (hrep n) c x y hxy)
        (summable_L1_abs_sub (F x) (F y))
  refine ⟨fun c => ∑' n, a n c, ?_, fun _ => rfl, ?_⟩
  · intro c
    exact tsum_nonneg (fun n => ha n c)
  · intro x y
    rw [norm_L1_sub]
    simp_rw [hrep]
    rw [Summable.tsum_finsetSum]
    · apply Finset.sum_congr rfl
      intro c _
      exact (hs c).tsum_mul_right _
    · intro c _
      exact (hs c).mul_right _

/-- Every nontrivial cut separates two ordered pairs. Hence the finite total
cut mass is bounded by the sum over unordered pairs, written as one half of
the ordered-pair sum (diagonal terms vanish automatically). -/
theorem cut_mass_bound {S : Type u} {C : Type v} [Fintype S] [Fintype C]
    (F : S → TreeEdit.RealL1) (U : C → S → ℝ) (A : C → ℝ)
    (hA : ∀ c, 0 ≤ A c)
    (hcut : ∀ c, A c = 0 ∨ ∃ x y, |U c x - U c y| = 1)
    (hrep : ∀ x y, ‖F x - F y‖ = ∑ c, A c * |U c x - U c y|) :
    ∑ c, A c ≤ (∑ p : S × S, ‖F p.1 - F p.2‖) / 2 := by
  classical
  have hc : ∀ c, 2 * A c ≤ ∑ p : S × S, A c * |U c p.1 - U c p.2| := by
    intro c
    rcases hcut c with hz | ⟨x, y, hxy⟩
    · simp [hz]
    · have hne : x ≠ y := by
        intro h
        subst y
        simp at hxy
      have hp : (x, y) ≠ (y, x) := by
        intro h
        exact hne (congrArg Prod.fst h)
      calc
        2 * A c = ∑ p ∈ ({(x, y), (y, x)} : Finset (S × S)),
            A c * |U c p.1 - U c p.2| := by
          simp only [Finset.sum_insert, Finset.mem_singleton, hp, not_false_eq_true,
            Finset.sum_singleton]
          rw [hxy, abs_sub_comm (U c y) (U c x), hxy]
          ring
        _ ≤ ∑ p : S × S, A c * |U c p.1 - U c p.2| := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro p _ _
          exact mul_nonneg (hA c) (abs_nonneg _)
  have hsum := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => hc c)
  rw [← Finset.mul_sum, Finset.sum_comm] at hsum
  have heq : (∑ p : S × S, ∑ c, A c * |U c p.1 - U c p.2|) =
      ∑ p : S × S, ‖F p.1 - F p.2‖ := by
    apply Finset.sum_congr rfl
    intro p _
    exact (hrep p.1 p.2).symm
  rw [heq] at hsum
  linarith

/-- Countable scalar decompositions yield a finite cut representation with bounded total weight. -/
theorem aggregate_with_mass_bound {S : Type u} {C : Type v}
    [Fintype S] [Fintype C]
    (F : S → TreeEdit.RealL1) (U : C → S → ℝ) (a : ℕ → C → ℝ)
    (ha : ∀ n c, 0 ≤ a n c)
    (hcut : ∀ c, (∀ n, a n c = 0) ∨ ∃ x y, |U c x - U c y| = 1)
    (hrep : ∀ n x y,
      |F x n - F y n| = ∑ c, a n c * |U c x - U c y|) :
    ∃ A : C → ℝ, (∀ c, 0 ≤ A c) ∧
      (∀ c, A c = ∑' n, a n c) ∧
      (∀ x y, ‖F x - F y‖ = ∑ c, A c * |U c x - U c y|) ∧
      (∑ c, A c ≤ (∑ p : S × S, ‖F p.1 - F p.2‖) / 2) := by
  obtain ⟨A, hA, hsum, hrepr⟩ := aggregate F U a ha hcut hrep
  refine ⟨A, hA, hsum, hrepr, cut_mass_bound F U A hA ?_ hrepr⟩
  intro c
  rcases hcut c with hz | hnontrivial
  · left
    simp [hsum, hz]
  · exact Or.inr hnontrivial

end TreeEdit.BinaryLower.CutAggregation

end

end OAI
