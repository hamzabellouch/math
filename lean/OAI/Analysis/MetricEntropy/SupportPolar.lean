import OAI.Analysis.MetricEntropy.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith

namespace OAI

universe uι uX uY

/-!
# Exact support and polar calculations

Both summands of the matrix body have explicit maximizing points. Consequently
the support equalities below are equalities to attained finite suprema, not
uses of the convention for an empty or unbounded real supremum.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators Pointwise

variable {ι : Type uι} {X : Type uX} {Y : Type uY}

def supportFunction [Fintype ι] (K : Set (RealSpace ι)) (δ : RealSpace ι) : ℝ :=
  sSup ((fun z => pairing z δ) '' K)

def signVector (δ : RealSpace ι) : RealSpace ι := fun i => if 0 ≤ δ i then 1 else -1

theorem signVector_mem_cube (δ : RealSpace ι) : signVector δ ∈ cube ι := by
  intro i
  simp only [signVector]
  split_ifs <;> norm_num

theorem pairing_signVector [Fintype ι] (δ : RealSpace ι) :
    pairing (signVector δ) δ = l1Norm δ := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : 0 ≤ δ i
  · simp [signVector, h, abs_of_nonneg h]
  · simp [signVector, h, abs_of_neg (lt_of_not_ge h)]

theorem pairing_cube_le [Fintype ι] (δ : RealSpace ι) {x : RealSpace ι}
    (hx : x ∈ cube ι) : pairing x δ ≤ l1Norm δ := by
  apply Finset.sum_le_sum
  intro i _
  calc
    x i * δ i ≤ |x i * δ i| := le_abs_self _
    _ = |x i| * |δ i| := abs_mul _ _
    _ ≤ 1 * |δ i| := mul_le_mul_of_nonneg_right (hx i) (abs_nonneg _)
    _ = |δ i| := one_mul _

theorem supportFunction_cube [Fintype ι] (δ : RealSpace ι) :
    supportFunction (cube ι) δ = l1Norm δ := by
  apply IsGreatest.csSup_eq
  constructor
  · exact ⟨signVector δ, signVector_mem_cube δ, pairing_signVector δ⟩
  · rintro r ⟨x, hx, rfl⟩
    exact pairing_cube_le δ hx

theorem polar_cube [Fintype ι] : polar (cube ι) = l1Ball ι := by
  ext δ
  change (∀ x ∈ cube ι, pairing x δ ≤ 1) ↔ l1Norm δ ≤ 1
  constructor
  · intro h
    rw [← pairing_signVector δ]
    exact h (signVector δ) (signVector_mem_cube δ)
  · intro h x hx
    exact (pairing_cube_le δ hx).trans h

/-- This formulation does not require boundedness, symmetry, or attainment. -/
theorem mem_smul_polar_iff [Fintype ι] (K : Set (RealSpace ι)) (δ : RealSpace ι)
    {c : ℝ} (hc : 0 < c) :
    δ ∈ c • polar K ↔ ∀ z ∈ K, pairing z δ ≤ c := by
  constructor
  · intro h z hz
    obtain ⟨v, hv, rfl⟩ := Set.mem_smul_set.mp h
    rw [pairing_smul_right]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hv z hz) hc.le
  · intro h
    refine Set.mem_smul_set.mpr ⟨c⁻¹ • δ, ?_, ?_⟩
    · intro z hz
      rw [pairing_smul_right]
      have h' := mul_le_mul_of_nonneg_left (h z hz) (inv_nonneg.mpr hc.le)
      simpa only [inv_mul_cancel₀ hc.ne'] using h'
    · rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]

theorem row_mem_absRowHull (g : Y → X → ℝ) (x : X) : row g x ∈ absRowHull g :=
  subset_convexHull ℝ _ (Or.inl ⟨x, rfl⟩)

theorem neg_row_mem_absRowHull (g : Y → X → ℝ) (x : X) : -row g x ∈ absRowHull g :=
  subset_convexHull ℝ _ (Or.inr ⟨x, rfl⟩)

private theorem convex_pairing_le [Fintype ι] (δ : RealSpace ι) (M : ℝ) :
    Convex ℝ {z : RealSpace ι | pairing z δ ≤ M} := by
  intro x hx y hy a b ha hb hab
  change pairing (a • x + b • y) δ ≤ M
  rw [pairing_add_left, pairing_smul_left, pairing_smul_left]
  calc
    a * pairing x δ + b * pairing y δ ≤ a * M + b * M :=
      add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = M := by rw [← add_mul, hab, one_mul]

theorem pairing_absRowHull_le_of_bounds [Fintype Y]
    (g : Y → X → ℝ) (δ : RealSpace Y) {M : ℝ}
    (hM : ∀ x, |pairing (row g x) δ| ≤ M)
    {z : RealSpace Y} (hz : z ∈ absRowHull g) : pairing z δ ≤ M := by
  apply convexHull_min (t := {z : RealSpace Y | pairing z δ ≤ M}) ?_
    (convex_pairing_le δ M) hz
  rintro w (⟨x, rfl⟩ | ⟨x, rfl⟩)
  · exact (abs_le.mp (hM x)).2
  · change pairing (-row g x) δ ≤ M
    rw [pairing_neg_left]
    exact neg_le.mpr (abs_le.mp (hM x)).1

/-- The row maximum is over the actual nonempty finite row index set. -/
def rowSupport [Fintype X] [Nonempty X] [Fintype Y]
    (g : Y → X → ℝ) (δ : RealSpace Y) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun x => |pairing (row g x) δ|)

theorem abs_pairing_row_le_rowSupport [Fintype X] [Nonempty X] [Fintype Y]
    (g : Y → X → ℝ) (δ : RealSpace Y) (x : X) :
    |pairing (row g x) δ| ≤ rowSupport g δ :=
  Finset.le_sup' (fun x => |pairing (row g x) δ|) (Finset.mem_univ x)

theorem rowSupport_attained [Fintype X] [Nonempty X] [Fintype Y]
    (g : Y → X → ℝ) (δ : RealSpace Y) :
    ∃ x, |pairing (row g x) δ| = rowSupport g δ := by
  obtain ⟨x, _, hx⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset X)) Finset.univ_nonempty
    (fun x => |pairing (row g x) δ|)
  exact ⟨x, hx.symm⟩

theorem rowSupport_nonneg [Fintype X] [Nonempty X] [Fintype Y]
    (g : Y → X → ℝ) (δ : RealSpace Y) : 0 ≤ rowSupport g δ := by
  obtain ⟨x, hx⟩ := rowSupport_attained g δ
  rw [← hx]
  exact abs_nonneg _

theorem absRowHull_support_attained [Fintype X] [Nonempty X] [Fintype Y]
    (g : Y → X → ℝ) (δ : RealSpace Y) :
    ∃ z ∈ absRowHull g, pairing z δ = rowSupport g δ := by
  obtain ⟨x, hx⟩ := rowSupport_attained g δ
  by_cases h : 0 ≤ pairing (row g x) δ
  · exact ⟨row g x, row_mem_absRowHull g x, (abs_of_nonneg h).symm.trans hx⟩
  · refine ⟨-row g x, neg_row_mem_absRowHull g x, ?_⟩
    rw [pairing_neg_left]
    exact (abs_of_neg (lt_of_not_ge h)).symm.trans hx

theorem supportFunction_absRowHull [Fintype X] [Nonempty X] [Fintype Y]
    (g : Y → X → ℝ) (δ : RealSpace Y) :
    supportFunction (absRowHull g) δ = rowSupport g δ := by
  apply IsGreatest.csSup_eq
  constructor
  · obtain ⟨z, hz, heq⟩ := absRowHull_support_attained g δ
    exact ⟨z, hz, heq⟩
  · rintro r ⟨z, hz, rfl⟩
    exact pairing_absRowHull_le_of_bounds g δ (abs_pairing_row_le_rowSupport g δ) hz

/-- The quantitative pointwise estimate consumed by the polar covering proof. -/
theorem matrixBody_pairing_le_of_bounds [Fintype Y]
    (g : Y → X → ℝ) (δ : RealSpace Y) {t M L : ℝ} (ht : 0 ≤ t)
    (hM : ∀ x, |pairing (row g x) δ| ≤ M) (hL : l1Norm δ ≤ L)
    {z : RealSpace Y} (hz : z ∈ matrixBody g t) : pairing z δ ≤ 3 * M + t * L := by
  obtain ⟨v0, hv0, w0, hw0, hzEq⟩ := Set.mem_add.mp hz
  obtain ⟨v, hv, hvEq⟩ := Set.mem_smul_set.mp hv0
  obtain ⟨w, hw, hwEq⟩ := Set.mem_smul_set.mp hw0
  rw [← hzEq, ← hvEq, ← hwEq, pairing_add_left, pairing_smul_left, pairing_smul_left]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (pairing_absRowHull_le_of_bounds g δ hM hv) (by norm_num))
    (mul_le_mul_of_nonneg_left ((pairing_cube_le δ hw).trans hL) ht)

theorem matrixBody_support_attained [Fintype X] [Nonempty X] [Fintype Y]
    (g : Y → X → ℝ) (δ : RealSpace Y) (t : ℝ) :
    ∃ z ∈ matrixBody g t, pairing z δ = 3 * rowSupport g δ + t * l1Norm δ := by
  obtain ⟨v, hv, heq⟩ := absRowHull_support_attained g δ
  refine ⟨(3 : ℝ) • v + t • signVector δ,
    Set.add_mem_add (Set.smul_mem_smul_set hv)
      (Set.smul_mem_smul_set (signVector_mem_cube δ)), ?_⟩
  rw [pairing_add_left, pairing_smul_left, pairing_smul_left, heq, pairing_signVector]

theorem supportFunction_matrixBody [Fintype X] [Nonempty X] [Fintype Y]
    (g : Y → X → ℝ) (δ : RealSpace Y) {t : ℝ} (ht : 0 ≤ t) :
    supportFunction (matrixBody g t) δ = 3 * rowSupport g δ + t * l1Norm δ := by
  apply IsGreatest.csSup_eq
  constructor
  · obtain ⟨z, hz, heq⟩ := matrixBody_support_attained g δ t
    exact ⟨z, hz, heq⟩
  · rintro r ⟨z, hz, rfl⟩
    exact matrixBody_pairing_le_of_bounds g δ ht
      (abs_pairing_row_le_rowSupport g δ) le_rfl hz

theorem mem_smul_polar_matrixBody_of_bounds [Fintype Y]
    (g : Y → X → ℝ) (δ : RealSpace Y) {t M L c : ℝ} (ht : 0 ≤ t) (hc : 0 < c)
    (hM : ∀ x, |pairing (row g x) δ| ≤ M) (hL : l1Norm δ ≤ L)
    (hbound : 3 * M + t * L ≤ c) : δ ∈ c • polar (matrixBody g t) := by
  apply (mem_smul_polar_iff (matrixBody g t) δ hc).mpr
  intro z hz
  exact (matrixBody_pairing_le_of_bounds g δ ht hM hL hz).trans hbound

theorem mem_smul_polar_matrixBody_iff [Fintype X] [Nonempty X] [Fintype Y]
    (g : Y → X → ℝ) (δ : RealSpace Y) {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c) :
    δ ∈ c • polar (matrixBody g t) ↔ 3 * rowSupport g δ + t * l1Norm δ ≤ c := by
  rw [mem_smul_polar_iff (matrixBody g t) δ hc]
  constructor
  · intro h
    obtain ⟨z, hz, heq⟩ := matrixBody_support_attained g δ t
    rw [← heq]
    exact h z hz
  · intro h z hz
    exact (matrixBody_pairing_le_of_bounds g δ ht
      (abs_pairing_row_le_rowSupport g δ) le_rfl hz).trans h

end MetricEntropyDuality

end

end OAI
