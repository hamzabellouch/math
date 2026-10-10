import OAI.Combinatorics.ContingencyTables.Rooted.ForestScaledBounds
import OAI.Combinatorics.ContingencyTables.Dense.DenseWeights

namespace OAI

/-! # The literal weight-evaluator density on its finite-dimensional bin cube -/

namespace ContingencyTables.CompanionOracleDensity

open scoped BigOperators Classical
open CompanionFactorialApplication ForestAssignmentSplit ForestScaledPenalty

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable abbrev dimension (A : Instance I J) := Fintype.card (FreeCell A.small A.T)

noncomputable def index (A : Instance I J) : Fin (dimension A) ≃ FreeCell A.small A.T :=
  (Fintype.equivFin _).symm

noncomputable def pull (A : Instance I J) (v : Fin (dimension A) → ℝ) : FreeCell A.small A.T → ℝ :=
  fun f => v ((index A).symm f)

noncomputable def binWidth (A : Instance I J) (C : ℝ) : ℝ := 16*C*(A.d:ℝ)^2

noncomputable def height (A : Instance I J) (C : ℝ) : ℝ := 10*C*(A.d:ℝ)^2*((A.W:ℝ)+1)

noncomputable def D (A : Instance I J) (C : ℝ) (z : View A → ℕ)
    (v : Fin (dimension A) → ℝ) : ℝ :=
  penalty A C (binWidth A C) (rowCounts A z) (columnCounts A z) (pull A v)

lemma binWidth_positive (A : Instance I J) (C : ℝ) (hC : 0 < C) : 0 < binWidth A C := by
  have hd : (0:ℝ) < A.d := by exact_mod_cast (show 0 < A.d by have hh := A.hd; omega)
  unfold binWidth
  positivity

lemma height_positive (A : Instance I J) (C : ℝ) (hC : 0 < C) : 0 < height A C := by
  have hd : (0:ℝ) < A.d := by exact_mod_cast (show 0 < A.d by have hh := A.hd; omega)
  unfold height
  positivity

theorem D_bounds (A : Instance I J) (C : ℝ) (hC : 0 < C)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Fin (dimension A) → ℝ) (hv : ∀ i,0 ≤ v i ∧ v i ≤ binWidth A C) :
    0 ≤ D A C z v ∧ D A C z v ≤ height A C := by
  have hh := penalty_cube_bound A C (binWidth A C) hC.le (binWidth_positive A C hC)
    z hz (pull A v) (fun f => hv ((index A).symm f))
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  unfold height
  ring

theorem D_change (A : Instance I J) (C : ℝ) (hC : 0 < C) (z : View A → ℕ)
    (v w : Fin (dimension A) → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hvw : ∀ i,|v i-w i| ≤ r) : |D A C z v-D A C z w| ≤ r/8 := by
  have hh := penalty_change A C (binWidth A C) hC.le (binWidth_positive A C hC)
    (rowCounts A z) (columnCounts A z) (pull A v) (pull A w) r hr
    (fun f => hvw ((index A).symm f))
  have hd : (A.d:ℝ) ≠ 0 := by exact_mod_cast (show A.d≠0 by have hh := A.hd; omega)
  have he : (2*C*(A.d:ℝ)^2/binWidth A C)*r=r/8 := by
    unfold binWidth
    field_simp [hC.ne',hd]
    ring
  simpa only [D,he] using hh

theorem D_continuous (A : Instance I J) (C : ℝ) (z : View A → ℕ) : Continuous (D A C z) := by
  have hpull : Continuous (pull A) := continuous_pi (fun f => continuous_apply ((index A).symm f))
  exact (penalty_continuous A C (binWidth A C) (rowCounts A z) (columnCounts A z)).comp hpull

theorem D_convex (A : Instance I J) (C : ℝ) (hC : 0 ≤ C) (z : View A → ℕ) :
    ConvexOn ℝ Set.univ (D A C z) := by
  refine ⟨convex_univ,?_⟩
  intro v _ w _ a b ha hb hab
  have hh := (penalty_convex A C (binWidth A C) hC (rowCounts A z) (columnCounts A z)).2
    (Set.mem_univ (pull A v)) (Set.mem_univ (pull A w)) ha hb hab
  exact hh

noncomputable def rho (A : Instance I J) (C a : ℝ) (z : View A → ℕ) :
    (Fin (dimension A) → ℝ) → ℝ := DenseWeights.density (a/height A C) (D A C z)

noncomputable def V (A : Instance I J) (C a : ℝ) (z : View A → ℕ) :
    (Fin (dimension A) → ℝ) → ℝ := DenseWeights.binWeight (a/height A C) (D A C z)

theorem rho_continuous (A : Instance I J) (C a : ℝ) (z : View A → ℕ) :
    Continuous (rho A C a z) := DenseWeights.density_continuous _ _ (D_continuous A C z)

theorem rho_positive (A : Instance I J) (C a : ℝ) (z : View A → ℕ) (v : Fin (dimension A) → ℝ) :
    0 < rho A C a z v := DenseWeights.density_pos _ _ _

theorem rho_logConcave (A : Instance I J) (C a : ℝ) (hC : 0 < C) (ha : 0 ≤ a)
    (z : View A → ℕ) : PublishedInputs.LogConcaveOn (rho A C a z) Set.univ :=
  DenseWeights.density_logConcave _ (div_nonneg ha (height_positive A C hC).le) _ _ (D_convex A C hC.le z)

/-- Every evaluator phase has base-two logarithmic Lipschitz constant
at most 1/8; the bin and cut-tube comparisons now apply to the actual
forest density. -/
theorem exponent_change (A : Instance I J) (C a : ℝ) (hC : 0 < C)
    (ha : 0 ≤ a) (haH : a ≤ height A C) (z : View A → ℕ)
    (v w : Fin (dimension A) → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hvw : ∀ i,|v i-w i| ≤ r) :
    |(a/height A C)*D A C z v-(a/height A C)*D A C z w| ≤ r/8 := by
  have hH := height_positive A C hC
  have hf0 : 0 ≤ a/height A C := div_nonneg ha hH.le
  have hf1 : a/height A C ≤ 1 := (div_le_one hH).mpr haH
  rw [← mul_sub,abs_mul,abs_of_nonneg hf0]
  exact (mul_le_mul_of_nonneg_left (D_change A C hC z v w r hr hvw) hf0).trans
    (mul_le_of_le_one_left (by positivity) hf1)

theorem bin_comparison (A : Instance I J) (C a : ℝ) (hC : 0 < C)
    (ha : 0 ≤ a) (haH : a ≤ height A C) (z : View A → ℕ)
    (v w : Fin (dimension A) → ℝ) (hvw : ∀ i,|v i-w i| ≤ 1) :
    V A C a z v/4 ≤ rho A C a z w ∧ rho A C a z w ≤ 2*V A C a z v := by
  have hh := exponent_change A C a hC ha haH z w v 1 (by norm_num)
    (fun i => by simpa only [abs_sub_comm] using hvw i)
  exact DenseWeights.bin_density_comparison _ _ w v (hh.trans (by norm_num))

end ContingencyTables.CompanionOracleDensity

end OAI
