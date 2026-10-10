import Mathlib
import OAI.Analysis.AffineBernstein.UniformLogCells
import OAI.Analysis.AffineBernstein.RegularFiberDomain

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter Metric
open scoped Topology

open Filter
/- Closed unit cells in the actual logarithmic base coordinates. -/
/- A fixed logarithmic box is covered by `(2R+1)^k` translated unit cells,
including its boundary and the zero-dimensional endpoint. -/
lemma logarithmicBox_subset_unitCells (k R : ℕ) :
    logarithmicBox k R ⊆ ⋃ q : Fin k → Fin (2*R+1),
      logarithmicUnitCell k (fun i => ((q i).val : ℤ)-(R:ℤ)) := by
  intro x hx
  have hb (i : Fin k) : 0 ≤ x i+(R:ℝ) ∧ x i+(R:ℝ) ≤ (2*R:ℕ) := by
    obtain ⟨hl,hu⟩ := abs_le.mp (hx i)
    constructor <;> push_cast <;> linarith
  let q : Fin k → Fin (2*R+1) := fun i =>
    ⟨⌊x i+(R:ℝ)⌋₊,by have hh := Nat.floor_le_of_le (hb i).2; omega⟩
  apply mem_iUnion.mpr
  refine ⟨q,?_⟩
  intro i
  have hl := Nat.floor_le (hb i).1
  have hu := Nat.lt_floor_add_one (x i+(R:ℝ))
  change ((⌊x i+(R:ℝ)⌋₊ : ℤ)-(R:ℤ):ℤ) ≤ x i ∧ x i ≤ _
  push_cast
  constructor <;> linarith

/- Uniform nonnegative cell mass implies the exact polynomial box growth
used by the source contradiction. No simultaneous large-box convergence is
required: only finitely many cell estimates are used for each fixed box. -/
theorem measure_logarithmicBox_bound_of_unitCells {k R : ℕ} (μ : Measure (Space k))
    {C : ℝ≥0∞} (_hC : C ≠ ⊤)
    (hcell : ∀ q : Fin k → Fin (2*R+1),
      μ (logarithmicUnitCell k (fun i => ((q i).val : ℤ)-(R:ℤ))) ≤ C) :
    μ (logarithmicBox k R) ≤ ((2*R+1:ℕ):ℝ≥0∞)^k*C := by
  calc
    _ ≤ μ (⋃ q : Fin k → Fin (2*R+1),
      logarithmicUnitCell k (fun i => ((q i).val : ℤ)-(R:ℤ))) :=
        measure_mono (logarithmicBox_subset_unitCells k R)
    _ ≤ ∑ q : Fin k → Fin (2*R+1),
      μ (logarithmicUnitCell k (fun i => ((q i).val : ℤ)-(R:ℤ))) :=
        measure_iUnion_fintype_le μ _
    _ ≤ ∑ _ : Fin k → Fin (2*R+1), C := Finset.sum_le_sum (fun q _ => hcell q)
    _ = _ := by simp

/- Pointwise-eventual cell bounds are sufficient for uniformly polynomial
box mass; the threshold may depend on the box, just as in the manuscript. -/
theorem eventual_logarithmicBox_bound_of_unitCells {k : ℕ} (μ : ℕ → Measure (Space k))
    {C : ℝ} (hC : 0 ≤ C)
    (hcell : ∀ z : Fin k → ℤ, ∀ᶠ j in atTop,
      μ j (logarithmicUnitCell k z) ≤ ENNReal.ofReal C) (R : ℕ) :
    ∀ᶠ j in atTop, (μ j).real (logarithmicBox k R) ≤ (2^k*C)*(R+1:ℝ)^k := by
  have hh : ∀ᶠ j in atTop, ∀ q : Fin k → Fin (2*R+1),
      μ j (logarithmicUnitCell k (fun i => ((q i).val : ℤ)-(R:ℤ))) ≤ ENNReal.ofReal C :=
    Filter.eventually_all.mpr (fun _ => hcell _)
  filter_upwards [hh] with j hj
  have hm := measure_logarithmicBox_bound_of_unitCells (μ j) ENNReal.ofReal_ne_top hj
  have ht : ((2*R+1:ℕ):ℝ≥0∞)^k*ENNReal.ofReal C ≠ ⊤ := by finiteness
  have hr := ENNReal.toReal_mono ht hm
  simp only [Measure.real]
  apply hr.trans
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_natCast,ENNReal.toReal_ofReal hC]
  rw [show (2^k*C)*(R+1:ℝ)^k = (2*((R:ℝ)+1))^k*C by rw [mul_pow]; ring]
  apply mul_le_mul_of_nonneg_right _ hC
  apply pow_le_pow_left₀ (by positivity)
  push_cast
  linarith

end AffineBernstein

end

end OAI
