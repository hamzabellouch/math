import OAI.NumberTheory.JointDickman.Basic
import OAI.NumberTheory.Jacobsthal.Renewal.DickmanFiniteDecay
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-!
# The joint Dickman law and strict ordering densities

The moving smoothness thresholds for both consecutive integers use the base `n`.
Counting is ordinary natural density through real endpoints.
-/

namespace JointDickman

open Filter
open scoped Topology

/-- The paper's real-endpoint ordinary density. The natural floor is harmless
for the positive endpoints in the limit, and includes exactly `2 ≤ n ≤ X`. -/
noncomputable def realDensity (P : ℕ → Prop) (X : ℝ) : ℝ :=
  (empiricalCount P ⌊X⌋₊ : ℝ) / X

/-- Integer-scale ordinary density gives the same limit through all real
endpoints. The factor `floor X / X` accounts for the change of normalization. -/
theorem realDensity_tendsto_of_nat {P : ℕ → Prop} {L : ℝ}
    (h : Tendsto (empiricalDensity P) atTop (𝓝 L)) :
    Tendsto (realDensity P) atTop (𝓝 L) := by
  have hprod := (h.comp (tendsto_nat_floor_atTop (α := ℝ))).mul
    (tendsto_nat_floor_div_atTop (R := ℝ))
  have heq : realDensity P =ᶠ[atTop]
      (fun X : ℝ => empiricalDensity P ⌊X⌋₊ * ((⌊X⌋₊ : ℝ) / X)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    have hN : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by simpa using hX)
    have hN0 : (⌊X⌋₊ : ℝ) ≠ 0 := by exact_mod_cast (show ⌊X⌋₊ ≠ 0 by omega)
    dsimp [realDensity, empiricalDensity]
    field_simp
  have hlimit : Tendsto
      (fun X : ℝ => empiricalDensity P ⌊X⌋₊ * ((⌊X⌋₊ : ℝ) / X))
      atTop (𝓝 L) := by simpa using hprod
  exact hlimit.congr' heq.symm

/-- Theorem 1 (`thm:main`): the moving-threshold joint Dickman law, through
all real endpoints with ordinary counting. Both powers use the base `n`. -/
def JointDickmanLaw : Prop :=
  ∀ a b : ℝ, 0 < a → a < 1 → 0 < b → b < 1 →
    Tendsto (realDensity (movingEvent a b)) atTop
      (𝓝 (Erdos970.NumberTheoryLean.Dickman.rho (1 / a) *
        Erdos970.NumberTheoryLean.Dickman.rho (1 / b)))

/-- Corollary 2 (`cor:comparison`), first strict ordering. -/
def IncreasingOrderLaw : Prop :=
  Tendsto (realDensity (fun n => n.maxPrimeFac < (n + 1).maxPrimeFac))
    atTop (𝓝 (1 / 2))

/-- The reverse ordering has the same density. -/
def DecreasingOrderLaw : Prop :=
  Tendsto (realDensity (fun n => (n + 1).maxPrimeFac < n.maxPrimeFac))
    atTop (𝓝 (1 / 2))

/-- The sum of the two strict-ordering densities has an exact elementary
formula. No joint-distribution assertion is used here. -/
theorem ordering_density_sum (X : ℝ) :
    realDensity (fun n => n.maxPrimeFac < (n + 1).maxPrimeFac) X +
      realDensity (fun n => (n + 1).maxPrimeFac < n.maxPrimeFac) X =
        ((⌊X⌋₊ - 1 : ℕ) : ℝ) / X := by
  rw [realDensity, realDensity, ← add_div, ← Nat.cast_add, orderingCounts_add]

theorem ordering_density_sum_tendsto :
    Tendsto (fun X : ℝ =>
      realDensity (fun n => n.maxPrimeFac < (n + 1).maxPrimeFac) X +
        realDensity (fun n => (n + 1).maxPrimeFac < n.maxPrimeFac) X)
      atTop (𝓝 1) := by
  have hinv : Tendsto (fun X : ℝ => 1 / X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h := (tendsto_nat_floor_div_atTop (R := ℝ)).sub hinv
  have heq : (fun X : ℝ =>
      realDensity (fun n => n.maxPrimeFac < (n + 1).maxPrimeFac) X +
        realDensity (fun n => (n + 1).maxPrimeFac < n.maxPrimeFac) X) =ᶠ[atTop]
      (fun X : ℝ => (⌊X⌋₊ : ℝ) / X - 1 / X) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    have hN : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by simpa using hX)
    rw [ordering_density_sum, Nat.cast_sub hN, Nat.cast_one, sub_div]
  have hh : Tendsto (fun X : ℝ => (⌊X⌋₊ : ℝ) / X - 1 / X) atTop (𝓝 1) := by
    simpa using h
  exact hh.congr' heq.symm

/-- It is enough to prove either ordering density. Complementarity supplies
the other; this does not establish their common value independently. -/
theorem increasingOrderLaw_iff_decreasingOrderLaw :
    IncreasingOrderLaw ↔ DecreasingOrderLaw := by
  constructor
  · intro h
    unfold IncreasingOrderLaw at h
    unfold DecreasingOrderLaw
    have ht := ordering_density_sum_tendsto.sub h
    convert ht using 1
    · ext X
      ring
    · norm_num
  · intro h
    unfold DecreasingOrderLaw at h
    unfold IncreasingOrderLaw
    have ht := ordering_density_sum_tendsto.sub h
    convert ht using 1
    · ext X
      ring
    · norm_num

end JointDickman

end OAI
