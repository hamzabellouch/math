import OAI.Geometry.EinsteinFour.ScalarPoissonKernelSourceChain
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

namespace OAI

/-! Nested cutoffs inside the half ball, used after the first local H2 gain. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal Topology

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

private def scalarHalfBumpGap (r : ℝ) (k : ℕ) : ℝ := (1 / 2 - r) * (1 / 4 : ℝ) ^ (k + 1)

private theorem scalarHalfBumpGap_pos {r : ℝ} (hr : r < 1 / 2) (k : ℕ) :
    0 < scalarHalfBumpGap r k := by
  exact mul_pos (sub_pos.mpr hr) (pow_pos (by norm_num) _)

private theorem scalarHalfBumpGap_lt {r : ℝ} (hr : r < 1 / 2) (k : ℕ) :
    scalarHalfBumpGap r k < 1 / 2 - r := by
  have hp : (1 / 4 : ℝ) ^ (k + 1) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero k)
  simpa only [scalarHalfBumpGap, mul_one] using
    mul_lt_mul_of_pos_left hp (sub_pos.mpr hr)

private theorem scalarHalfBumpGap_succ (r : ℝ) (k : ℕ) :
    scalarHalfBumpGap r (k + 1) = scalarHalfBumpGap r k / 4 := by
  simp only [scalarHalfBumpGap, pow_succ]
  ring

/-- A concrete real bump; the gap shrinks geometrically with the index. -/
def scalarHalfNestedRealBump (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1 / 2) (k : ℕ) :
    ContDiffBump (0 : V) where
  rIn := 1 / 2 - scalarHalfBumpGap r k
  rOut := 1 / 2 - scalarHalfBumpGap r k / 2
  rIn_pos := by
    have hg := scalarHalfBumpGap_lt hr1 k
    linarith
  rIn_lt_rOut := by
    have hg := scalarHalfBumpGap_pos hr1 k
    linarith

private theorem scalarHalfNestedRealBump_inner {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1 / 2) (k : ℕ) :
    r < (scalarHalfNestedRealBump r hr0 hr1 k).rIn := by
  change r < 1 / 2 - scalarHalfBumpGap r k
  linarith [scalarHalfBumpGap_lt hr1 k]

private theorem scalarHalfNestedRealBump_outer {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1 / 2) (k : ℕ) :
    (scalarHalfNestedRealBump r hr0 hr1 k).rOut < 1 / 2 := by
  change 1 / 2 - scalarHalfBumpGap r k / 2 < 1 / 2
  linarith [scalarHalfBumpGap_pos hr1 k]

private theorem scalarHalfNestedRealBump_separated {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1 / 2) (k : ℕ) :
    (scalarHalfNestedRealBump r hr0 hr1 k).rOut <
      (scalarHalfNestedRealBump r hr0 hr1 (k + 1)).rIn := by
  change 1 / 2 - scalarHalfBumpGap r k / 2 < 1 / 2 - scalarHalfBumpGap r (k + 1)
  rw [scalarHalfBumpGap_succ]
  linarith [scalarHalfBumpGap_pos hr1 k]

/-- Complexification turns the actual compact real bump into a Schwartz cutoff. -/
def scalarHalfNestedBumpSchwartz (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1 / 2) (k : ℕ) : S :=
  ((scalarHalfNestedRealBump r hr0 hr1 k).hasCompactSupport.comp_left
    (show Complex.ofReal (0 : ℝ) = 0 by rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (scalarHalfNestedRealBump r hr0 hr1 k).contDiff)

theorem scalarHalfNestedBumpSchwartz_apply (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1 / 2)
    (k : ℕ) (x : V) :
    scalarHalfNestedBumpSchwartz r hr0 hr1 k x = (scalarHalfNestedRealBump r hr0 hr1 k x : ℂ) := rfl

private theorem scalarHalfNestedBumpSchwartz_tsupport (r : ℝ) (hr0 : 0 < r)
    (hr1 : r < 1 / 2) (k : ℕ) :
    tsupport (scalarHalfNestedBumpSchwartz r hr0 hr1 k : V → ℂ) =
      closedBall 0 (scalarHalfNestedRealBump r hr0 hr1 k).rOut := by
  have hs : Function.support (scalarHalfNestedBumpSchwartz r hr0 hr1 k : V → ℂ) =
      Function.support (scalarHalfNestedRealBump r hr0 hr1 k : V → ℝ) := by
    ext x
    simp only [Function.mem_support, scalarHalfNestedBumpSchwartz_apply, ne_eq,
      Complex.ofReal_eq_zero]
  rw [tsupport, hs]
  exact (scalarHalfNestedRealBump r hr0 hr1 k).tsupport_eq

private theorem scalarHalfNestedBumpSchwartz_one_nhds (r : ℝ) (hr0 : 0 < r)
    (hr1 : r < 1 / 2) (k : ℕ) {x : V}
    (hx : x ∈ ball 0 (scalarHalfNestedRealBump r hr0 hr1 k).rIn) :
    (scalarHalfNestedBumpSchwartz r hr0 hr1 k : V → ℂ) =ᶠ[𝓝 x] fun _ => 1 := by
  filter_upwards [(scalarHalfNestedRealBump r hr0 hr1 k).eventuallyEq_one_of_mem_ball hx] with y hy
  simp only [scalarHalfNestedBumpSchwartz_apply, hy, Pi.one_apply, Complex.ofReal_one]

private theorem scalarHalfNestedBumpSchwartz_nested (r : ℝ) (hr0 : 0 < r)
    (hr1 : r < 1 / 2) (k : ℕ) :
    ScalarCutoffNested (scalarHalfNestedBumpSchwartz r hr0 hr1 k)
      (scalarHalfNestedBumpSchwartz r hr0 hr1 (k + 1)) := by
  intro x hx
  rw [scalarHalfNestedBumpSchwartz_tsupport] at hx
  apply scalarHalfNestedBumpSchwartz_one_nhds
  exact (mem_closedBall.mp hx).trans_lt (scalarHalfNestedRealBump_separated hr0 hr1 k)

/-- Every compact cutoff inside a smaller closed ball starts a concrete
infinite nested sequence supported in the open unit ball. -/
theorem exists_scalar_half_nested_cutoffs (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1 / 2)
    (φ : S) (hφc : HasCompactSupport (φ : V → ℂ))
    (hφ : tsupport (φ : V → ℂ) ⊆ closedBall 0 r) :
    ∃ ψ : ℕ → S, ψ 0 = φ ∧ (∀ k, ScalarCutoffNested (ψ k) (ψ (k + 1))) ∧
      ∀ k, HasCompactSupport (ψ k : V → ℂ) ∧ tsupport (ψ k : V → ℂ) ⊆ ball 0 (1 / 2) := by
  let ψ : ℕ → S := fun k => match k with
    | 0 => φ
    | j + 1 => scalarHalfNestedBumpSchwartz r hr0 hr1 j
  refine ⟨ψ, rfl, ?_, ?_⟩
  · intro k
    cases k with
    | zero =>
        intro x hx
        apply scalarHalfNestedBumpSchwartz_one_nhds
        exact (mem_closedBall.mp (hφ hx)).trans_lt (scalarHalfNestedRealBump_inner hr0 hr1 0)
    | succ k => exact scalarHalfNestedBumpSchwartz_nested r hr0 hr1 k
  · intro k
    cases k with
    | zero =>
        refine ⟨hφc, ?_⟩
        intro x hx
        exact (mem_closedBall.mp (hφ hx)).trans_lt hr1
    | succ k =>
        change HasCompactSupport (scalarHalfNestedBumpSchwartz r hr0 hr1 k : V → ℂ) ∧ _
        constructor
        · change IsCompact (tsupport (scalarHalfNestedBumpSchwartz r hr0 hr1 k : V → ℂ))
          rw [scalarHalfNestedBumpSchwartz_tsupport]
          exact isCompact_closedBall _ _
        · intro x hx
          rw [scalarHalfNestedBumpSchwartz_tsupport] at hx
          exact (mem_closedBall.mp hx).trans_lt (scalarHalfNestedRealBump_outer hr0 hr1 k)


end
end PositiveEinsteinFour.Geometry

end OAI
