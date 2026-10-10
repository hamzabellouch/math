import OAI.Geometry.EinsteinFour.ScalarPoissonKernelSourceChain
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

namespace OAI

/-! Concrete nested compact cutoffs inside the unit ball. Their radii tend
to one, while each support lies strictly inside the next region of value one. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal Topology

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

private def scalarBumpGap (r : ℝ) (k : ℕ) : ℝ := (1 - r) * (1 / 4 : ℝ) ^ (k + 1)

private theorem scalarBumpGap_pos {r : ℝ} (hr : r < 1) (k : ℕ) :
    0 < scalarBumpGap r k := by
  exact mul_pos (sub_pos.mpr hr) (pow_pos (by norm_num) _)

private theorem scalarBumpGap_lt {r : ℝ} (hr : r < 1) (k : ℕ) :
    scalarBumpGap r k < 1 - r := by
  have hp : (1 / 4 : ℝ) ^ (k + 1) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero k)
  simpa only [scalarBumpGap, mul_one] using
    mul_lt_mul_of_pos_left hp (sub_pos.mpr hr)

private theorem scalarBumpGap_succ (r : ℝ) (k : ℕ) :
    scalarBumpGap r (k + 1) = scalarBumpGap r k / 4 := by
  simp only [scalarBumpGap, pow_succ]
  ring

/-- A concrete real bump; the gap shrinks geometrically with the index. -/
def scalarNestedRealBump (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) :
    ContDiffBump (0 : V) where
  rIn := 1 - scalarBumpGap r k
  rOut := 1 - scalarBumpGap r k / 2
  rIn_pos := by
    have hg := scalarBumpGap_lt hr1 k
    linarith
  rIn_lt_rOut := by
    have hg := scalarBumpGap_pos hr1 k
    linarith

private theorem scalarNestedRealBump_inner {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) :
    r < (scalarNestedRealBump r hr0 hr1 k).rIn := by
  change r < 1 - scalarBumpGap r k
  linarith [scalarBumpGap_lt hr1 k]

private theorem scalarNestedRealBump_outer {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) :
    (scalarNestedRealBump r hr0 hr1 k).rOut < 1 := by
  change 1 - scalarBumpGap r k / 2 < 1
  linarith [scalarBumpGap_pos hr1 k]

private theorem scalarNestedRealBump_separated {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) :
    (scalarNestedRealBump r hr0 hr1 k).rOut <
      (scalarNestedRealBump r hr0 hr1 (k + 1)).rIn := by
  change 1 - scalarBumpGap r k / 2 < 1 - scalarBumpGap r (k + 1)
  rw [scalarBumpGap_succ]
  linarith [scalarBumpGap_pos hr1 k]

/-- Complexification turns the actual compact real bump into a Schwartz cutoff. -/
def scalarNestedBumpSchwartz (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) : S :=
  ((scalarNestedRealBump r hr0 hr1 k).hasCompactSupport.comp_left
    (show Complex.ofReal (0 : ℝ) = 0 by rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (scalarNestedRealBump r hr0 hr1 k).contDiff)

theorem scalarNestedBumpSchwartz_apply (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (k : ℕ) (x : V) :
    scalarNestedBumpSchwartz r hr0 hr1 k x = (scalarNestedRealBump r hr0 hr1 k x : ℂ) := rfl

private theorem scalarNestedBumpSchwartz_tsupport (r : ℝ) (hr0 : 0 < r)
    (hr1 : r < 1) (k : ℕ) :
    tsupport (scalarNestedBumpSchwartz r hr0 hr1 k : V → ℂ) =
      closedBall 0 (scalarNestedRealBump r hr0 hr1 k).rOut := by
  have hs : Function.support (scalarNestedBumpSchwartz r hr0 hr1 k : V → ℂ) =
      Function.support (scalarNestedRealBump r hr0 hr1 k : V → ℝ) := by
    ext x
    simp only [Function.mem_support, scalarNestedBumpSchwartz_apply, ne_eq,
      Complex.ofReal_eq_zero]
  rw [tsupport, hs]
  exact (scalarNestedRealBump r hr0 hr1 k).tsupport_eq

private theorem scalarNestedBumpSchwartz_one_nhds (r : ℝ) (hr0 : 0 < r)
    (hr1 : r < 1) (k : ℕ) {x : V}
    (hx : x ∈ ball 0 (scalarNestedRealBump r hr0 hr1 k).rIn) :
    (scalarNestedBumpSchwartz r hr0 hr1 k : V → ℂ) =ᶠ[𝓝 x] fun _ => 1 := by
  filter_upwards [(scalarNestedRealBump r hr0 hr1 k).eventuallyEq_one_of_mem_ball hx] with y hy
  simp only [scalarNestedBumpSchwartz_apply, hy, Pi.one_apply, Complex.ofReal_one]

private theorem scalarNestedBumpSchwartz_nested (r : ℝ) (hr0 : 0 < r)
    (hr1 : r < 1) (k : ℕ) :
    ScalarCutoffNested (scalarNestedBumpSchwartz r hr0 hr1 k)
      (scalarNestedBumpSchwartz r hr0 hr1 (k + 1)) := by
  intro x hx
  rw [scalarNestedBumpSchwartz_tsupport] at hx
  apply scalarNestedBumpSchwartz_one_nhds
  exact (mem_closedBall.mp hx).trans_lt (scalarNestedRealBump_separated hr0 hr1 k)

/-- Every compact cutoff inside a smaller closed ball starts a concrete
infinite nested sequence supported in the open unit ball. -/
theorem exists_scalar_nested_cutoffs (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (φ : S) (hφc : HasCompactSupport (φ : V → ℂ))
    (hφ : tsupport (φ : V → ℂ) ⊆ closedBall 0 r) :
    ∃ ψ : ℕ → S, ψ 0 = φ ∧ (∀ k, ScalarCutoffNested (ψ k) (ψ (k + 1))) ∧
      ∀ k, HasCompactSupport (ψ k : V → ℂ) ∧ tsupport (ψ k : V → ℂ) ⊆ ball 0 1 := by
  let ψ : ℕ → S := fun k => match k with
    | 0 => φ
    | j + 1 => scalarNestedBumpSchwartz r hr0 hr1 j
  refine ⟨ψ, rfl, ?_, ?_⟩
  · intro k
    cases k with
    | zero =>
        intro x hx
        apply scalarNestedBumpSchwartz_one_nhds
        exact (mem_closedBall.mp (hφ hx)).trans_lt (scalarNestedRealBump_inner hr0 hr1 0)
    | succ k => exact scalarNestedBumpSchwartz_nested r hr0 hr1 k
  · intro k
    cases k with
    | zero =>
        refine ⟨hφc, ?_⟩
        intro x hx
        exact (mem_closedBall.mp (hφ hx)).trans_lt hr1
    | succ k =>
        change HasCompactSupport (scalarNestedBumpSchwartz r hr0 hr1 k : V → ℂ) ∧ _
        constructor
        · change IsCompact (tsupport (scalarNestedBumpSchwartz r hr0 hr1 k : V → ℂ))
          rw [scalarNestedBumpSchwartz_tsupport]
          exact isCompact_closedBall _ _
        · intro x hx
          rw [scalarNestedBumpSchwartz_tsupport] at hx
          exact (mem_closedBall.mp hx).trans_lt (scalarNestedRealBump_outer hr0 hr1 k)

/-- Local H1 and a smooth localized equation imply every local integer
Sobolev order; all cutoff-existence obligations are constructed above. -/
theorem scalar_ball_local_sobolev
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (u : T)
    (hH1 : ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 → MemSobolev 1 2 (M ψ u))
    (hforce : ∀ n : ℕ, ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 →
        MemSobolev (n : ℝ) 2 (M ψ (scalarPerturbedOperator a b u)))
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (φ : S)
    (hφc : HasCompactSupport (φ : V → ℂ))
    (hφ : tsupport (φ : V → ℂ) ⊆ closedBall 0 r) :
    ∀ n : ℕ, MemSobolev (n : ℝ) 2 (M φ u) := by
  obtain ⟨ψ, hψ, hnest, hsupp⟩ := exists_scalar_nested_cutoffs r hr0 hr1 φ hφc hφ
  apply scalar_cutoff_family_all_orders a b δ hδ ha ha1 ha2 hb hb1 hsmall u φ
  intro n
  exact ⟨ψ, hψ, fun k _ => hnest k, hH1 (ψ n) (hsupp n).1 (hsupp n).2,
    fun k _ => hforce n (ψ k) (hsupp k).1 (hsupp k).2⟩


/-- The geometric remainder P u - u suffices; the solution itself is
initially assumed only locally H1. -/
theorem scalar_ball_local_sobolev_of_remainder
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (u : T)
    (hH1 : ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 → MemSobolev 1 2 (M ψ u))
    (hforce : ∀ n : ℕ, ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 →
        MemSobolev (n : ℝ) 2 (M ψ (scalarPerturbedOperator a b u - u)))
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (φ : S)
    (hφc : HasCompactSupport (φ : V → ℂ))
    (hφ : tsupport (φ : V → ℂ) ⊆ closedBall 0 r) :
    ∀ n : ℕ, MemSobolev (n : ℝ) 2 (M φ u) := by
  obtain ⟨ψ, hψ, hnest, hsupp⟩ := exists_scalar_nested_cutoffs r hr0 hr1 φ hφc hφ
  apply scalar_cutoff_family_all_orders_of_remainder a b δ hδ ha ha1 ha2 hb hb1 hsmall u φ
  intro n
  exact ⟨ψ, hψ, fun k _ => hnest k, hH1 (ψ n) (hsupp n).1 (hsupp n).2,
    fun k _ => hforce n (ψ k) (hsupp k).1 (hsupp k).2⟩

end
end PositiveEinsteinFour.Geometry

end OAI
