import OAI.Geometry.RCD.Coordinates.NormalizedPairing
import OAI.Geometry.RCD.Harmonic.LocalRadialDerivative
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

namespace OAI

/-! # Compact Euclidean test functions on the actual rescaled spaces -/

open Set MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def compactTestBound {n : ℕ} (ψ : Euclidean n → ℝ) (hc : Continuous ψ) (hs : HasCompactSupport ψ) : ℝ :=
  ‖ofCompactSupport ψ hc hs‖

theorem compactTestBound_nonneg {n : ℕ} (ψ : Euclidean n → ℝ)
    (hc : Continuous ψ) (hs : HasCompactSupport ψ) : 0 ≤ compactTestBound ψ hc hs := norm_nonneg _

theorem compactTestBound_spec {n : ℕ} (ψ : Euclidean n → ℝ)
    (hc : Continuous ψ) (hs : HasCompactSupport ψ) (x : Euclidean n) :
    |ψ x| ≤ compactTestBound ψ hc hs :=
  (ofCompactSupport ψ hc hs).norm_coe_le_norm x

def compactTestLp {n : ℕ} (s : Set X) (hfin : μ s ≠ ∞)
    (V : X → Euclidean n) (hV : Measurable V) (ψ : Euclidean n → ℝ)
    (hc : Continuous ψ) (hs : HasCompactSupport ψ) : Lp ℝ 2 (μ.restrict s) := by
  let : IsFiniteMeasure (μ.restrict s) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfin.lt_top⟩
  have hmem : MemLp (fun x => ψ (V x)) 2 (μ.restrict s) :=
    MemLp.of_bound (hc.measurable.comp hV).aestronglyMeasurable (compactTestBound ψ hc hs)
      (Filter.Eventually.of_forall (fun x => compactTestBound_spec ψ hc hs (V x)))
  exact hmem.toLp (fun x => ψ (V x))

theorem compactTestLp_coe {n : ℕ} (s : Set X) (hfin : μ s ≠ ∞)
    (V : X → Euclidean n) (hV : Measurable V) (ψ : Euclidean n → ℝ)
    (hc : Continuous ψ) (hs : HasCompactSupport ψ) :
    compactTestLp μ s hfin V hV ψ hc hs =ᵐ[μ.restrict s] fun x => ψ (V x) := by
  unfold compactTestLp
  exact MemLp.coeFn_toLp _

theorem compactTestLp_normalized_norm {n : ℕ} (s : Set X) (hfin : μ s ≠ ∞)
    (V : X → Euclidean n) (hV : Measurable V) (ψ : Euclidean n → ℝ)
    (hc : Continuous ψ) (hs : HasCompactSupport ψ) :
    ‖normalizeLocalL2 μ s hfin (compactTestLp μ s hfin V hV ψ hc hs)‖ ≤
      compactTestBound ψ hc hs := by
  apply normalized_norm_le_of_bound μ s hfin _ (compactTestBound_nonneg ψ hc hs)
  filter_upwards [compactTestLp_coe μ s hfin V hV ψ hc hs] with x hx
  rw [hx]
  exact compactTestBound_spec ψ hc hs (V x)

theorem compactTest_one_pairing {n : ℕ} (s : Set X) (hfin : μ s ≠ ∞)
    (V : X → Euclidean n) (hV : Measurable V) (ψ : Euclidean n → ℝ)
    (hc : Continuous ψ) (hs : HasCompactSupport ψ) :
    ⟪normalizeLocalL2 μ s hfin (compactTestLp μ s hfin V hV ψ hc hs),
      normalizeLocalL2 μ s hfin (restrictedOne μ s hfin)⟫_ℝ =
        (μ.real s)⁻¹ * ∫ x in s, ψ (V x) ∂μ := by
  have hone : restrictedOne μ s hfin =ᵐ[μ.restrict s] fun _ => (1 : ℝ) := by
    simpa only [restrictedOne, indicator_univ] using
      (indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := μ.restrict s)
        (hs := MeasurableSet.univ) (hμs := by simpa using hfin) (c := (1 : ℝ)))
  simpa only [mul_one] using normalized_inner_of_representatives μ s hfin
    (compactTestLp μ s hfin V hV ψ hc hs) (restrictedOne μ s hfin)
    (fun x => ψ (V x)) (fun _ => (1 : ℝ)) (compactTestLp_coe μ s hfin V hV ψ hc hs) hone

variable [MetricSpace X] [BorelSpace X] [ProperSpace X] (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] in
theorem compactTest_sobolev_pairing {n : ℕ} (s : Set X) (hfin : μ s ≠ ∞)
    (V : X → Euclidean n) (hV : Measurable V) (ψ : Euclidean n → ℝ)
    (hc : Continuous ψ) (hs : HasCompactSupport ψ) (w : SobolevSpace μ hQ) :
    ⟪normalizeLocalL2 μ s hfin (compactTestLp μ s hfin V hV ψ hc hs),
      normalizeLocalL2 μ s hfin (SobolevSpace.restrictLp μ hQ s w)⟫_ℝ =
        (μ.real s)⁻¹ * ∫ x in s, ψ (V x) * SobolevSpace.toLp μ hQ w x ∂μ :=
  normalized_inner_of_representatives μ s hfin _ _ _ _
    (compactTestLp_coe μ s hfin V hV ψ hc hs) (SobolevSpace.restrictLp_coe μ hQ s w)

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] in
/-- Normalization preserves the full finite affine Euler identity. -/
theorem normalized_euler_identity {n : ℕ} (s : Set X) (hfin : μ s ≠ ∞)
    (w e d one : Lp ℝ 2 (μ.restrict s)) (u : Fin n → Lp ℝ 2 (μ.restrict s))
    (ell : Fin n → ℝ) (k a : ℝ)
    (hid : a • d = w + ∑ j, ell j • u j + k • one + e) :
    a • normalizeLocalL2 μ s hfin d = normalizeLocalL2 μ s hfin w +
      ∑ j, ell j • normalizeLocalL2 μ s hfin (u j) +
        k • normalizeLocalL2 μ s hfin one + normalizeLocalL2 μ s hfin e := by
  have hh := congrArg (normalizeLocalL2 μ s hfin) hid
  simpa only [normalizeLocalL2, smul_add, Finset.smul_sum,
    smul_comm a, smul_comm k, smul_comm _ (‖restrictedOne μ s hfin‖⁻¹)] using hh

/-- The normalized radial pairing is exactly the rescaled test integral
appearing in Ambrosio--Honda's weak gradient convergence. -/
theorem compactTest_radial_pairing {n : ℕ} (s : Set X) (hfin : μ s ≠ ∞)
    (V : X → Euclidean n) (hV : Measurable V) (ψ : Euclidean n → ℝ)
    (hc : Continuous ψ) (hs : HasCompactSupport ψ) (f w : SobolevSpace μ hQ)
    {B : ℝ} (hf : ∀ᵐ x ∂μ.restrict s, localGamma μ hQ f f x ≤ B) (a : ℝ) :
    ⟪normalizeLocalL2 μ s hfin (compactTestLp μ s hfin V hV ψ hc hs),
      a • normalizeLocalL2 μ s hfin (localRadialDerivative μ hQ s f hf w)⟫_ℝ =
        (μ.real s)⁻¹ * ∫ x in s, ψ (V x) * (a * localGamma μ hQ f w x) ∂μ := by
  have hg : (a • localRadialDerivative μ hQ s f hf w : Lp ℝ 2 (μ.restrict s)) =ᵐ[μ.restrict s]
      fun x => a * localGamma μ hQ f w x := by
    filter_upwards [Lp.coeFn_smul a (localRadialDerivative μ hQ s f hf w),
      localRadialDerivative_representative μ hQ s f w hf] with x hs hg
    simp only [hs, Pi.smul_apply, smul_eq_mul, hg]
  have hh := normalized_inner_of_representatives μ s hfin
    (compactTestLp μ s hfin V hV ψ hc hs) (a • localRadialDerivative μ hQ s f hf w)
    (fun x => ψ (V x)) (fun x => a * localGamma μ hQ f w x)
    (compactTestLp_coe μ s hfin V hV ψ hc hs) hg
  simpa only [normalizeLocalL2, smul_comm a] using hh

end RegularPointCoordinates

end

end OAI
