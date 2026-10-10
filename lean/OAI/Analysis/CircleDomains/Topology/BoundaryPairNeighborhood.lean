import OAI.Analysis.CircleDomains.Topology.CircleBoundaryPersistence
import OAI.Analysis.CircleDomains.Probability.PathHitLaws
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc

namespace OAI

/-! Open exclusion neighborhoods use the actual fixed-source boundary
functional. Its continuity is proved from the disk-distance estimate;
no stability or exclusion assertion is assumed. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal

noncomputable section
namespace CircleDomainRigidity

abbrev BoundaryPairData := C(PathTime, ℂ) × (ℂ × ℝ≥0)

def boundaryPairFunctional (v : ℝ → ℝ) (p : BoundaryPairData) : ℝ :=
  roundDiskBoundaryPairing (p.1 ∘ projIcc 0 1 zero_le_one) p.2.1 p.2.2 v

def boundaryCurveTrace (γ : ℝ → ℂ) (hγ : Continuous γ) : C(PathTime, ℂ) :=
  ⟨fun t => γ t, hγ.comp continuous_subtype_val⟩

 theorem boundaryPairFunctional_trace (γ : ℝ → ℂ) (hγ : Continuous γ)
    (c : ℂ) (r : ℝ≥0) (v : ℝ → ℝ) :
    boundaryPairFunctional v (boundaryCurveTrace γ hγ, c, r) =
      roundDiskBoundaryPairing γ c r v := by
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
  change infDist (γ (projIcc 0 1 zero_le_one t)) (closedBall c (r : ℝ)) * deriv v t = _
  rw [coe_projIcc, min_eq_right ht'.2, max_eq_right ht'.1]

 theorem boundaryPairFunctional_lipschitz (v : ℝ → ℝ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    ∃ L : ℝ≥0, LipschitzWith L (boundaryPairFunctional v) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    (hv.continuous_deriv (by simp)).continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by simp))
  refine ⟨⟨3 * M, by positivity⟩, LipschitzWith.of_dist_le_mul ?_⟩
  intro p q
  have h := roundDiskBoundaryPairing_stability
    (p.1 ∘ projIcc 0 1 zero_le_one) (q.1 ∘ projIcc 0 1 zero_le_one)
    (p.1.continuous.comp continuous_projIcc) (q.1.continuous.comp continuous_projIcc)
    p.2.1 q.2.1 p.2.2.property q.2.2.property v hv (dist_nonneg (x := p.1) (y := q.1))
    (fun t _ => ContinuousMap.dist_apply_le_dist (projIcc 0 1 zero_le_one t))
    (fun t ht => by simpa only [Real.norm_eq_abs] using hM t ht)
  have hf : dist p.1 q.1 ≤ dist p q := by
    exact le_max_left _ _
  have hc : dist p.2.1 q.2.1 ≤ dist p q :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hr : |(p.2.2 : ℝ) - q.2.2| ≤ dist p q := by
    change dist p.2.2 q.2.2 ≤ dist p q
    exact (le_max_right _ _).trans (le_max_right _ _)
  change |boundaryPairFunctional v p - boundaryPairFunctional v q| ≤ 3 * M * dist p q
  have hs : dist p.1 q.1 + dist p.2.1 q.2.1 + |(p.2.2 : ℝ) - q.2.2| ≤ 3 * dist p q := by
    linarith
  exact h.trans ((mul_le_mul_of_nonneg_right hs hM0).trans_eq (by ring))

 theorem continuous_boundaryPairFunctional (v : ℝ → ℝ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) : Continuous (boundaryPairFunctional v) :=
  (boundaryPairFunctional_lipschitz v hv).choose_spec.continuous

/-- This is the open set excluded by a single retained period coordinate. -/
def boundaryExclusionSet (v : ℝ → ℝ) (budget : ℝ) : Set BoundaryPairData :=
  {p | budget < |boundaryPairFunctional v p|}

 theorem isOpen_boundaryExclusionSet (v : ℝ → ℝ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (budget : ℝ) :
    IsOpen (boundaryExclusionSet v budget) :=
  isOpen_lt continuous_const (continuous_boundaryPairFunctional v hv).abs

 theorem boundaryExclusionSet_excludes_stokes_limit
    (γ : ℕ → ℝ → ℂ) (γ₀ : ℝ → ℂ)
    (hγ : ∀ n, Differentiable ℝ (γ n)) (hγ₀ : Continuous γ₀)
    (O : ℕ → Set ℂ) (hO : ∀ n, IsOpen (O n))
    (u : ℕ → ℂ → UnitAddCircle) (hu : ∀ n, FiniteTransfer.SmoothCircleOn (u n) (O n))
    (hγO : ∀ n t, γ n t ∈ O n)
    (v : ℝ → ℝ) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hproj : ∀ n t, (v t : UnitAddCircle) = u n (γ n t))
    (c : ℕ → ℂ) (c₀ : ℂ) (hc : Tendsto c atTop (𝓝 c₀))
    (r : ℕ → ℝ) (r₀ : ℝ≥0) (hr : ∀ n, 0 ≤ r n)
    (hrr : Tendsto r atTop (𝓝 (r₀ : ℝ)))
    (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n) (he0 : Tendsto e atTop (𝓝 0))
    (hclose : ∀ n, ∀ t ∈ Icc (0 : ℝ) 1, dist (γ n t) (γ₀ t) ≤ e n)
    (L E B : ℝ) (εE εA : ℕ → ℝ)
    (hεE : Tendsto εE atTop (𝓝 0)) (hεA : Tendsto εA atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop,
      |circleFormIntegral (fun z => infDist z (closedBall (c n) (r n))) (u n) (γ n)| ≤
        Real.sqrt Real.pi * L * (E + εE n) + 2 * Real.pi * L * (B + εA n)) :
    (boundaryCurveTrace γ₀ hγ₀, c₀, r₀) ∉
      boundaryExclusionSet v (Real.sqrt Real.pi * L * E + 2 * Real.pi * L * B) := by
  have hb := stokes_boundary_limit_bound γ γ₀ hγ hγ₀ O hO u hu hγO v hv hproj c c₀ hc
    r hr r₀.property hrr e he he0 hclose L E B εE εA hεE hεA hbound
  change ¬ _ < |boundaryPairFunctional v _|
  rw [boundaryPairFunctional_trace]
  exact not_lt_of_ge hb

end CircleDomainRigidity

end

end OAI
