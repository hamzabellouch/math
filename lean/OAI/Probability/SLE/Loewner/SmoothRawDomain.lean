import OAI.Probability.SLE.Loewner.RawLifetimeTrace
import OAI.Probability.SLE.Loewner.TargetSurvivalLifetime
import OAI.Probability.SLE.Loewner.SmoothRawGeometry

namespace OAI

/-! For a smooth driver the raw survival domain is the geometric slit
domain. Every lost interior point is a tip at its first lifetime. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace SLEExactGauge

theorem Target.exists_trace_time_of_not_surviving
    (b : Driver) (z : ℂ) (hz : z ∈ upperHalfPlane) (T : ℝ≥0)
    (hdead : ¬Surviving 1 b z T) (b' : ℝ → ℝ) (L : ℝ≥0)
    (hd : ∀ t, 0 ≤ t → HasDerivWithinAt (driverValue b) (b' t) (Ici 0) t)
    (hb : ∀ t, 0 ≤ t → |b' t| ≤ L) :
    ∃ τ : ℝ≥0, 0 < τ ∧ τ ≤ T ∧ z=trace 1 b τ := by
  obtain ⟨τ,hτ,hτT,hs⟩ := exists_survival_lifetime 1 b z hz T.coe_nonneg hdead
  refine ⟨⟨τ,hτ.le⟩,hτ,hτT,?_⟩
  apply eq_trace_at_lifetime b z hz hτ
    (fun t ht htτ => (hs t ht).mpr htτ)
    (fun h => lt_irrefl τ ((hs τ hτ.le).mp h))
    b' (fun t ht => (hd t ht.1).mono Icc_subset_Ici_self) L.coe_nonneg
    (fun t ht => hb t ht.1)

theorem Target.smooth_geometric_subset_raw_surviving
    (b : Driver) (b' : ℝ → ℝ) (L : ℝ≥0)
    (hd : ∀ t, 0 ≤ t → HasDerivWithinAt (driverValue b) (b' t) (Ici 0) t)
    (hb : ∀ t, 0 ≤ t → |b' t| ≤ L) (T : ℝ≥0) :
    survivingDomain (fun s : ℝ≥0 => trace 1 b s) T ⊆ {z | Surviving 1 b z T} := by
  intro z hz
  by_contra hn
  obtain ⟨τ,_hτ,hτT,he⟩ := exists_trace_time_of_not_surviving b z hz.1.1 T hn b' L hd hb
  exact hz.1.2 ⟨τ,⟨zero_le,hτT⟩,he.symm⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}

theorem RegularSLEPresentation.smooth_raw_surviving_eq_geometric
    (a : RegularSLEPresentation P κ γ) (hκ : 0 < κ)
    (b : Target.Driver) (b' : ℝ → ℝ) (L : ℝ≥0)
    (hd : ∀ t, 0 ≤ t → HasDerivWithinAt (Target.driverValue b) (b' t) (Ici 0) t)
    (hb : ∀ t, 0 ≤ t → |b' t| ≤ L) (T : ℝ≥0) (hT : 0 < T) :
    {z | Target.Surviving 1 b z T} =
      survivingDomain (fun s : ℝ≥0 => Target.trace 1 b s) T :=
  Set.Subset.antisymm (a.smooth_raw_surviving_subset_geometric hκ b b' L hd hb T hT)
    (Target.smooth_geometric_subset_raw_surviving b b' L hd hb T)

end SLEExactGauge

end

end OAI
