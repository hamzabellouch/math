import OAI.Probability.SLE.Loewner.InitialForwardChart
import OAI.Probability.SLE.Loewner.InitialInverseNormalFamily

namespace OAI

/-! The compactified forward charts form a bounded normal family on the final domain. -/
noncomputable section
open Set Filter Function
open scoped Topology

namespace SLEExactGauge

theorem initialForwardCayley_subsequence (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    (t : ℕ → unitInterval) :
    ∃ (φ : ℕ → ℕ) (F : ℂ → ℂ), StrictMono φ ∧
      DifferentiableOn ℂ F (upperHalfPlane \ range p) ∧
      TendstoLocallyUniformlyOn
        (fun n z => halfPlaneCayley (initialForwardChart p hi h0 hH (t (φ n)) z))
        F atTop (upperHalfPlane \ range p) := by
  have hD : IsOpen (upperHalfPlane \ range p) :=
    isOpen_upperHalfPlane.sdiff (isCompact_range p.continuous).isClosed
  apply TauCeti.montel (F := fun n z => halfPlaneCayley (initialForwardChart p hi h0 hH (t n) z)) hD
  · intro n
    exact halfPlaneCayley_differentiableOn.comp
      (initialForwardChart_differentiableOn p hi h0 hH (t n))
      (initialForwardChart_mapsTo p hi h0 hH (t n))
  · apply TauCeti.isLocallyBoundedOn_of_forall_norm_le (C := 1)
    intro n z hz
    exact (halfPlaneCayley_norm_lt
      (initialForwardChart_mapsTo p hi h0 hH (t n) hz)).le

end SLEExactGauge

end

end OAI
