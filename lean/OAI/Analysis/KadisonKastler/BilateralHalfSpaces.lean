import OAI.Analysis.KadisonKastler.BilateralCoordinateSigma
import OAI.Analysis.KadisonKastler.IndependentL2Variance

namespace OAI

/-! Closed coordinate subspaces and their constant intersection. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory Set

variable {X K : Type*} [mX : MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup K] [CompleteSpace K]

theorem aestronglyMeasurable_of_L2_approximations {m : MeasurableSpace X} (hm : m ≤ mX)
    (f : Lp K 2 μ)
    (happrox : ∀ ε > (0 : ℝ), ∃ g : Lp K 2 μ, AEStronglyMeasurable[m] g μ ∧ dist f g < ε) :
    AEStronglyMeasurable[m] f μ := by
  have hc : IsClosed {g : Lp K 2 μ | AEStronglyMeasurable[m] g μ} :=
    isClosed_aestronglyMeasurable hm
  exact hc.closure_subset (Metric.mem_closure_iff.mpr happrox)

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [InnerProductSpace ℂ K] [TopologicalSpace.SeparableSpace K]

theorem bilateral_L2_constant_of_half_measurable (f : Lp K 2 (bilateralWalkLaw G))
    (hp : AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) {j : ℤ | 0 ≤ j}]
      f (bilateralWalkLaw G))
    (hn : AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) {j : ℤ | j < 0}]
      f (bilateralWalkLaw G)) :
    f = hilbertConstantL2 (bilateralWalkLaw G) (∫ ω, f ω ∂bilateralWalkLaw G) := by
  borelize K
  have hd : Disjoint {j : ℤ | 0 ≤ j} {j : ℤ | j < 0} := by
    apply Set.disjoint_left.mpr
    intro j hp hn
    change 0 ≤ j at hp
    change j < 0 at hn
    omega
  have hi := bilateralCoordinate_indepFun hd hp.stronglyMeasurable_mk.measurable
    hn.stronglyMeasurable_mk.measurable hp.ae_eq_mk hn.ae_eq_mk
  let : InnerProductSpace ℝ K := InnerProductSpace.complexToReal
  have h := independent_L2_centering_le f f hi
  rw [sub_self, norm_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

end

end KadisonKastler

end OAI
