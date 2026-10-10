import OAI.Analysis.KadisonKastler.BilateralBoundaryPair
import OAI.Analysis.KadisonKastler.BoundaryPairInvariance
import OAI.Analysis.KadisonKastler.RandomWalkPrefix

namespace OAI

/-! The boundary pair transforms by the inverse increment under a bilateral shift.

The boundary uses an invariant sigma algebra, not a point quotient. Its endpoint
identities are therefore proved on measurable Hilbert-valued functions.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory ProbabilityTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

def bilateralRawHalves (ω : BilateralWalkPath G) : (ℕ → G) × (ℕ → G) :=
  (bilateralFuture G ω, bilateralReflectedPast G ω)

theorem bilateralRawHalves_measurePreserving :
    MeasurePreserving (bilateralRawHalves G) (bilateralWalkLaw G)
      ((Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G)).prod
        (Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G))) := by
  refine ⟨(bilateralFuture_measurable G).prodMk (bilateralReflectedPast_measurable G), ?_⟩
  exact ((bilateral_reflected_halves_independent G).map_prod_eq_prod_map_map
    (bilateralFuture_measurable G).aemeasurable (bilateralReflectedPast_measurable G).aemeasurable).trans
      (by rw [bilateralFuture_law, bilateralReflectedPast_law])

def bilateralTransportPairAt (g : G) (ω : BilateralWalkPath G) :
    RandomWalkPath G × RandomWalkPath G :=
  ((g⁻¹, bilateralFuture G ω), (1, randomWalkPrepend G g⁻¹ (bilateralReflectedPast G ω)))

theorem bilateralTransportPairAt_quasi (g : G) :
    Measure.QuasiMeasurePreserving (bilateralTransportPairAt G g) (bilateralWalkLaw G)
      ((randomWalkPathLaw G).prod (randomWalkPathLaw G)) :=
  (MeasureTheory.QuasiMeasurePreserving.prodMap (randomWalkRoot_quasi G g⁻¹)
    ((randomWalkRoot_quasi G 1).comp (randomWalkPrepend_quasi G g⁻¹))).comp
      (bilateralRawHalves_measurePreserving G).quasiMeasurePreserving

def bilateralTransportPair (ω : BilateralWalkPath G) : RandomWalkPath G × RandomWalkPath G :=
  bilateralTransportPairAt G (ω 0) ω

theorem bilateralTransportPair_quasi :
    Measure.QuasiMeasurePreserving (bilateralTransportPair G) (bilateralWalkLaw G)
      ((randomWalkPathLaw G).prod (randomWalkPathLaw G)) :=
  quasiMeasurePreserving_countable_selection (bilateralTransportPairAt_quasi G) (measurable_pi_apply 0)

theorem bilateralTransportPair_first (ω : BilateralWalkPath G) :
    (shiftBoundaryMap (randomWalkPathLaw G) (randomWalkAdvance G)
        (randomWalkAdvance G (bilateralTransportPair G ω).1),
      shiftBoundaryMap (randomWalkPathLaw G) (randomWalkAdvance G) (bilateralTransportPair G ω).2) =
    bilateralBoundaryPair G (bilateralTranslate G 1 ω) := by
  apply Prod.ext
  · change ((ω 0)⁻¹ * ω 0, fun n : ℕ => ω ((n + 1 : ℕ) : ℤ)) =
      (1, fun n : ℕ => ω ((n : ℤ) + 1))
    simp
  · change (1, randomWalkPrepend G (ω 0)⁻¹ (bilateralReflectedPast G ω)) =
      (1, bilateralReflectedPast G (bilateralTranslate G 1 ω))
    congr 1
    funext n
    cases n with
    | zero => simp [randomWalkPrepend, bilateralReflectedPast, bilateralPast, bilateralTranslate]
    | succ n =>
      dsimp [randomWalkPrepend, bilateralReflectedPast, bilateralPast, bilateralTranslate]
      congr 2
      omega

theorem bilateralTransportPair_second (ω : BilateralWalkPath G) :
    (shiftBoundaryMap (randomWalkPathLaw G) (randomWalkAdvance G) (bilateralTransportPair G ω).1,
      shiftBoundaryMap (randomWalkPathLaw G) (randomWalkAdvance G)
        (randomWalkAdvance G (bilateralTransportPair G ω).2)) =
    (randomWalkBoundaryAction G).diagonal.toPerm (ω 0)⁻¹ (bilateralBoundaryPair G ω) := by
  change ((_, _), (1 * (ω 0)⁻¹, _)) = ((_, _), ((ω 0)⁻¹ * 1, _))
  simp only [one_mul, mul_one]
  simp [bilateralTransportPair, bilateralTransportPairAt, randomWalkPrepend, Equiv.mulLeft]

variable {G} {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [TopologicalSpace.SeparableSpace K]

theorem bilateral_boundary_function_transport
    {f : RandomWalkBoundary G × RandomWalkBoundary G → K}
    (hf : AEStronglyMeasurable f ((randomWalkBoundaryMeasure G).prod (randomWalkBoundaryMeasure G))) :
    ∀ᵐ ω ∂bilateralWalkLaw G,
      f (bilateralBoundaryPair G (bilateralTranslate G 1 ω)) =
      f ((randomWalkBoundaryAction G).diagonal.toPerm (ω 0)⁻¹ (bilateralBoundaryPair G ω)) := by
  have hl := (bilateralTransportPair_quasi G).ae
    (boundaryPairLift_advance_left (randomWalkAdvance_quasi (G := G)) hf)
  have hr := (bilateralTransportPair_quasi G).ae
    (boundaryPairLift_advance_right (randomWalkAdvance_quasi (G := G)) hf)
  filter_upwards [hl, hr] with ω hleft hright
  change f _ = f _ at hleft hright
  rw [← bilateralTransportPair_first, ← bilateralTransportPair_second]
  exact hleft.trans hright.symm

theorem bilateral_equivariant_function_transport [CompleteSpace K]
    (σ : G →* unitary (K →L[ℂ] K)) {f : RandomWalkBoundary G × RandomWalkBoundary G → K}
    (hf : AEStronglyMeasurable f ((randomWalkBoundaryMeasure G).prod (randomWalkBoundaryMeasure G)))
    (he : ∀ g, ∀ᵐ z ∂(randomWalkBoundaryMeasure G).prod (randomWalkBoundaryMeasure G),
      f ((randomWalkBoundaryAction G).diagonal.toPerm g z) = (σ g : K →L[ℂ] K) (f z)) :
    ∀ᵐ ω ∂bilateralWalkLaw G,
      f (bilateralBoundaryPair G (bilateralTranslate G 1 ω)) =
      (σ (ω 0)⁻¹ : K →L[ℂ] K) (f (bilateralBoundaryPair G ω)) := by
  have he' := (bilateralBoundaryPair_measurePreserving G).quasiMeasurePreserving.ae
    (ae_all_iff.mpr he)
  filter_upwards [bilateral_boundary_function_transport hf, he'] with ω ht heω
  exact ht.trans (heω (ω 0)⁻¹)

end

end KadisonKastler

end OAI
