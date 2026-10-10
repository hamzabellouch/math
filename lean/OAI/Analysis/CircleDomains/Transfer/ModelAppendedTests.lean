import OAI.Analysis.CircleDomains.Transfer.ModelAppendedPairs
import OAI.Analysis.CircleDomains.Topology.CompactPriorityTest
import OAI.Analysis.CircleDomains.Topology.CompactHeightPullback

namespace OAI

/-! The finite appended list consists of actual continuous compact tests
with local Sobolev witnesses and all pair-null relations. Its ingredients
are the constructed flattenings, priority cutoffs and descended height. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem compact_appended_tests (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcoarea : PlanarSobolevCoarea)
    (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (hpairs : ∀ i j, i ≠ j → volume ((fun p =>
      (sphereFromPlaneFunction (u i) p,sphereFromPlaneFunction (u j) p)) '' Gᶜ) = 0)
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ p ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ p = 0)
    (O : Fin m → Set ℝ) (hO : ∀ i, MeasurableSet (O i))
    (WO : ∀ i, DeGiorgi.MemW1pWitness 2 (flattenValues (O i) ∘ u i) (physicalPlaneDomain G))
    (V : Set ℝ) (hV : MeasurableSet V) (A : ℝ)
    (WV : DeGiorgi.MemW1pWitness 2 (flattenValues V ∘ H.height ∘ complexPlaneCoordinates) (ball 0 A))
    (b : ℕ → ℂ) (hb : ∀ n, (b n : Sphere) ∉ G)
    (c : ℕ → ℝ) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (χ : ℕ → ℂ → ℝ) (hχ : ∀ n, ContDiff ℝ ∞ (χ n))
    (hχs : ∀ n, support (χ n) ⊆ ball (b n) (r n))
    (hOld : ∀ i n, ∃ a : ℝ, ∀ z ∈ {z : ℂ | (z : Sphere) ∉ G} ∩ support (χ n),
      flattenValues (O i) (sphereFromPlaneFunction (u i) (z : Sphere)) = a)
    (hHeight : ∀ n, ∃ a : ℝ, ∀ z ∈ {z : ℂ | (z : Sphere) ∉ G} ∩ support (χ n),
      flattenValues V (M.heightSection H (z : Sphere)) = a)
    (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η) (hsη : HasCompactSupport η)
    (hηB : ∀ z : ℂ, (z : Sphere) ∉ G → η z = 1)
    {L : ℝ} (hsL : tsupport η ⊆ ball 0 L)
    (hp : Continuous (fun z : ℂ =>
      priorityInfiniteValue (fun n => χ n z) c (M.horizontalSection (z : Sphere))))
    (he : MemLp (fun z : ℂ => fderiv ℝ
      (fun w : ℂ => priorityInfiniteValue (fun n => χ n w) c (M.horizontalSection (w : Sphere))) z -
      fderiv ℝ (fun w : ℂ => M.horizontalSection (w : Sphere)) z)
      2 (volume.restrict ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 L)))
    (θ : EuclideanPlane → ℝ) (hθ : ContDiff ℝ ∞ θ) (hsθ : HasCompactSupport θ)
    (hθA : tsupport θ ⊆ ball 0 A)
    (hθF : ∀ x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G), θ x = 1) :
    let t := appendScalarPair (fun i => flattenValues (O i) ∘ u i)
      (M.compactPrioritySource χ c η) (M.compactHeightSource H (flattenValues V) θ)
    (∀ i, Continuous (t i)) ∧ (∀ i, HasCompactSupport (t i)) ∧
      Nonempty (∀ i, DeGiorgi.MemW1pWitness 2 (t i) (physicalPlaneDomain G)) ∧
      (∀ i j, i ≠ j → volume ((fun p =>
        (sphereFromPlaneFunction (t i) p,sphereFromPlaneFunction (t j) p)) '' Gᶜ) = 0) := by
  obtain ⟨hpc, hps, _, WP⟩ := M.compact_priority_test hG hinf b hb c r hr χ hχ hχs
    η hη hsη hsL hp he
  obtain ⟨hqc, hqs, WQ⟩ := M.compact_flattened_height_pullback hsard hsch
    hG hconn hinf hTD H hHz V hV A WV θ hθ hsθ hθA hθF
  obtain ⟨WP⟩ := WP
  obtain ⟨WQ⟩ := WQ
  refine ⟨?_, ?_, ?_, M.compact_appended_trace_pairs hsard hsch hcoarea
    hG hconn hinf hTD hu hs hpairs H hHz O hO V hV χ c hOld hHeight η hηB θ hθF⟩
  · intro i
    refine Fin.cases hqc (fun j => ?_) i
    refine Fin.cases (hpc.comp complexPlaneCoordinates.continuous) (fun k => ?_) j
    exact (flattenValues_lipschitz (hO k)).continuous.comp (hu k)
  · intro i
    refine Fin.cases hqs (fun j => ?_) i
    refine Fin.cases (hps.comp_homeomorph complexPlaneCoordinates.toHomeomorph) (fun k => ?_) j
    exact (hs k).comp_left (flattenValues_zero (O k))
  · exact ⟨Fin.cases WQ (Fin.cases WP WO)⟩

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
