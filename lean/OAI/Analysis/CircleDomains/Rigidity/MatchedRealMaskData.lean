import OAI.Analysis.CircleDomains.Rigidity.MatchedMaskDomain
import OAI.Analysis.CircleDomains.Rigidity.TraceBalloonRealCoordinates

namespace OAI

/-! Data of the actual scalar masks used in the axial trace argument.
All fields are constructed from the matched disks and the planar maximal input. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}
variable [Encodable D.IndexedMatchedPair]

 def realSelectedScalar (D : MatchedConformalEnds G f) (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) (φ : Sphere → ℝ) (p : ℝ × ℝ) : ℝ :=
  φ (D.selectedTarget hG hf (Complex.equivRealProdCLM.symm p : Sphere))

 def realMaskValue (D : MatchedConformalEnds G f) [Encodable D.IndexedMatchedPair] (E : D.MatchedRoundDisks)
    (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G))
    (φ : Sphere → ℝ) (L : ℝ≥0) (cutoff : ℕ → (ℝ × ℝ) → ℝ) (p : ℝ × ℝ) : ℝ :=
  infiniteTracePrimitive cutoff (E.traceInterval hG hf φ L) 0 p (D.realSelectedScalar hG hf φ p)

 def maskDomain (G : Set Sphere) (W : D.IndexedMatchedPair → Set ℂ) : Set Sphere :=
  G ∪ ⋃ j, ((↑) : ℂ → Sphere) '' W j

 structure MatchedRealMask (E : D.MatchedRoundDisks) (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) (φ : Sphere → ℝ) (L : ℝ≥0) (m : ℕ) where
  cutoff : ℕ → (ℝ × ℝ) → ℝ
  smooth : ∀ n, ContDiff ℝ 1 (cutoff n)
  unit : ∀ n p, cutoff n p ∈ Icc (0:ℝ) 1
  zero : ∀ n p, ‖Complex.equivRealProdCLM.symm p-E.traceCenter n‖ ≤
    traceBalloonInnerRatio m*traceBalloonRadius E.traceRadius m n → cutoff n p = 0
  outer : ∀ n p, traceBalloonRadius E.traceRadius m n ≤
    ‖Complex.equivRealProdCLM.symm p-E.traceCenter n‖ → cutoff n p = 1
  density : (ℝ × ℝ) → ℝ
  density_measurable : Measurable density
  density_nonneg : ∀ p, 0 ≤ density p
  density_memLp : MemLp density 2 volume
  pays : ∀ᵐ p ∂volume, ∀ n, ∑ j ∈ Finset.range n,
    volume.real (E.traceInterval hG hf φ L j)*‖fderiv ℝ (cutoff j) p‖ ≤ density p
  neighborhood : D.IndexedMatchedPair → Set ℂ
  neighborhood_open : ∀ j, IsOpen (neighborhood j)
  neighborhood_contains : ∀ j, closedBall (E.sourceCenter j) (E.sourceRadius j) ⊆ neighborhood j
  neighborhood_zero : ∀ j z, z ∈ neighborhood j → cutoff (Encodable.encode j) (Complex.equivRealProdCLM z) = 0 ∧
    φ (D.selectedTarget hG hf (z : Sphere)) ∈ E.traceInterval hG hf φ L (Encodable.encode j)
  continuous : Continuous (D.realMaskValue E hG hf φ L cutoff)
  compact : HasCompactSupport (D.realMaskValue E hG hf φ L cutoff)
  domain_open : IsOpen (maskDomain G neighborhood)
  domain_connected : IsConnected (maskDomain G neighborhood)
  domain_dust : IsTotallyDisconnected (maskDomain G neighborhood)ᶜ
  domain_removable : IsConformallyRemovable (maskDomain G neighborhood)ᶜ

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
