import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanContactProbeBridge
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceVolumeComparison

namespace OAI

/-! # The bridge at the prescribed inward contact pivot -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra Filter Set
open scoped Manifold Topology

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

/-- The bridge estimate applies to the exact dilation already used by
the three sampler chains. Agreement on nilpotent exponentials identifies
it with the action constructed in the bridge theorem. -/
theorem exists_fixed_contact_pivot_probe_bridge
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (S : H → MulAut F.N.carrier)
    (hS : ∀ h v, S h (F.ExpN (F.N.equiv v)) =
      F.ExpN (F.N.equiv (cartanIdealWeightDilation T H h v)))
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {d : ℕ} (σ : (Fin d → ℝ) →ₗ[ℝ] cartanRootIdeal H)
    {Z : Set (Fin d → ℝ)} (hZ : IsCompact Z)
    (letter : Fin M.letterCount) (h₀ : H) (hq : 0 ≤ M.weight letter h₀)
    {c : ℝ} (hc : 0 ≤ c)
    (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale0 : ∀ n, 0 ≤ scale n) (hR0 : ∀ n, 0 ≤ R n)
    (hR : HasSubexponentialUpperBoundSeq scale R) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ ε : ℝ, 0 < ε →
        ∀ᶠ j in atTop, ∀ δ : ℝ, 0 ≤ δ → c * δ ≤ 1 →
          ∀ (n i : F.N.carrier) (x : G) (t : ℝ) (z : Fin d → ℝ),
          |t| ≤ R j * Real.exp ((1 + δ) * (M.weight letter h₀) * scale j) → z ∈ Z →
          let h := (scale j * (1 - c * δ)) • h₀
          dist (x * (F.inclusionN (coneProbeFirst (S h) n i (F.ExpN (F.N.equiv (σ z)))) *
                F.inclusionD (F.ExpD (F.D.equiv h))))
            (x * (F.inclusionN (n * S h i * F.ExpN (F.N.equiv (t • M.letter letter))) *
                F.inclusionD (F.ExpD (F.D.equiv h)))) ≤
            (C * δ + D * ε) * scale j := by
  obtain ⟨S₀, hS₀, C, D, hC, hD, hb⟩ := exists_contact_pivot_probe_bridge T M F
    hExpG realize haarN haarD dynkinN b₀ σ hZ letter h₀ hq hc scale R hs
    hscale0 hR0 hR
  obtain ⟨⟨chart, hchart⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  have hbij : Function.Bijective F.ExpN := funext hchart ▸ chart.bijective
  have heq : S₀ = S := by
    funext h
    apply MulEquiv.ext
    intro n
    obtain ⟨v, rfl⟩ := (hbij.comp F.N.equiv.bijective).surjective n
    exact (hS₀ h v).trans (hS h v).symm
  subst S₀
  exact ⟨C, D, hC, hD, hb⟩

end PolycyclicRecognition

end

end OAI
