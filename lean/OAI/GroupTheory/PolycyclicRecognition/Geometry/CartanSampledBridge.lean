import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFixedProbeBridge
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceVolumeComparison

namespace OAI

/-! # The contact bridge in the original sampled group frame -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra Filter Set
open scoped Manifold Topology

/-- Translate both probes by the same sampled root element. -/
theorem sampled_coneProbe_dist
    {N G : Type*} [Group N] [Group G] [PseudoMetricSpace G]
    (ι : N →* G) (S : MulAut N) (u i sample q k : N) (x d : G) :
    dist (x * ι (sample * coneProbeSecond S u i k) * d)
      (x * ι (sample * coneProbeFirst S u i q) * d) =
    dist ((x * ι sample) * (ι (coneProbeFirst S u i q) * d))
      ((x * ι sample) * (ι (u * S i * S k) * d)) := by
  simp only [coneProbeSecond, map_mul, mul_assoc, dist_comm]

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

/-- The metric bridge joins the actual first and second probes after the
same root translation used in the source count. The normalized inside
letter is the inverse image of the original neighboring step. -/
theorem exists_sampled_contact_pivot_bridge
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
        ∀ (u i sample : F.N.carrier) (x : G) (t : ℝ) (z : Fin d → ℝ),
        |t| ≤ R j * Real.exp ((1 + δ) * (M.weight letter h₀) * scale j) → z ∈ Z →
        let h := (scale j * (1 - c * δ)) • h₀
        let k := (S h).symm (F.ExpN (F.N.equiv (t • M.letter letter)))
        dist (x * F.inclusionN (sample * coneProbeSecond (S h) u i k) *
            F.inclusionD (F.ExpD (F.D.equiv h)))
          (x * F.inclusionN
            (sample * coneProbeFirst (S h) u i (F.ExpN (F.N.equiv (σ z)))) *
            F.inclusionD (F.ExpD (F.D.equiv h))) ≤
          (C * δ + D * ε) * scale j := by
  obtain ⟨C, D, hC, hD, hb⟩ := exists_fixed_contact_pivot_probe_bridge T M F
    hExpG realize haarN haarD dynkinN S hS b₀ σ hZ letter h₀ hq hc scale R hs
    hscale0 hR0 hR
  refine ⟨C, D, hC, hD, ?_⟩
  intro ε hε
  filter_upwards [hb ε hε] with j hj
  intro δ hδ hδc u i sample x t z ht hz
  have he := hj δ hδ hδc u i (x * F.inclusionN sample) t z ht hz
  dsimp only at he ⊢
  rw [sampled_coneProbe_dist]
  simpa only [MulEquiv.apply_symm_apply] using he

end PolycyclicRecognition

end

end OAI
