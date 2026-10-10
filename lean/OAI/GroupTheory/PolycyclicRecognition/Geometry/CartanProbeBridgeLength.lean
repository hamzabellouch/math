import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNLogMetric
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPivotCoordinateBound
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProbePivotBridge
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceLogMetric
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorCharts

namespace OAI

/-! # Metric length of the actual source probe bridge

Conjugation by the pivot cancels the exact height dilation. The remaining
residual action contributes one subexponential factor, and logarithmic
distortion then retains precisely the small exponential rate.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra Filter
open scoped Manifold Topology

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

/-- Basis-specific form, so the actual compact section and generator may
be estimated after choosing a logarithmic metric bound. -/
theorem source_probe_bridge_bound_in_basis
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (β : M.Bases) {D : ℝ} (hD : 0 ≤ D)
    (hd : ∀ v : cartanRootIdeal H,
      dist 1 (F.inclusionN (F.ExpN (F.N.equiv v))) ≤
        D * Real.log (2 + ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun v‖))
    (scale RH R : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale0 : ∀ n, 0 ≤ scale n) (hRH0 : ∀ n, 0 ≤ RH n) (hR0 : ∀ n, 0 ≤ R n)
    (hRH : HasSubexponentialUpperBoundSeq scale RH)
    (hR : HasSubexponentialUpperBoundSeq scale R) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ δ : ℝ, 0 ≤ δ →
      ∀ (h : H) (S : MulAut F.N.carrier) (n i s k : F.N.carrier) (x : G)
        (v : cartanRootIdeal H),
      ‖(finBasis ℝ H).equivFun h‖ ≤ RH j →
      (∀ z, S (F.ExpN (F.N.equiv z)) =
        F.ExpN (F.N.equiv (cartanIdealWeightDilation T H h z))) →
      s⁻¹ * k = F.ExpN (F.N.equiv v) →
      ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun v‖ ≤
        R j * Real.exp (δ * scale j) →
      dist (x * (F.inclusionN (coneProbeFirst S n i s) * F.inclusionD (F.ExpD (F.D.equiv h))))
        (x * (F.inclusionN (coneProbeSecond S n i k) * F.inclusionD (F.ExpD (F.D.equiv h)))) ≤
          D * (δ + ε) * scale j := by
  obtain ⟨R', hR'0, hR', hp⟩ := M.exists_sequence_pivot_coordinate_bound T β
    scale RH R hs hRH0 hR0 hRH hR
  let E : cartanRootIdeal H → G := fun v => F.inclusionN (F.ExpN (F.N.equiv v))
  let size := fun v : cartanRootIdeal H =>
    ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun v‖
  have hm := metric_bound_of_sequence_exponential_coordinates E size (fun v => norm_nonneg _)
    hD hd scale R' hs hscale0 hR'0 hR'
  intro ε hε
  filter_upwards [hm ε hε] with j hj
  intro δ hδ h S n i s k x v hh hS hv hvbound
  rw [probe_pivot_bridge_distance F.action F.inclusionN F.inclusionD F.conjugation, hv, hS]
  have hneg : (F.ExpD (F.D.equiv h))⁻¹ = F.ExpD (F.D.equiv (-h)) := by
    rw [map_neg, F.isExpD.map_neg]
  rw [hneg, cartan_action_exp_of_published_realization T M F hExpG realize haarN haarD dynkinN]
  exact hj δ hδ _ (hp j δ h v hh hvbound)

/-- One fixed basis and constant work for every probe, ideal coordinate,
basepoint and sufficiently large scale. All group maps are the actual
Cartan-factor maps. -/
theorem exists_source_probe_bridge_bound
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (scale RH R : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale0 : ∀ n, 0 ≤ scale n) (hRH0 : ∀ n, 0 ≤ RH n) (hR0 : ∀ n, 0 ≤ R n)
    (hRH : HasSubexponentialUpperBoundSeq scale RH)
    (hR : HasSubexponentialUpperBoundSeq scale R) :
    ∃ (β : M.Bases) (D : ℝ), 0 ≤ D ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j in atTop, ∀ δ : ℝ, 0 ≤ δ → ∀ (h : H) (S : MulAut F.N.carrier)
        (n i s k : F.N.carrier) (x : G) (v : cartanRootIdeal H),
        ‖(finBasis ℝ H).equivFun h‖ ≤ RH j →
        (∀ z, S (F.ExpN (F.N.equiv z)) =
          F.ExpN (F.N.equiv (cartanIdealWeightDilation T H h z))) →
        s⁻¹ * k = F.ExpN (F.N.equiv v) →
        ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun v‖ ≤
          R j * Real.exp (δ * scale j) →
        dist (x * (F.inclusionN (coneProbeFirst S n i s) * F.inclusionD (F.ExpD (F.D.equiv h))))
          (x * (F.inclusionN (coneProbeSecond S n i k) * F.inclusionD (F.ExpD (F.D.equiv h)))) ≤
            D * (δ + ε) * scale j := by
  obtain ⟨β, D, hD, hd⟩ := exists_cartan_n_log_metric_bound T M F
    hExpG realize haarN dynkinN b₀
  exact ⟨β, D, hD, source_probe_bridge_bound_in_basis T M F hExpG realize haarN haarD
    dynkinN β hD hd scale RH R hs hscale0 hRH0 hR0 hRH hR⟩

end PolycyclicRecognition

end

end OAI
