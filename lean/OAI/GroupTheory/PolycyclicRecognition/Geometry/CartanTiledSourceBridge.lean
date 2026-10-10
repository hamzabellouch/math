import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSourceSectionCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborRateBridge
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTiledLinkedEndpoints
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialQuotientSection
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SectionProbeReparametrization
import OAI.GroupTheory.PolycyclicRecognition.Analysis.KernelHaarTransport

namespace OAI

/-! # The metric contact bridge on the actual source probability cell -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric
open Filter
open scoped Manifold Pointwise Topology

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (C : Set (H →ₗ[ℝ] ℝ))
  [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]


variable
    (ExpI : M.coneWordIdeal C → I)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (β : Fin 3 → M.ConeIdealBases C)
    (ambient : M.Bases) (t : Fin M.letterCount → ℝ) (scale : ℕ → ℝ)
    (φ : ℕ → I ≃ₜ* I) (ι : I →* F.N.carrier)
    (tiles : ℕ → ℕ) (anchor : ∀ n, Fin (tiles n) → I)
    (D : M.TiledProbeChainData T F hunimod eW C ExpI bN E β ambient t scale φ ι tiles anchor)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (πQ : F.N.carrier →* Q.carrier)
    (hι : Topology.IsClosedEmbedding ι) (hrange : range ι = (πQ.ker : Set F.N.carrier))


local notation "Y" => fun n => TiledProbeChainData.sourceCell (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
    (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
    (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (πQ := πQ) (hι := hι) (hrange := hrange) n
local notation "ψ" => fun n => TiledProbeChainData.sourceCoordinates (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
    (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
    (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (πQ := πQ) (hι := hι) (hrange := hrange) n
local notation "σ" => TiledProbeChainData.sourceSection (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
    (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
    (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (chartN := chartN)

omit [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I] in
/-- The published exponential representation yields the bridge for the
actual quotient section retained by the tiled source cell. The original
center and the independently selected sample are both preserved. -/
theorem TiledProbeChainData.exists_source_cell_bridge
    [SimplyConnectedSpace G] [IsIsometricSMul G G]
    (hExpG : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (S : H → MulAut F.N.carrier)
    (hS : ∀ h v, S h (F.ExpN (F.N.equiv v)) =
      F.ExpN (F.N.equiv (cartanIdealWeightDilation T H h v)))
    (letter : Fin M.letterCount) (h₀ : H) (hq : 0 < M.weight letter h₀)
    {c B₀ : ℝ} (hc : 0 ≤ c) (hB₀ : 0 ≤ B₀)
    (R : ℕ → ℝ) (hscale : Filter.Tendsto scale Filter.atTop Filter.atTop)
    (hscale0 : ∀ n, 0 ≤ scale n) (hR0 : ∀ n, 0 ≤ R n)
    (hR : HasSubexponentialUpperBoundSeq scale R) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∀ δ : ℝ, 0 ≤ δ → c * δ ≤ 1 →
        ∀ (u sample : F.N.carrier) (x : G) (time : ℝ) (y : Y n),
        |time| ≤ R n * Real.exp ((M.weight letter h₀ + B₀ * δ) * scale n) →
        let h := (scale n * (1 - c * δ)) • h₀
        let k := (S h).symm (F.ExpN (F.N.equiv (time • M.letter letter)))
        dist (x * F.inclusionN (sample * coneProbeSecond (S h) u (y.val.2 : F.N.carrier) k) *
            F.inclusionD (F.ExpD (F.D.equiv h)))
          (x * F.inclusionN (sample * coneProbeFirst (S h) u
            (y.val.2 : F.N.carrier) (σ y.val.1)) *
            F.inclusionD (F.ExpD (F.D.equiv h))) ≤
          (A * δ + B * ε) * scale n := by
  let σlin := (quotientLinearSection (M.coneWordIdeal C) D.bQ D.lift).comp
    D.bQ.equivFun.symm.toLinearMap
  obtain ⟨A, B, hA, hB, hb⟩ := exists_sampled_contact_bridge_at_neighbor_rate T M F
    hExpG realize haarN haarD dynkinN S hS bN σlin
    (isCompact_closedBall (0 : Fin (finrank ℝ
      (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) 1)
    letter h₀ hq hc hB₀ scale R hscale hscale0 hR0 hR
  refine ⟨A, B, hA, hB, ?_⟩
  intro ε hε
  filter_upwards [hb ε hε] with n hn
  intro δ hδ hδc u sample x time y ht
  have hz := (ψ n y).1.property
  have hp := hn δ hδ hδc u (y.val.2 : F.N.carrier) sample x time (ψ n y).1.val ht hz
  have he : σ y.val.1 = F.ExpN (F.N.equiv (σlin (ψ n y).1.val)) :=
    TiledProbeChainData.sourceSection_sourceCoordinates
      (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
      (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
      (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor)
      (D := D) (Q := Q) (chartQ := chartQ) (chartN := chartN)
      (πQ := πQ) (hι := hι) (hrange := hrange) hchartN n y
  rw [← he] at hp
  exact hp

end PolycyclicRecognition.CartanWordModel

end

end OAI
