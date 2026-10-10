import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSourceSectionCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformContactBridge
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTiledLinkedEndpoints
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialQuotientSection
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SectionProbeReparametrization
import OAI.GroupTheory.PolycyclicRecognition.Analysis.KernelHaarTransport

namespace OAI

/-! # Uniform contact constants for every actual tiled source cell -/

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


omit [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I] in
/-- The metric constants are fixed before the scale, radius, quotient section,
and counted source partition. Every such actual source cell satisfies the
same neighboring-letter bridge estimate. -/
theorem exists_uniform_tiled_source_bridge
    [SimplyConnectedSpace G] [IsIsometricSMul G G]
    (hExpG : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (S : H → MulAut F.N.carrier)
    (hS : ∀ h v, S h (F.ExpN (F.N.equiv v)) =
      F.ExpN (F.N.equiv (cartanIdealWeightDilation T H h v)))
    (letter : Fin M.letterCount) (h₀ : H) (hq : 0 < M.weight letter h₀)
    {c B₀ : ℝ} (hc : 0 ≤ c) (hB₀ : 0 ≤ B₀) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀
    (ExpI : M.coneWordIdeal C → I)
    (E : Fin 3 → Set W) (β : Fin 3 → M.ConeIdealBases C)
    (ambient : M.Bases) (t : Fin M.letterCount → ℝ) (scale : ℕ → ℝ)
    (φ : ℕ → I ≃ₜ* I) (ι : I →* F.N.carrier)
    (tiles : ℕ → ℕ) (anchor : ∀ n, Fin (tiles n) → I)
    (D : M.TiledProbeChainData T F hunimod eW C ExpI bN E β ambient t scale φ ι tiles anchor)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (πQ : F.N.carrier →* Q.carrier)
    (hι : Topology.IsClosedEmbedding ι) (hrange : range ι = (πQ.ker : Set F.N.carrier)),
    (∀ v, chartN v = F.ExpN v) →
    let Y := fun n => TiledProbeChainData.sourceCell (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
      (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
      (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor)
      (D := D) (Q := Q) (chartQ := chartQ)
      (πQ := πQ) (hι := hι) (hrange := hrange) n
    let σ := TiledProbeChainData.sourceSection (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
      (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
      (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor)
      (D := D) (Q := Q) (chartQ := chartQ) (chartN := chartN)
    ∀ (R : ℕ → ℝ), Tendsto scale atTop atTop →
      (∀ n, 0 ≤ scale n) → (∀ n, 0 ≤ R n) →
      HasSubexponentialUpperBoundSeq scale R →
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ δ : ℝ, 0 ≤ δ → c * δ ≤ 1 →
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
  obtain ⟨A, B, hA, hB, hb⟩ := exists_uniform_sampled_contact_bridge T M F
    hExpG realize haarN haarD dynkinN S hS bN letter h₀ hq hc hB₀
  refine ⟨A, B, hA, hB, ?_⟩
  intro ExpI E β ambient t scale φ ι tiles anchor D Q chartN chartQ πQ hι hrange hchartN
  dsimp only
  intro R hs hs0 hR0 hR ε hε
  let τ := (quotientLinearSection (M.coneWordIdeal C) D.bQ D.lift).comp
    D.bQ.equivFun.symm.toLinearMap
  let ψ := fun n => TiledProbeChainData.sourceCoordinates (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
      (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
      (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor)
      (D := D) (Q := Q) (chartQ := chartQ)
      (πQ := πQ) (hι := hι) (hrange := hrange) n
  filter_upwards [hb τ (isCompact_closedBall (0 : Fin (finrank ℝ
    (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) 1)
    scale R hs hs0 hR0 hR ε hε] with n hn
  intro δ hδ hδc u sample x time y ht
  have hp := hn δ hδ hδc u (y.val.2 : F.N.carrier) sample x time
    (ψ n y).1.val ht (ψ n y).1.property
  have he := TiledProbeChainData.sourceSection_sourceCoordinates
    (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
      (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
      (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor)
      (D := D) (Q := Q) (chartQ := chartQ) (chartN := chartN)
    (πQ := πQ) (hι := hι) (hrange := hrange) hchartN n y
  change TiledProbeChainData.sourceSection (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
      (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
      (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor)
      (D := D) (Q := Q) (chartQ := chartQ) (chartN := chartN) y.val.1 =
    F.ExpN (F.N.equiv (τ (ψ n y).1.val)) at he
  rw [← he] at hp
  exact hp

end PolycyclicRecognition.CartanWordModel

end

end OAI
