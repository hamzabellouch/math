import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformTiledSourceBridge
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSourceDilation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformContactBridge
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTiledLinkedEndpoints
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialQuotientSection
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SectionProbeReparametrization
import OAI.GroupTheory.PolycyclicRecognition.Analysis.KernelHaarTransport

namespace OAI

/-! # The contact estimate for the original root step and moving pivot -/

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
/-- The constants work for the original group-valued root step. The chart
need only agree eventually with the contact ray, as in concentration. -/
theorem exists_uniform_original_step_bridge
    [SimplyConnectedSpace G] [IsIsometricSMul G G]
    (hExpG : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (hbijN : Function.Bijective F.ExpN)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
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
    (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (πQ : F.N.carrier →* Q.carrier)
    (hι : Topology.IsClosedEmbedding ι) (hrange : range ι = (πQ.ker : Set F.N.carrier)),
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
    ∀ δ : ℝ, 0 ≤ δ → c * δ ≤ 1 →
    ∀ (u step sample : ℕ → F.N.carrier) (x chart : ℕ → G) (time : ℕ → ℝ),
      (∀ n, |time n| ≤ R n * Real.exp ((M.weight letter h₀ + B₀ * δ) * scale n)) →
      (∀ n, F.inclusionN (step n) = Exp (time n •
        (M.letter letter : GroupLieAlgebra (𝓘(ℝ, EG)) G))) →
      (∀ᶠ n in atTop, chart n = Exp
        (((scale n * (1 - c * δ)) • h₀ : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G)) →
      ∀ᶠ n in atTop, ∀ y : Y n,
        let S := M.sourceDilation T F hbijN chartN hchartN dynkinN
          ((scale n * (1 - c * δ)) • h₀)
        let k := S.symm (step n)
        dist (x n * F.inclusionN (sample n *
            coneProbeSecond S.toMulEquiv (u n) (y.val.2 : F.N.carrier) k) * chart n)
          (x n * F.inclusionN (sample n *
            coneProbeFirst S.toMulEquiv (u n) (y.val.2 : F.N.carrier) (σ y.val.1)) * chart n) ≤
          (A * δ + B * ε) * scale n := by
  let S := fun h => (M.sourceDilation T F hbijN chartN hchartN dynkinN h).toMulEquiv
  obtain ⟨A, B, hA, hB, hb⟩ := exists_uniform_tiled_source_bridge
    (EG := EG) (G := G) (W := W) (I := I)
    T M F hunimod eW C hExpG realize haarN haarD dynkinN bN S
    (M.sourceDilation_apply_exp T F hbijN chartN hchartN dynkinN) letter h₀ hq hc hB₀
  refine ⟨A, B, hA, hB, ?_⟩
  intro ExpI E β ambient t scale φ ι tiles anchor D Q chartQ πQ hι hrange
  dsimp only
  intro R hs hs0 hR0 hR ε hε δ hδ hδc u step sample x chart time htime hstep hchart
  have he := hb ExpI E β ambient t scale φ ι tiles anchor D Q chartN chartQ
    πQ hι hrange hchartN R hs hs0 hR0 hR ε hε
  filter_upwards [he, hchart] with n hn hcn
  intro y
  have hroot : F.ExpN (F.N.equiv (time n • M.letter letter)) = step n :=
    (F.closedN.injective ((hstep n).trans (F.compatibleN (time n • M.letter letter)).symm)).symm
  have hpoint : chart n = F.inclusionD
      (F.ExpD (F.D.equiv ((scale n * (1 - c * δ)) • h₀))) :=
    hcn.trans (F.compatibleD _).symm
  have hbound := hn δ hδ hδc (u n) (sample n) (x n) (time n) y (htime n)
  dsimp only at hbound ⊢
  rw [hroot, ← hpoint] at hbound
  exact hbound

end PolycyclicRecognition.CartanWordModel

end

end OAI
