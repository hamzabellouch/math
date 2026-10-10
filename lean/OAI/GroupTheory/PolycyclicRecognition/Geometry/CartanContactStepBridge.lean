import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanOriginalStepBridge

namespace OAI

/-! # Original contact estimate without auxiliary centers -/

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
/-- The uncentered contact estimate needed by the counted polar source.
The constants precede all source sections, scales and enlargement choices. -/
theorem exists_uniform_contact_step_bridge
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
    ∀ (u step : ℕ → F.N.carrier) (time : ℕ → ℝ),
      (∀ n, |time n| ≤ R n * Real.exp ((M.weight letter h₀ + B₀ * δ) * scale n)) →
      (∀ n, F.inclusionN (step n) = Exp (time n •
        (M.letter letter : GroupLieAlgebra (𝓘(ℝ, EG)) G))) →
      ∀ᶠ n in atTop, ∀ y : Y n,
        let S := M.sourceDilation T F hbijN chartN hchartN dynkinN
          ((scale n * (1 - c * δ)) • h₀)
        let k := S.symm (step n)
        dist (F.inclusionN
            (coneProbeSecond S.toMulEquiv (u n) (y.val.2 : F.N.carrier) k) *
              Exp (((scale n * (1 - c * δ)) • h₀ : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G))
          (F.inclusionN (u n * S ((y.val.2 : F.N.carrier) * σ y.val.1)) *
              Exp (((scale n * (1 - c * δ)) • h₀ : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G)) ≤
          (A * δ + B * ε) * scale n := by
  obtain ⟨A, B, hA, hB, hb⟩ := exists_uniform_original_step_bridge
    (I := I) T M F hunimod eW C hExpG realize haarN haarD dynkinN
    hbijN chartN hchartN bN letter h₀ hq hc hB₀
  refine ⟨A, B, hA, hB, ?_⟩
  intro ExpI E β ambient t scale φ ι tiles anchor D Q chartQ πQ hι hrange
  dsimp only
  intro R hs hs0 hR0 hR ε hε δ hδ hδc u step time htime hstep
  have he := hb ExpI E β ambient t scale φ ι tiles anchor D Q chartQ πQ hι hrange
    R hs hs0 hR0 hR ε hε δ hδ hδc u step (fun _ => 1) (fun _ => 1)
    (fun n => Exp (((scale n * (1 - c * δ)) • h₀ : H) :
      GroupLieAlgebra (𝓘(ℝ, EG)) G)) time htime hstep
    (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [he] with n hn
  intro y
  have hc (e : F.N.carrier ≃ₜ* F.N.carrier) (z : F.N.carrier) :
      e.toMulEquiv z = e z := rfl
  simpa only [one_mul, coneProbeFirst, hc] using hn y

end PolycyclicRecognition.CartanWordModel

end

end OAI
