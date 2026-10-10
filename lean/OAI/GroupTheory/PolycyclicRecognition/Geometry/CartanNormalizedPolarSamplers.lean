import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPolarTiledSamplers
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNormalizedNeighborStep
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialRepresentationInput

namespace OAI

/-! # The original neighboring step supplies the polar tiling flow -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric Filter MeasureTheory
open scoped Manifold Pointwise Topology

variable {EG G W EI I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (K : ProperCone ℝ (StrongDual ℝ W))
  [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]
  [NormedAddCommGroup EI] [NormedSpace ℝ EI] [FiniteDimensional ℝ EI]
  [ChartedSpace EI I] [LieGroup (𝓘(ℝ, EI)) ⊤ I] [SimplyConnectedSpace I] [T2Space I]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "C" => heightConePreimage T eW K

open scoped Matrix.Norms.Operator

/-- The original neighboring amplitude gives the actual normalized tiling
flow. Its rate and conjugation identity are proved, and the quotient section
is fixed before the scale, neighboring step and tail are chosen. -/
theorem exists_normalized_polar_samplers
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (eI : M.coneWordIdeal C ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EI)) I)
    (ExpI : GroupLieAlgebra (𝓘(ℝ, EI)) I → I) (hExpI : IsGroupExponential ExpI)
    (chartI : GroupLieAlgebra (𝓘(ℝ, EI)) I ≃ₜ I) (hchartI : ∀ v, chartI v = ExpI v)
    (dynkinI : NilpotentDynkinExpansionInput EI I)
    (haarI : NilpotentExponentialHaarInput EI I)
    (ι : I →* F.N.carrier) (hι : Function.Injective ι) (hιm : Measurable ι)
    (hcompat : ∀ v : M.coneWordIdeal C,
      ι (ExpI (eI v)) = F.ExpN (F.N.equiv (v : cartanRootIdeal H)))
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (i : Fin M.letterCount) (hi : (M.weight i : H →ₗ[ℝ] ℝ) ∈ C)
    (pivot : H) (hpivot : 0 < M.weight i pivot)
    (c B ε : ℝ) (hc : 0 ≤ c) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ (β : M.ConeIdealBases C) (μI : MeasureTheory.Measure I)
      (hbij : Function.Bijective ExpI)
      (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
        ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
      (lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
        cartanRootIdeal H) (Rbox δ₀ : ℝ),
      (∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j) ∧
      M.IsMaximizingConeIdealBasis C bI (M.polarProbeWidths T hunimod eW K) β ∧
      μI.IsHaarMeasure ∧ 0 < Rbox ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (scale : ℕ → ℝ), StrictMono scale → Tendsto scale atTop atTop →
      (∀ n, 0 < scale n) →
      ∀ (radius time : ℕ → ℝ), HasSubexponentialUpperBoundSeq scale radius →
      (∀ n, |time n| ≤ radius n * Real.exp
        ((M.weight i pivot + δ * B) * scale n)) →
      ∀ (S : H → MulAut F.N.carrier),
      (∀ h v, S h (F.ExpN (F.N.equiv v)) =
        F.ExpN (F.N.equiv (cartanIdealWeightDilation T H h v))) →
      ∀ (step : ℕ → F.N.carrier),
      (∀ n, F.inclusionN (step n) = Exp (time n •
        (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))) →
      ∃ n₀ : ℕ,
        let r := fun n => scale (n + n₀)
        let h := fun n => (r n * (1 - c * δ)) • pivot
        let tn := fun n => Real.exp (-M.weight i (h n)) * time (n + n₀)
        let φ := fun n => M.coneIdealLetterAutomorphism C eI ExpI hExpI hbij chartI
          hchartI dynkinI i (tn n)
        ∃ D : M.PolarTiledSamplerData T F hunimod eW K (ExpI ∘ eI) ι bN ε β Rbox r φ,
          D.chain.bQ = bQ ∧ D.chain.lift = lift ∧
          ∀ n z, ι (φ n z) =
            (S (h n)).symm (step (n + n₀)) * ι z *
              ((S (h n)).symm (step (n + n₀)))⁻¹ := by
  obtain ⟨m, hm, ρ, j, hind, hmatch⟩ := realize ⟨a, ⟨T⟩⟩ Exp hExp
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  let jN := j.comp (cartanRootIdeal H).incl
  let ρN := ρ.comp F.inclusionN
  have hρN : Function.Injective ρN := hρ.comp F.closedN.injective
  have hN (v : cartanRootIdeal H) :
      ρN (F.ExpN (F.N.equiv v)) = algebraExpUnit (jN v) := by
    change ρ (F.inclusionN (F.ExpN (F.N.equiv v))) = algebraExpUnit (j v)
    rw [F.compatibleN, hmatch]
  let U := B + c * M.weight i pivot + 1
  have hU : 0 < U := by
    have hmul := mul_nonneg hc hpivot.le
    dsimp only [U]
    linarith
  obtain ⟨β, μI, hbij, bQ, lift, Rbox, δ₀, hlift, hβ, hμI, hRbox, hδ₀, htile⟩ :=
    M.exists_polar_tiled_samplers T F hunimod eW K hExp realize haarN dynkinN
      eI ExpI hExpI chartI hchartI dynkinI haarI ι hι hιm hcompat
      jN ρN hρN hN bN bI i hi hε hU
  refine ⟨β, μI, hbij, bQ, lift, Rbox, δ₀, hlift, hβ, hμI, hRbox, hδ₀, ?_⟩
  intro δ hδ hd scale hs hscale hs0 radius time hrad ht S hS step hstep
  obtain ⟨η, _, hη, hn⟩ := M.exists_normalized_neighbor_rate T F S hS i pivot c B δ
    scale radius time hs0 hrad step hstep ht
  let h := fun n => (scale n * (1 - c * δ)) • pivot
  let tn := fun n => Real.exp (-M.weight i (h n)) * time n
  have htn : ∀ᶠ n in atTop, |tn n| ≤ Real.exp ((U * δ + η n) * scale n) := by
    apply Eventually.of_forall
    intro n
    exact (hn n).2.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (by dsimp only [U]; nlinarith) (hs0 n).le))
  obtain ⟨n₀, D, hQ, hl⟩ := htile δ hδ hd scale hs hscale (fun n => (hs0 n).le)
    tn η hη htn
  refine ⟨n₀, D, hQ, hl, ?_⟩
  intro n z
  have hconj := M.coneIdealLetterAutomorphism_conjugation C eI ExpI hExpI hbij
    chartI hchartI dynkinI ι (F.ExpN ∘ F.N.equiv) hcompat jN ρN hρN hN
    i (tn (n + n₀)) z
  change ι (M.coneIdealLetterAutomorphism C eI ExpI hExpI hbij chartI hchartI
    dynkinI i (tn (n + n₀)) z) = _
  have he := congrArg (fun v : F.N.carrier => v * ι z * v⁻¹) (hn (n + n₀)).1
  exact hconj.trans he.symm

end PolycyclicRecognition.CartanWordModel

end

end OAI
