import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPolarProbeTemplates
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SequenceConeIdealFlowTiling
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ConeIdealFlowConjugation

namespace OAI

/-! # Strict-width tiling for the actual polar probe templates -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra MeasureTheory Set Filter
open scoped Manifold Topology Pointwise BigOperators

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {d : ℕ} (T : TriangularAdjoint L d)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (K : ProperCone ℝ (StrongDual ℝ W))

local notation "C" => heightConePreimage T eW K
local notation "s" => M.polarProbeWidths T hunimod eW K

variable {EI I N A : Type*} [NormedAddCommGroup EI] [NormedSpace ℝ EI]
  [FiniteDimensional ℝ EI] [TopologicalSpace I] [ChartedSpace EI I] [Group I]
  [LieGroup (𝓘(ℝ, EI)) ⊤ I] [T2Space I] [SimplyConnectedSpace I]
  [MeasurableSpace I] [BorelSpace I] [Group N]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The source tiling has the exact three polar radii. Its reverse anchors
use the inverse of the actual conjugating automorphism, and its number of
tiles has exponent `(b-a)` times the fixed polar ideal exponent. -/
theorem exists_polar_flow_tiling
    (eI : M.coneWordIdeal C ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EI)) I)
    (ExpI : GroupLieAlgebra (𝓘(ℝ, EI)) I → I) (hExpI : IsGroupExponential ExpI)
    (chartI : GroupLieAlgebra (𝓘(ℝ, EI)) I ≃ₜ I) (hchartI : ∀ v, chartI v = ExpI v)
    (dynkinI : NilpotentDynkinExpansionInput EI I)
    (haarI : NilpotentExponentialHaarInput EI I)
    (ι : I →* N) (hι : Function.Injective ι)
    (ExpN : cartanRootIdeal H → N)
    (hcompat : ∀ v : M.coneWordIdeal C, ι (ExpI (eI v)) = ExpN v)
    (j : cartanRootIdeal H →ₗ⁅ℝ⁆ A) (ρ : N →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (ExpN x) = algebraExpUnit (j x))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (i : Fin M.letterCount) (hi : (M.weight i : H →ₗ[ℝ] ℝ) ∈ C)
    {a b c U : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) (hU : 0 < U) :
    ∃ (β : M.ConeIdealBases C) (μ : Measure I) (hbij : Function.Bijective ExpI) (R δ₀ : ℝ),
      M.IsMaximizingConeIdealBasis C bI s β ∧ μ.IsHaarMeasure ∧ 0 < R ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (scale : ℕ → ℝ), StrictMono scale → Tendsto scale atTop atTop →
      ∀ time ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) →
      (∀ᶠ n in atTop, |time n| ≤ Real.exp ((U * δ + ε n) * scale n)) →
      ∀ᶠ n in atTop,
        let φ := M.coneIdealLetterAutomorphism C eI ExpI hExpI hbij chartI hchartI dynkinI i (time n)
        ∃ (m : ℕ) (anchor : Fin m → I) (tile : Fin m → Set I),
          (∀ z, ι (φ z) = ExpN (time n • M.letter i) * ι z * (ExpN (time n • M.letter i))⁻¹) ∧
          (∀ l, anchor l ∈ M.coneIdealBox C (ExpI ∘ eI)
            ((M.supportIn T hunimod eW).weightSupport
              ((fun x : W => b • x) '' conePolarTemplate K)) β (scale n) 1) ∧
          (∀ l, φ.symm (anchor l) ∈ M.coneIdealBox C (ExpI ∘ eI)
            ((M.supportIn T hunimod eW).weightSupport
              ((fun x : W => c • x) '' conePolarTemplate K)) β (scale n) 1) ∧
          (∀ l, MeasurableSet (tile l)) ∧
          Pairwise (fun l q => Disjoint (tile l) (tile q)) ∧
          (⋃ l, tile l) = M.coneIdealBox C (ExpI ∘ eI)
            ((M.supportIn T hunimod eW).weightSupport
              ((fun x : W => b • x) '' conePolarTemplate K)) β (scale n) 1 ∧
          (∀ l, tile l ⊆ anchor l • (φ '' M.coneIdealBox C (ExpI ∘ eI)
            ((M.supportIn T hunimod eW).weightSupport
              ((fun x : W => a • x) '' conePolarTemplate K)) β (scale n) R)) ∧
          (m : ℝ) ≤ R ^ finrank ℝ (M.coneWordIdeal C) * Real.exp (scale n *
            ((b - a) * ∑ l, M.coneIdealWordCost C s (β.val l))) := by
  obtain ⟨β, hβ, _⟩ := M.exists_polar_probe_basis T hunimod eW K bI
  obtain ⟨μ, hbij, R, δ₀, hμ, hR, hδ₀, htiles⟩ :=
    M.exists_strict_width_sequence_tiling_with_anchors C eI ExpI hExpI chartI hchartI
      dynkinI haarI bI s (M.polar_width_nonneg T hunimod eW K)
      (M.polar_width_pos T hunimod eW K) β hβ i
      (M.polar_width_zero T hunimod eW K i hi) ha hab hbc hU
  refine ⟨β, μ, hbij, R, δ₀, hβ, hμ, hR, hδ₀, ?_⟩
  intro δ hδ hδle scale hmono hscale time ε hε ht
  have hw (v : ℝ) (hv : 0 ≤ v) :
      (M.supportIn T hunimod eW).weightSupport
        ((fun x : W => v • x) '' conePolarTemplate K) = fun i => v * s i := by
    funext l
    exact M.weightSupport_polar_smul T hunimod eW K hv l
  have hexp : columnBasisWeight
      (fun w : M.coneIdealWordList C => M.coneIdealWordCost C (fun l => b * s l) w) β.val -
      columnBasisWeight
      (fun w : M.coneIdealWordList C => M.coneIdealWordCost C (fun l => a * s l) w) β.val =
      (b - a) * ∑ l, M.coneIdealWordCost C s (β.val l) := by
    simp only [columnBasisWeight, M.coneIdealWordCost_smul, ← Finset.mul_sum, sub_mul]
  filter_upwards [htiles δ hδ hδle scale hmono hscale time ε hε ht] with n hn
  dsimp only
  obtain ⟨m, anchor, tile, han, hrev, hm, hd, hu, hsmall, hcount⟩ := hn
  refine ⟨m, anchor, tile, ?_, ?_, ?_, hm, hd, ?_, ?_, ?_⟩
  · exact M.coneIdealLetterAutomorphism_conjugation C eI ExpI hExpI hbij chartI hchartI
      dynkinI ι ExpN hcompat j ρ hρ hmatch i (time n)
  · simpa only [hw b (ha.trans hab.le)] using han
  · intro l
    rw [hw c (ha.trans (hab.le.trans hbc.le))]
    rw [← M.coneIdealLetterAutomorphism_neg_apply C eI ExpI hExpI hbij chartI hchartI
      dynkinI ι ExpN hcompat j ρ hρ hmatch hι]
    exact hrev l
  · simpa only [hw b (ha.trans hab.le)] using hu
  · simpa only [hw a ha] using hsmall
  · simpa only [hexp] using hcount

end PolycyclicRecognition.CartanWordModel

end

end OAI
