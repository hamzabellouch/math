import OAI.Combinatorics.Progressions.Lattices.WeightedModerateIntegerApproximation
import OAI.Combinatorics.Progressions.Sampling.ForecastInactiveFiberLaw

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical NNReal

theorem forecastInactive_retained_character_split
    {J : Type*} [Fintype J] {M d K : ℕ} [NeZero M] [NeZero d]
    (k : J → Fin M) (a : J → ℤ) (ξ : J → ℝ)
    (hfreq : ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / d + ξ j / K)
    (z : J → ℤ) :
    rectangularGridCharacter M k z =
      (∏ j, cyclicIntegerCharacter d (a j) (z j : ZMod d)) *
        CircleFourier.character
          ((∑ j, ξ j * ((z j : ℝ) / K) : ℝ) : CircleFourier.Circle) := by
  have hpoint (j : J) : integerGridCharacter M (k j) (z j) =
      cyclicIntegerCharacter d (a j) (z j : ZMod d) *
        CircleFourier.character ((ξ j * ((z j : ℝ) / K) : ℝ) : CircleFourier.Circle) := by
    rw [integerGridCharacter_eq, hfreq j, add_mul, AddCircle.coe_add,
      CircleFourier.character_add, cyclicIntegerCharacter_intCast]
    congr 2 <;> congr 1 <;> ring
  simp only [rectangularGridCharacter, hpoint, Finset.prod_mul_distrib,
    circle_coe_fintype_sum, CircleFourier.character_fintype_sum]

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable (degree : D → ℕ)
variable (L : PrincipalTupleIndex B (fun a => degree a + 1) → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (fun a => degree a + 1) → Option α → ZMod q) (axis : D)
variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ L ⟨axis, b, v⟩)
local notation "sources" => principalSupportedAxisSources B (fun a => degree a + 1) L hL q hq r axis hsize
local notation "law" => principalTupleWeights (α := α) B (fun a => degree a + 1) L hL
local notation "cell" => Finset.univ.filter (fun y => principalResidueLabel q y = r)

theorem exists_forecastInactive_fiber_spectrum
    [Nonempty (B axis)] {K : ℕ} [NeZero K]
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {P V C E ε : ℝ}
    (hP : 1 ≤ P) (hV : 0 ≤ V) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hprimitive : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hupper : ∀ b, (∏ v : Fin (degree axis + 1), (L ⟨axis, b, v⟩ : ℝ)) ≤ V * K)
    (hlower : ∀ b, (K : ℝ) ≤ C * ∏ v : Fin (degree axis + 1), (L ⟨axis, b, v⟩ : ℝ))
    (power : ℕ) (hpower : ∀ b v, (K : ℝ) ≤ E * (L ⟨axis, b, v⟩ : ℝ) ^ power)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree axis + 1)
    (hB : uniformSpectrumBlockCount (degree axis) rows.card (power * rows.card) ≤ Fintype.card (B axis)) :
    let R := blockTorusFactor (Fintype.card α) (degree axis + 1) (Fintype.card (B axis)) V
    let ζ := uniformBlockRetainedBias (degree axis) rows.card (power * rows.card) P
      ((R : ℝ) * C) (((R : ℝ) * E) ^ rows.card) ε
    ∃ F : Finset (rows → Fin (R * K)),
      (F.card : ℝ) ≤ uniformSpectrumSizeConstant (degree axis) rows.card (power * rows.card)
        P ((R : ℝ) * C) (((R : ℝ) * E) ^ rows.card) /
          ε ^ max (majorArcSpectrumExponent (degree axis) rows.card)
            (majorArcLengthExponent (degree axis) * (power * rows.card)) ∧
      (∑ k, ‖∏ b, weightedCubeGridCoefficient (sources b) (R * K) rows k‖) ≤
        uniformSpectrumAbsoluteCap (degree axis) rows.card (power * rows.card)
          P ((R : ℝ) * C) (((R : ℝ) * E) ^ rows.card) ∧
      (∀ k ∈ F, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ uniformCharacterDenominatorBound
          (degree axis) rows.card (power * rows.card) P
          ((R : ℝ) * C) (((R : ℝ) * E) ^ rows.card) ζ ∧
        ∃ (a : rows → ℤ) (ξ : rows → ℝ),
          (∀ t, |ξ t| ≤ 2 * majorArcCoverConstant (degree axis) rows.card P ((R : ℝ) * C) /
            ζ ^ majorArcCoverExponent (degree axis) rows.card) ∧
          ∀ t, ((k t).val : ℝ) / (R * K) = (a t : ℝ) / d + ξ t / K) ∧
      ∀ shift z : rows → ℤ,
        (∀ t, |(z t : ℝ) - shift t| ≤ blockJetScaleBound (Fintype.card α) (degree axis + 1)
          (Fintype.card (B axis)) V * K) →
        ‖(((K : ℝ) ^ rows.card * (law).fiberMean (principalResidueLabel q) r
            (fun y => if (shift + ∑ b, fun t : rows => integerBooleanBlockJet
              (fun v k => (y ⟨axis, b, v⟩ k : ℤ)) t) = z then 1 else 0) : ℝ) : ℂ) -
          ((law).mass cell : ℂ) * weightedCubeGridApproximation sources K (R * K) rows shift z F‖ ≤
          (law).mass cell * ε := by
  intro R ζ
  have hs (b : B axis) (v : Fin (degree axis + 1)) :
      ScalarCubePrimitiveBudget (sources b v) A P :=
    (principalSupportedAxisSources_primitive B (fun a => degree a + 1) L hL q hq r axis hsize b v A).mono hprimitive
  obtain ⟨F, hcard, hcap, hchar, herr⟩ := weightedCube_integer_density_approximation (K := K)
    sources A hA hP hV hC hE hε hε1 hs hupper hlower power hpower rows hrows hB
  refine ⟨F, hcard, hcap, hchar, ?_⟩
  intro shift z hz
  rw [forecastInactive_fiber_image_all B degree L hL q hq r axis hsize rows shift z]
  have herror := herr shift z hz
  have hmass := (law).mass_nonneg cell
  have heq :
      (((K : ℝ) ^ rows.card * ((law).mass cell *
        finiteImageMass (weightedCubeIntegerSource sources) (weightedCubeIntegerJetSum sources rows shift) z) : ℝ) : ℂ) -
          ((law).mass cell : ℂ) * weightedCubeGridApproximation sources K (R * K) rows shift z F =
      ((law).mass cell : ℂ) *
        ((((K : ℝ) ^ rows.card * finiteImageMass (weightedCubeIntegerSource sources)
          (weightedCubeIntegerJetSum sources rows shift) z : ℝ) : ℂ) -
            weightedCubeGridApproximation sources K (R * K) rows shift z F) := by
    push_cast
    ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hmass]
  exact mul_le_mul_of_nonneg_left herror hmass

end Erdos3

end

end OAI
