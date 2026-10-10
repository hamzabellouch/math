import OAI.Analysis.KadisonKastler.SmoothingHeightSequence
import OAI.Analysis.KadisonKastler.TypeIIISmoothing
import OAI.Analysis.KadisonKastler.ModulatedAlgebraGap

namespace OAI

/-! # Exact normalizers from the constructed frequency smoothing

All constants precede the Hilbert space and algebra. The previously
proved polar-path theorem is applied to the actual Poisson operators
at positive heights tending to zero.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

local instance frequencyNormalizerOrder {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance frequencyNormalizerStarOrder {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

theorem uniform_typeIII_normalizer_from_frequency_smoothing
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (hSakai : PublishedSimpleDerivationInner.{u})
    (hDistance : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H], ∀ M : VonNeumannAlgebra H,
        PublishedBlockCommutantApproximation (Algebra M) H)
    (hHardy : PublishedHardyMultiplierEvaluation.{u}) :
    ∃ δ0 K : ℝ, 0 < δ0 ∧ 0 < K ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [Nontrivial H] [TopologicalSpace.SeparableSpace H],
      ∀ (M : VonNeumannAlgebra H), TypeIIIFactor M →
      ∀ (W : ℝ → unitary (H →L[ℂ] H)), W 0 = 1 →
      (∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x)) →
      (∀ x, Continuous (fun t => star (W t : H →L[ℂ] H) x)) →
      (∀ t, PublishedMultiplicationCorrection (unitaryConjugateAlgebra (W t) M)) →
      ∀ δ : ℝ, 0 < δ → δ < δ0 →
      FrequencySmoothing (modulatedUnitaryField W) δ →
      FrequencySmoothing (modulatedUnitaryField (fun t => star (W t))) δ →
      (∀ t, kkDistance (unitaryConjugateAlgebra (W t) M) M < δ) →
      ∀ t, ∃ v : unitary (H →L[ℂ] H), Conjugates v M M ∧
        ‖(v : H →L[ℂ] H) - W t‖ ≤ K * δ := by
  obtain ⟨r0, C, hr0, hC, hnormal⟩ :=
    uniform_typeIII_normalizer_from_smoothing hSpectral hCompare hSakai hDistance
  refine ⟨min (1 / 16) (r0 / 12), 12 * C, lt_min (by norm_num) (by positivity),
    by positivity, ?_⟩
  intro H _ _ _ _ _ M hM W hW0 hW hWs hCorrection δ hδ hδ0 A B hgap t
  have hnear := infDist_modulated_sandwich_le M W hgap
  have hgapInv (s : ℝ) : kkDistance (unitaryConjugateAlgebra (star (W s)) M) M < δ := by
    rw [kkDistance_inverse_conjugate]
    exact hgap s
  have hnearInv := infDist_modulated_sandwich_le M (fun s => star (W s)) hgapInv
  have hδ16 : δ ≤ 1 / 16 := (hδ0.trans_le (min_le_left _ _)).le
  have hδ8 : δ ≤ 1 / 8 := hδ16.trans (by norm_num)
  have hRsmall : 12 * δ < r0 := by
    have h := hδ0.trans_le (min_le_right _ _)
    linarith
  let a (n : ℕ) (t : ℝ) := A.smooth t (smoothingHeight δ n) (smoothingHeight_pos hδ n)
  let c (n : ℕ) (t : ℝ) := B.smooth t (smoothingHeight δ n) (smoothingHeight_pos hδ n)
  let D (n : ℕ) (t : ℝ) := poissonBoundaryApprox W hW t (smoothingHeight δ n)
  have hF (x : H) : AEStronglyMeasurable (fun t => modulatedUnitaryField W t x) volume :=
    (modulatedUnitaryField_continuous W hW x).aestronglyMeasurable
  have hG (x : H) : AEStronglyMeasurable
      (fun t => modulatedUnitaryField (fun s => star (W s)) t x) volume :=
    (modulatedUnitaryField_continuous (fun s => star (W s)) hWs x).aestronglyMeasurable
  have hFn : ∀ᵐ s, ‖modulatedUnitaryField W s‖ ≤ 1 :=
    Filter.Eventually.of_forall (norm_modulatedUnitaryField_le_one W)
  have hGn : ∀ᵐ s, ‖modulatedUnitaryField (fun t => star (W t)) s‖ ≤ 1 :=
    Filter.Eventually.of_forall (norm_modulatedUnitaryField_le_one (fun t => star (W t)))
  have hFG : ∀ᵐ s, modulatedUnitaryField W s *
      modulatedUnitaryField (fun t => star (W t)) s = poissonCharacterField 2 s :=
    Filter.Eventually.of_forall (modulatedUnitaryField_mul_inverse W)
  have hGF : ∀ᵐ s, modulatedUnitaryField (fun t => star (W t)) s *
      modulatedUnitaryField W s = poissonCharacterField 2 s := by
    filter_upwards with s
    simpa only [star_star] using modulatedUnitaryField_mul_inverse (fun t => star (W t)) s
  have han (n : ℕ) (s : ℝ) : ‖a n s‖ ≤ 1 + 12 * δ :=
    (A.norm_smooth_le_one_add hδ.le hδ8 s _ (smoothingHeight_pos hδ n)
      (smoothingHeight_le hδ.le n)).trans (by linarith)
  have hcn (n : ℕ) (s : ℝ) : ‖c n s‖ ≤ 1 + 12 * δ :=
    (B.norm_smooth_le_one_add hδ.le hδ8 s _ (smoothingHeight_pos hδ n)
      (smoothingHeight_le hδ.le n)).trans (by linarith)
  have hac (n : ℕ) (s : ℝ) : ‖a n s * c n s - 1‖ ≤ 12 * δ :=
    A.norm_product_sub_one_le hHardy B hF hG hFn hGn hFG hδ.le hδ16 s _
      (smoothingHeight_pos hδ n) (smoothingHeight_le hδ.le n)
  have hca (n : ℕ) (s : ℝ) : ‖c n s * a n s - 1‖ ≤ 12 * δ :=
    B.norm_product_sub_one_le hHardy A hG hF hGn hFn hGF hδ.le hδ16 s _
      (smoothingHeight_pos hδ n) (smoothingHeight_le hδ.le n)
  have halg (n : ℕ) (s : ℝ) (x : H →L[ℂ] H) (hx : x ∈ unitBall M) :
      Metric.infDist (a n s * x * c n s) (M : Set (H →L[ℂ] H)) ≤ 12 * δ := by
    have h := A.infDist_smooth_sandwich_le hHardy M (hDistance H M.commutant) B
      hFn hGn hδ.le le_rfl hδ.le hδ16 x (Filter.Eventually.of_forall fun s => hnear s x hx.1)
      s _ (smoothingHeight_pos hδ n) (smoothingHeight_le hδ.le n)
    exact h.trans ((mul_le_mul_of_nonneg_left hx.2 (by positivity)).trans_eq (mul_one _))
  have hcalg (n : ℕ) (s : ℝ) (x : H →L[ℂ] H) (hx : x ∈ unitBall M) :
      Metric.infDist (c n s * x * a n s) (M : Set (H →L[ℂ] H)) ≤ 12 * δ := by
    have h := B.infDist_smooth_sandwich_le hHardy M (hDistance H M.commutant) A
      hGn hFn hδ.le le_rfl hδ.le hδ16 x (Filter.Eventually.of_forall fun s => by simpa only [star_star] using hnearInv s x hx.1)
      s _ (smoothingHeight_pos hδ n) (smoothingHeight_le hδ.le n)
    exact h.trans ((mul_le_mul_of_nonneg_left hx.2 (by positivity)).trans_eq (mul_one _))
  have hDn (n : ℕ) (s : ℝ) : ‖D n s‖ ≤ 2 :=
    norm_poissonBoundaryApprox_smoothingHeight_le_two W hW hδ hδ8 n s
  have haD (n : ℕ) (s : ℝ) : ‖a n s - D n s‖ ≤ 12 * δ :=
    (A.norm_smooth_sub_boundary_le_four W hW hδ.le hδ8 s _
      (smoothingHeight_pos hδ n) (smoothingHeight_le hδ.le n)).trans (by linarith)
  obtain ⟨v, hv, hvn⟩ := hnormal H M hM W hW0 hCorrection a c D (12 * δ)
    (by positivity) hRsmall (fun n => A.continuous_smooth hδ.le _ (smoothingHeight_pos hδ n))
    han hcn hac hca halg hcalg hDn haD
    (poissonBoundaryApprox_smoothingHeight_tendsto W hW δ)
    (poissonBoundaryApprox_star_smoothingHeight_tendsto W hW hWs δ)
    (fun s => (hgap s).trans (by linarith)) t
  refine ⟨v, hv, hvn.trans_eq ?_⟩
  ring

/-- The analytic approximation and exact-normalizer construction applied
straight to the two concrete frequency-cut defects. -/
theorem uniform_typeIII_normalizer_from_frequency_defects
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (hSakai : PublishedSimpleDerivationInner.{u})
    (hDistance : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H], ∀ M : VonNeumannAlgebra H,
        PublishedBlockCommutantApproximation (Algebra M) H)
    (hHardy : PublishedHardyMultiplierEvaluation.{u})
    (hNest : PublishedRealNestDistance.{u})
    (hRealSpectral : PublishedRealSpectralCommutant.{u})
    (hDiagonal : PublishedRealDiagonalDecomposition.{u}) :
    ∃ δ0 K : ℝ, 0 < δ0 ∧ 0 < K ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [Nontrivial H] [TopologicalSpace.SeparableSpace H],
      ∀ (M : VonNeumannAlgebra H), TypeIIIFactor M →
      ∀ (W : ℝ → unitary (H →L[ℂ] H)), W 0 = 1 →
      ∀ (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x))
        (hWs : ∀ x, Continuous (fun t => star (W t : H →L[ℂ] H) x)),
      (∀ t, PublishedMultiplicationCorrection (unitaryConjugateAlgebra (W t) M)) →
      ∀ δ : ℝ, 0 < δ → δ < δ0 →
      (∀ a, ‖(1 - regularFrequencyNest a) *
        regularFieldOperator volume (modulatedUnitaryField W)
          (fun x => (modulatedUnitaryField_continuous W hW x).aestronglyMeasurable) 1
          (Filter.Eventually.of_forall (norm_modulatedUnitaryField_le_one W)) *
        regularFrequencyNest a‖ ≤ δ) →
      (∀ a, ‖(1 - regularFrequencyNest a) *
        regularFieldOperator volume (modulatedUnitaryField (fun t => star (W t)))
          (fun x => (modulatedUnitaryField_continuous (fun t => star (W t)) hWs x).aestronglyMeasurable) 1
          (Filter.Eventually.of_forall (norm_modulatedUnitaryField_le_one (fun t => star (W t)))) *
        regularFrequencyNest a‖ ≤ δ) →
      (∀ t, kkDistance (unitaryConjugateAlgebra (W t) M) M < δ) →
      ∀ t, ∃ v : unitary (H →L[ℂ] H), Conjugates v M M ∧
        ‖(v : H →L[ℂ] H) - W t‖ ≤ K * δ := by
  obtain ⟨δ0, K, hδ0, hK, hn⟩ :=
    uniform_typeIII_normalizer_from_frequency_smoothing hSpectral hCompare hSakai hDistance hHardy
  refine ⟨δ0, K, hδ0, hK, ?_⟩
  intro H _ _ _ _ _ M hM W hW0 hW hWs hCorrection δ hδ hsmall hF hG hgap
  obtain ⟨A⟩ := exists_frequencySmoothing hNest hRealSpectral hDiagonal
    (modulatedUnitaryField W)
    (fun x => (modulatedUnitaryField_continuous W hW x).aestronglyMeasurable)
    (Filter.Eventually.of_forall (norm_modulatedUnitaryField_le_one W)) hδ hF
  obtain ⟨B⟩ := exists_frequencySmoothing hNest hRealSpectral hDiagonal
    (modulatedUnitaryField (fun t => star (W t)))
    (fun x => (modulatedUnitaryField_continuous (fun t => star (W t)) hWs x).aestronglyMeasurable)
    (Filter.Eventually.of_forall (norm_modulatedUnitaryField_le_one (fun t => star (W t)))) hδ hG
  exact hn H M hM W hW0 hW hWs hCorrection δ hδ hsmall A B hgap

end

end KadisonKastler

end OAI
