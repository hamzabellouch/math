import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Harmonic.HarmonicOperatorEvolution
import OAI.Geometry.RCD.Coordinates.WeightedInverse

namespace OAI

/-!
# A single regularization for monotone harmonic heat Grams

The regularizer is constructed from the actual annular error and the
curvature term. Positivity is proved uniformly in the direction and pole;
it is not assumed as an additional heat-flow input.
-/

open Set Metric MeasureTheory
open scoped NNReal InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {k : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ k)
  {n : ℕ} {U : Euclidean n →L[ℝ] SobolevSpace μ hQ}
  {M : PositiveBilinearMeasure X (Euclidean n)} {κ : ℝ} {p : X} {r : ℝ} {L : ℝ≥0}
  (G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p r L v)
  {ρ C : ℝ} (χ : GoodLaplacianCutoff μ hQ p ρ C)

def harmonicHeatDerivative {t : ℝ} (ht : 0 < t) (x : X) (lambda : ℝ) :
    Euclidean n →L[ℝ] Euclidean n :=
  (2 : ℝ) • cutoffHeatMass μ hQ hk χ.weight.continuous
      (χ.hasCompactSupport μ hQ) M ht x -
    (2 * κ) • cutoffHeatGram μ hQ hk χ.weight.continuous
      (χ.hasCompactSupport μ hQ) U ht x 0 +
    harmonicHeatError μ hQ (k := k) G χ t x +
    lambda • ContinuousLinearMap.id ℝ (Euclidean n)

/-- The regularized derivative lies between twice the heat mass and
that mass plus a uniform scalar error. -/
theorem harmonicHeatDerivative_bounds (hρr : ρ < r) (hκ : 0 ≤ κ)
    {t : ℝ} (ht : 0 < t) (x : X) {η lambda : ℝ}
    (herr : ‖harmonicHeatError μ hQ (k := k) G χ t x‖ ≤ η)
    (hlambda : 2 * κ * (L : ℝ) ^ 2 + η ≤ lambda) (v : Euclidean n) :
    2 * ⟪v, cutoffHeatMass μ hQ hk χ.weight.continuous
      (χ.hasCompactSupport μ hQ) M ht x v⟫_ℝ ≤
      ⟪v, harmonicHeatDerivative μ hQ hk G χ ht x lambda v⟫_ℝ ∧
    ⟪v, harmonicHeatDerivative μ hQ hk G χ ht x lambda v⟫_ℝ ≤
      2 * ⟪v, cutoffHeatMass μ hQ hk χ.weight.continuous
        (χ.hasCompactSupport μ hQ) M ht x v⟫_ℝ + (lambda + η) * ‖v‖ ^ 2 := by
  let A := cutoffHeatGram μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ) U ht x 0
  let E := harmonicHeatError μ hQ (k := k) G χ t x
  have hχΩ : tsupport (χ.weight : X → ℝ) ⊆ ball p (2 * r) := by
    intro z hz
    have hd : dist z p ≤ 2 * ρ := χ.tsupport_subset μ hQ hz
    exact lt_of_le_of_lt hd (by linarith)
  have hA := (G v).heatGram_le μ hQ hk χ.weight χ.bounds (χ.hasCompactSupport μ hQ) hχΩ ht x
  have hApos : 0 ≤ ⟪v, A v⟫_ℝ :=
    (cutoffHeatGram_isPositive μ hQ hk _ _ U (fun z => (χ.bounds z).1) ht x le_rfl).inner_nonneg_right v
  have hE : |⟪v, E v⟫_ℝ| ≤ η * ‖v‖ ^ 2 := by
    calc
      |⟪v, E v⟫_ℝ| ≤ ‖v‖ * ‖E v‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖v‖ * (η * ‖v‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg v)
        exact (E.le_opNorm v).trans (mul_le_mul_of_nonneg_right herr (norm_nonneg v))
      _ = _ := by ring
  have hcurv := mul_le_mul_of_nonneg_left hA (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hκ)
  have hreg := mul_le_mul_of_nonneg_right hlambda (sq_nonneg ‖v‖)
  have hcurvpos := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hκ) hApos
  change ⟪v, A v⟫_ℝ ≤ _ at hA
  change 2 * κ * ⟪v, A v⟫_ℝ ≤ _ at hcurv
  simp only [harmonicHeatDerivative, add_apply, sub_apply, smul_apply,
    ContinuousLinearMap.id_apply, inner_add_right, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq]
  change _ ≤ _ - _ + ⟪v, E v⟫_ℝ + _ ∧ _ - _ + ⟪v, E v⟫_ℝ + _ ≤ _
  constructor <;> nlinarith only [hcurv, hreg, hcurvpos, (abs_le.mp hE).1, (abs_le.mp hE).2]

/-- An actual operator derivative also differentiates every quadratic value. -/
theorem harmonicHeatQuadratic_hasDerivAt (hρ : 0 < ρ) (hρr : ρ < r)
    {t : ℝ} (ht : 0 < t) (x : X) {lambda : ℝ} (hlambda : 0 ≤ lambda) (v : Euclidean n) :
    HasDerivAt (fun s => ⟪v, cutoffHeatGramAt μ hQ hk χ.weight.continuous
      (χ.hasCompactSupport μ hQ) U s x lambda v⟫_ℝ)
      ⟪v, harmonicHeatDerivative μ hQ hk G χ ht x lambda v⟫_ℝ t := by
  have h := harmonicHeatGram_hasDerivAt μ hQ hk G χ hρ hρr ht x hlambda
  have hv := h.clm_apply (hasDerivAt_const t v)
  have hi := (hasDerivAt_const t v).inner ℝ hv
  simpa only [inner_zero_left, map_zero, add_zero, harmonicHeatDerivative] using hi

include G in
/-- Uniform annular decay constructs one strictly positive regularizer
valid for every inner pole and every direction on a common time interval. -/
theorem exists_monotone_regularized_heat (hg : HasCoordinateHeatBounds μ k)
    (hρ : 0 < ρ) (hρr : ρ < r) (hκ : 0 ≤ κ)
    {D V η : ℝ} (hD : 0 < D) (hV : 0 < V) (hη : 0 < η)
    (hvol : ∀ y, ρ ≤ dist p y → dist p y ≤ 2 * ρ →
      ∀ s, 0 < s → s ≤ D → V * s ^ n ≤ μ.real (ball y s)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ lambda : ℝ, 0 < lambda ∧
      lambda = 2 * κ * (L : ℝ) ^ 2 + η ∧
      ∀ x ∈ ball p (ρ / 2), ∀ v : Euclidean n,
        MonotoneOn (fun t => ⟪v, cutoffHeatGramAt μ hQ hk χ.weight.continuous
          (χ.hasCompactSupport μ hQ) U t x lambda v⟫_ℝ) (Ioo 0 δ) := by
  obtain ⟨δ, hδ, hb⟩ := harmonicHeatError_uniformly_small μ hQ hk hg G χ hρ hD hV hvol hη
  let lambda := 2 * κ * (L : ℝ) ^ 2 + η
  have hlambda : 0 < lambda := by
    dsimp only [lambda]
    positivity
  refine ⟨δ, hδ, lambda, hlambda, rfl, ?_⟩
  intro x hx v
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo (0 : ℝ) δ)
    (f' := fun t => if ht : 0 < t then
      ⟪v, harmonicHeatDerivative μ hQ hk G χ ht x lambda v⟫_ℝ else 0)
  · intro t ht
    exact (harmonicHeatQuadratic_hasDerivAt μ hQ hk G χ hρ hρr ht.1 x hlambda.le v).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) δ := by simpa only [interior_Ioo] using ht
    simp only [dite_eq_left ht'.1]
    exact (harmonicHeatQuadratic_hasDerivAt μ hQ hk G χ hρ hρr ht'.1 x hlambda.le v).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) δ := by simpa only [interior_Ioo] using ht
    simp only [dite_eq_left ht'.1]
    have hlow := (harmonicHeatDerivative_bounds μ hQ hk G χ hρr hκ ht'.1 x
      (hb t ht'.1 ht'.2 x hx).le (le_refl lambda) v).1
    exact (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      ((cutoffHeatMass_isPositive μ hQ hk _ _ M (fun z => (χ.bounds z).1) ht'.1 x).inner_nonneg_right v)).trans hlow

include G in
/-- Inverting the actual positive heat Gram reverses its time order. -/
theorem exists_antitone_regularized_inverse (hg : HasCoordinateHeatBounds μ k)
    (hρ : 0 < ρ) (hρr : ρ < r) (hκ : 0 ≤ κ)
    {D V η : ℝ} (hD : 0 < D) (hV : 0 < V) (hη : 0 < η)
    (hvol : ∀ y, ρ ≤ dist p y → dist p y ≤ 2 * ρ →
      ∀ s, 0 < s → s ≤ D → V * s ^ n ≤ μ.real (ball y s)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ lambda : ℝ, ∃ hlambda : 0 < lambda,
      lambda = 2 * κ * (L : ℝ) ^ 2 + η ∧
      ∀ x ∈ ball p (ρ / 2), ∀ s t (hs : 0 < s) (hst : s ≤ t), t < δ →
        ((cutoffHeatGramEquiv μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ)
            U (fun z => (χ.bounds z).1) hs x hlambda).symm.toContinuousLinearMap -
         (cutoffHeatGramEquiv μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ)
            U (fun z => (χ.bounds z).1) (hs.trans_le hst) x hlambda).symm.toContinuousLinearMap).IsPositive := by
  obtain ⟨δ, hδ, lambda, hlambda, heq, hm⟩ := exists_monotone_regularized_heat μ hQ hk G χ
    hg hρ hρr hκ hD hV hη hvol
  refine ⟨δ, hδ, lambda, hlambda, heq, ?_⟩
  intro x hx s t hs hst htδ
  let P := cutoffHeatGramEquiv μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ)
    U (fun z => (χ.bounds z).1) (hs.trans_le hst) x hlambda
  let Q := cutoffHeatGramEquiv μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ)
    U (fun z => (χ.bounds z).1) hs x hlambda
  have hP : (P : Euclidean n →L[ℝ] Euclidean n).IsPositive :=
    cutoffHeatGram_isPositive μ hQ hk _ _ U (fun z => (χ.bounds z).1) (hs.trans_le hst) x hlambda.le
  have hQ' : (Q : Euclidean n →L[ℝ] Euclidean n).IsPositive :=
    cutoffHeatGram_isPositive μ hQ hk _ _ U (fun z => (χ.bounds z).1) hs x hlambda.le
  have hPQ : ((P : Euclidean n →L[ℝ] Euclidean n) - (Q : Euclidean n →L[ℝ] Euclidean n)).IsPositive := by
    apply (ContinuousLinearMap.isPositive_iff _).mpr
    refine ⟨hP.isSymmetric.sub hQ'.isSymmetric, ?_⟩
    intro v
    rw [real_inner_comm]
    simp only [sub_apply, inner_sub_right]
    apply sub_nonneg.mpr
    change ⟪v, cutoffHeatGram μ hQ hk χ.weight.continuous
      (χ.hasCompactSupport μ hQ) U hs x lambda v⟫_ℝ ≤
      ⟪v, cutoffHeatGram μ hQ hk χ.weight.continuous
      (χ.hasCompactSupport μ hQ) U (hs.trans_le hst) x lambda v⟫_ℝ
    have h := hm x hx v ⟨hs, hst.trans_lt htδ⟩ ⟨hs.trans_le hst, htδ⟩ hst
    simpa only [cutoffHeatGramAt_of_pos μ hQ hk _ _ U hs,
      cutoffHeatGramAt_of_pos μ hQ hk _ _ U (hs.trans_le hst)] using h
  exact inverse_increment_isPositive P Q hP hQ' hPQ

end RegularPointCoordinates

end

end OAI
