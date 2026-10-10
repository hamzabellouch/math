import OAI.Geometry.RCD.Harmonic.QuadraticInteriorError
import OAI.Geometry.RCD.Harmonic.QuadraticModelValues

namespace OAI

/-! # Quantitative radial smallness in normalized harmonic coordinates -/

open Set Metric MeasureTheory
open scoped NNReal ENNReal BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- The cutoff gradient bound follows from its actual Lipschitz representative. -/
theorem GoodLaplacianCutoff.gradient_le {p : X} {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (χ : GoodLaplacianCutoff μ hQ p r C) :
    ∀ᵐ x ∂μ, localGamma μ hQ χ.sobolev χ.sobolev x ≤ (C / r) ^ 2 := by
  filter_upwards [SobolevSpace.minimalSlope_le_lipschitz μ hQ χ.sobolev χ.lipschitz χ.representative,
    localGamma_self μ hQ χ.sobolev,
    (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ χ.sobolev)] with x hx he hn
  rw [he]
  have hx' : SobolevSpace.minimalSlope μ hQ χ.sobolev x ≤ C / r := by
    simpa only [Real.coe_toNNReal _ (div_nonneg hC hr.le)] using hx
  exact (sq_le_sq₀ hn (div_nonneg hC hr.le)).mpr hx'

omit [IsFiniteMeasureOnCompacts μ] [ProperSpace X] in
private theorem gram_integral_bound {n : ℕ} {Ω : Set X} (hfin : μ Ω ≠ ∞)
    (u : Fin n → SobolevSpace μ hQ) {E : ℝ}
    (hE : ∀ i j, (∫ x in Ω, |localGamma μ hQ (u i) (u j) x - if i = j then 1 else 0| ∂μ) ≤ E) :
    (∫ x in Ω, ∑ i, ∑ j, |localGamma μ hQ (u j) (u i) x - if j = i then 1 else 0| ∂μ) ≤
      (n : ℝ) ^ 2 * E := by
  have hi (i j : Fin n) : IntegrableOn (fun x =>
      |localGamma μ hQ (u j) (u i) x - if j = i then 1 else 0|) Ω μ :=
    ((localGamma_memL1 μ hQ (u j) (u i)).integrableOn.sub (integrableOn_const hfin)).abs
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hi _ j)]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hE j i))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_two, mul_assoc] using hh

omit [IsFiniteMeasureOnCompacts μ] [ProperSpace X] in
private theorem gram_column_integral_bound {n : ℕ} {I Ω : Set X}
    (hIΩ : I ⊆ Ω) (hfin : μ Ω ≠ ∞) (u : Fin n → SobolevSpace μ hQ) {E : ℝ}
    (hE : ∀ i j, (∫ x in Ω, |localGamma μ hQ (u i) (u j) x - if i = j then 1 else 0| ∂μ) ≤ E)
    (j : Fin n) :
    (∫ x in I, ∑ i, |localGamma μ hQ (u i) (u j) x - if i = j then 1 else 0| ∂μ) ≤
      (n : ℝ) * E := by
  have hi (i : Fin n) : IntegrableOn (fun x =>
      |localGamma μ hQ (u i) (u j) x - if i = j then 1 else 0|) Ω μ :=
    ((localGamma_memL1 μ hQ (u i) (u j)).integrableOn.sub (integrableOn_const hfin)).abs
  have hmono := setIntegral_mono_set (integrable_finsetSum Finset.univ (fun i _ => hi i))
    (Filter.Eventually.of_forall fun x => Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (Filter.Eventually.of_forall hIΩ)
  apply hmono.trans
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hE i j)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh

/-- The manuscript's qualitative radial estimate, with an explicit modulus:
metric error epsilon and first-order Gram error epsilon give a squared
radial error at most a dimensional constant times epsilon*r^2*volume.
Global boundedness may be obtained by `boundedLocalVersion`; it preserves
all local quantities in this statement. -/
theorem normalized_coordinate_radial_error {n : ℕ} {p : X} {r ε Cχ Q : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hCχ : 0 ≤ Cχ) (hQb : 0 ≤ Q)
    (u : Fin n → SobolevSpace μ hQ) (v : X → Euclidean n)
    (hfirst : FirstOrderSplittingOn μ hQ p (4 * r) ε u v)
    (hv : v p = 0)
    (hmetric : IsPointedApproximation p 0 r 4 ε (fun x => r⁻¹ • v x))
    (hub : ∀ j, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (u j) x| ≤ 5 * r)
    (q : SobolevSpace μ hQ)
    (hq : SobolevSpace.toLp μ hQ q =ᵐ[μ.restrict (ball p (4 * r))] fun x => dist p x ^ 2 / 2)
    (hqbound : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ q x| ≤ Q)
    (heik : ∀ᵐ x ∂μ.restrict (ball p (4 * r)), localGamma μ hQ q q x = 2 * SobolevSpace.toLp μ hQ q x)
    (χ : GoodLaplacianCutoff μ hQ p r Cχ)
    (hvol : 0 < μ.real (ball p (4 * r))) (j : Fin n) :
    (∫ x in ball p r, (localGamma μ hQ q (u j) x - SobolevSpace.toLp μ hQ (u j) x) ^ 2 ∂μ) ≤
      (1000 * ((n : ℝ) + 1) ^ 2 * (Cχ + 1)) * ε * r ^ 2 * μ.real (ball p (4 * r)) := by
  let C : ℝ≥0 := ⟨5 * r, by positivity⟩
  let D : ℝ≥0 := ⟨Q + (n : ℝ) * (5 * r) ^ 2 / 2, by positivity⟩
  let V := μ.real (ball p (4 * r))
  have hfin : μ (ball p (4 * r)) ≠ ∞ := ne_of_lt
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall p (4 * r)).measure_lt_top)
  have hb : ∀ j, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (u j) x| ≤ C := hub
  have hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (q - coordinateQuadratic μ hQ u C) x| ≤ D := by
    filter_upwards [hqbound, coordinateQuadratic_bound μ hQ u C hb,
      Lp.coeFn_sub (SobolevSpace.toLp μ hQ q) (SobolevSpace.toLp μ hQ (coordinateQuadratic μ hQ u C))]
      with x hq' hH hs
    change |(SobolevSpace.toLp μ hQ q - SobolevSpace.toLp μ hQ (coordinateQuadratic μ hQ u C)) x| ≤ _
    rw [hs, Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add hq' hH.2)
  have hsmall := coordinateQuadratic_metric_value_error μ hQ hr (by norm_num : (0 : ℝ) ≤ 4)
    hε u C v hb hfirst.representative hv hmetric q hq
  have hgrad : ∀ i, ∀ᵐ x ∂μ.restrict (ball p (4 * r)), localGamma μ hQ (u i) (u i) x ≤ (2 : ℝ) ^ 2 := by
    intro i
    filter_upwards [hfirst.gradient i] with x hx
    exact hx.trans (by nlinarith)
  have hsub : ball p r ⊆ ball p (4 * r) := ball_subset_ball (by linarith)
  have hsupport : tsupport (χ.weight : X → ℝ) ⊆ ball p (4 * r) := by
    intro x hx
    have hd : dist x p ≤ 2 * r := χ.tsupport_subset μ hQ hx
    change dist x p < 4 * r
    linarith
  have hbound := coordinateQuadratic_interior_radial_error μ hQ measurableSet_ball hsub hfin
    u C D (Cχ / r).toNNReal hfirst.harmonic hb χ.sobolev q χ.weight χ.lipschitz
    (χ.hasCompactSupport μ hQ)
    (fun x => by rw [abs_of_nonneg (χ.bounds x).1]; exact (χ.bounds x).2)
    (fun x => (χ.bounds x).1) hsupport χ.representative χ.one hw
    (by positivity : 0 ≤ r ^ 2 * (ε * (2 * 4 + ε) / 2)) (by norm_num : (0 : ℝ) ≤ 2)
    (div_nonneg hCχ hr.le) hsmall heik hgrad (ae_restrict_of_ae (χ.gradient_le μ hQ hr hCχ)) j
  have hgram (i k : Fin n) :
      (∫ x in ball p (4 * r), |localGamma μ hQ (u i) (u k) x - if i = k then 1 else 0| ∂μ) ≤ ε * V := by
    apply (div_le_iff₀ hvol).mp
    simpa only [div_eq_inv_mul] using hfirst.gram i k
  have hG := gram_integral_bound μ hQ hfin u hgram
  have hGj := gram_column_integral_bound μ hQ hsub hfin u hgram j
  have hbound' : (∫ x in ball p r,
      (localGamma μ hQ q (u j) x - SobolevSpace.toLp μ hQ (u j) x) ^ 2 ∂μ) ≤
      8 * (2 * (r ^ 2 * (ε * (2 * 4 + ε) / 2)) *
        (1 + (n : ℝ) * 4 + (n : ℝ) * (5 * r) * 2 * (Cχ / r)) * V +
        (5 * r) ^ 2 * ((n : ℝ) ^ 2 * (ε * V))) +
      2 * ((n : ℝ) * (5 * r) ^ 2 * 5) * ((n : ℝ) * (ε * V)) := by
    have hsum := add_le_add
      (le_refl (2 * (r ^ 2 * (ε * (2 * 4 + ε) / 2)) *
        (1 + (n : ℝ) * (2 : ℝ) ^ 2 + (n : ℝ) * (C : ℝ) * 2 * (Cχ / r)) * V))
      (mul_le_mul_of_nonneg_left hG (sq_nonneg (C : ℝ)))
    have hh := add_le_add
      (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2 * 2 ^ 2))
      (mul_le_mul_of_nonneg_left hGj
        (by positivity : 0 ≤ 2 * ((n : ℝ) * (C : ℝ) ^ 2 * ((2 : ℝ) ^ 2 + 1))))
    have hC : (C : ℝ) = 5 * r := rfl
    simp only [hC] at hbound hh
    convert hbound.trans hh using 1
    ring
  have hcancel : (n : ℝ) * (5 * r) * 2 * (Cχ / r) = 10 * n * Cχ := by
    field_simp
    ring
  rw [hcancel] at hbound'
  have hδ : r ^ 2 * (ε * (2 * 4 + ε) / 2) ≤ (9 / 2 : ℝ) * ε * r ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hε1 (by positivity : 0 ≤ ε * r ^ 2)
    nlinarith
  have hcoef : 72 + 288 * (n : ℝ) + 720 * n * Cχ + 450 * (n : ℝ) ^ 2 ≤
      1000 * ((n : ℝ) + 1) ^ 2 * (Cχ + 1) := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) hCχ, mul_nonneg hn hCχ]
  have hfactor : 0 ≤ 1 + (n : ℝ) * 4 + 10 * n * Cχ := by positivity
  have hδ' := mul_le_mul_of_nonneg_right hδ (mul_nonneg hfactor hvol.le)
  have hlast := mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ ε * r ^ 2 * V)
  have hcoarse : (∫ x in ball p r,
      (localGamma μ hQ q (u j) x - SobolevSpace.toLp μ hQ (u j) x) ^ 2 ∂μ) ≤
      (72 + 288 * (n : ℝ) + 720 * n * Cχ + 450 * (n : ℝ) ^ 2) * (ε * r ^ 2 * V) := by
    nlinarith only [hbound', hδ']
  apply hcoarse.trans
  convert hlast using 1
  ring

end RegularPointCoordinates

end

end OAI
