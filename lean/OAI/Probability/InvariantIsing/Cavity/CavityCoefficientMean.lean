import OAI.Probability.InvariantIsing.Cavity.CavityCoefficientError

namespace OAI

/-! Replacement of random cavity blocks in bounded replica moments.
Concentration of the blocks is combined with a uniform second-moment
bound, without requiring a deterministic uniform bound on the marks. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

def cavityCappedReplicaProduct {d k r : ℕ} (A : CavityFactorBlocks d k) (T : ℝ)
    (y : Fin r → EuclideanSpace ℝ (Fin d)) (ε : Fin r → Spin k) : ℝ :=
  ∏ i, Real.exp (min (cavityLogFactor A.1 A.2.1 A.2.2 (y i) (ε i)) T)

lemma cavityCappedReplicaProduct_nonneg {d k r : ℕ} (A : CavityFactorBlocks d k) (T : ℝ)
    (y : Fin r → EuclideanSpace ℝ (Fin d)) (ε : Fin r → Spin k) :
    0 ≤ cavityCappedReplicaProduct A T y ε :=
  Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le)

lemma cavityCappedReplicaProduct_le {d k r : ℕ} (A : CavityFactorBlocks d k) (T : ℝ)
    (y : Fin r → EuclideanSpace ℝ (Fin d)) (ε : Fin r → Spin k) :
    cavityCappedReplicaProduct A T y ε ≤ Real.exp ((r : ℝ) * T) := by
  rw [cavityCappedReplicaProduct, ← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  exact (Finset.sum_le_sum (fun _ _ => min_le_right _ _)).trans_eq (by simp)

lemma measurable_cavityCappedReplicaProduct {Ω : Type*} [MeasurableSpace Ω]
    {d k r : ℕ} (A : Ω → CavityFactorBlocks d k) (hA : Measurable A) (T : ℝ)
    (y : Ω → Fin r → EuclideanSpace ℝ (Fin d)) (hy : Measurable y)
    (ε : Ω → Fin r → Spin k) (hε : Measurable ε) :
    Measurable (fun ω => cavityCappedReplicaProduct (A ω) T (y ω) (ε ω)) := by
  unfold cavityCappedReplicaProduct
  apply Finset.measurable_prod
  intro i _
  apply Measurable.exp
  apply Measurable.min _ measurable_const
  unfold cavityLogFactor cavityQuadratic
  fun_prop

theorem cavity_capped_coefficient_mean_error {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d k r : ℕ}
    (A A' : Ω → CavityFactorBlocks d k) (hA : Measurable A) (hA' : Measurable A')
    (y : Ω → Fin r → EuclideanSpace ℝ (Fin d)) (hy : Measurable y)
    (ε : Ω → Fin r → Spin k) (hε : Measurable ε)
    (F : Ω → ℝ) (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B) (hFb : ∀ ω, |F ω| ≤ B)
    (T : ℝ) (s : Set Ω) (hs : MeasurableSet s) {δ M : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ ω ∈ s, cavityFactorSize ((A ω).1 - (A' ω).1)
      ((A ω).2.1 - (A' ω).2.1) ((A ω).2.2 - (A' ω).2.2) ≤ δ)
    (hi : Integrable (fun ω => ∑ i, (1 + ‖y ω i‖^2)) P)
    (hM : (∫ ω, ∑ i, (1 + ‖y ω i‖^2) ∂P) ≤ M) :
    |(∫ ω, cavityCappedReplicaProduct (A ω) T (y ω) (ε ω) * F ω ∂P) -
      ∫ ω, cavityCappedReplicaProduct (A' ω) T (y ω) (ε ω) * F ω ∂P| ≤
      Real.exp ((r : ℝ) * T) * B * (δ * M + 2 * P.real sᶜ) := by
  let E := Real.exp ((r : ℝ) * T)
  let W := fun ω => ∑ i, (1 + ‖y ω i‖^2)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hW ω : 0 ≤ W ω := Finset.sum_nonneg (fun _ _ => by positivity)
  have hfi (a : Ω → CavityFactorBlocks d k) (ha : Measurable a) :
      Integrable (fun ω => cavityCappedReplicaProduct (a ω) T (y ω) (ε ω) * F ω) P := by
    apply integrable_of_measurable_abs_le
      ((measurable_cavityCappedReplicaProduct a ha T y hy ε hε).mul hF)
    intro ω
    dsimp only [Pi.mul_apply]
    rw [abs_mul, abs_of_nonneg (cavityCappedReplicaProduct_nonneg _ _ _ _)]
    exact mul_le_mul (cavityCappedReplicaProduct_le _ _ _ _) (hFb ω) (abs_nonneg _) hE
  have hb ω : |(cavityCappedReplicaProduct (A ω) T (y ω) (ε ω) -
      cavityCappedReplicaProduct (A' ω) T (y ω) (ε ω)) * F ω| ≤
      E * B * δ * W ω + 2 * E * B * sᶜ.indicator (fun _ => (1 : ℝ)) ω := by
    by_cases hω : ω ∈ s
    · have hcoef := cavity_capped_replica_coefficient_error (A ω).1 (A' ω).1
        (A ω).2.1 (A' ω).2.1 (A ω).2.2 (A' ω).2.2 T (y ω) (ε ω)
      have hcoeff := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hclose ω hω) hE) (hW ω)
      change |cavityCappedReplicaProduct (A ω) T (y ω) (ε ω) -
        cavityCappedReplicaProduct (A' ω) T (y ω) (ε ω)| ≤ _ at hcoef
      rw [abs_mul]
      have hh := mul_le_mul (hcoef.trans hcoeff) (hFb ω) (abs_nonneg _) (by positivity)
      rw [indicator_of_notMem (show ω ∉ sᶜ from not_not_intro hω), mul_zero, add_zero]
      exact hh.trans_eq (by ring)
    · have ha := cavityCappedReplicaProduct_le (A ω) T (y ω) (ε ω)
      have ha' := cavityCappedReplicaProduct_le (A' ω) T (y ω) (ε ω)
      have hdiff := abs_sub_le (cavityCappedReplicaProduct (A ω) T (y ω) (ε ω))
        (0 : ℝ) (cavityCappedReplicaProduct (A' ω) T (y ω) (ε ω))
      rw [sub_zero, zero_sub, abs_neg,
        abs_of_nonneg (cavityCappedReplicaProduct_nonneg _ _ _ _),
        abs_of_nonneg (cavityCappedReplicaProduct_nonneg _ _ _ _)] at hdiff
      have hh : |cavityCappedReplicaProduct (A ω) T (y ω) (ε ω) -
          cavityCappedReplicaProduct (A' ω) T (y ω) (ε ω)| ≤ 2 * E := by
        change _ ≤ E at ha ha'
        linarith
      rw [abs_mul, indicator_of_mem (show ω ∈ sᶜ from hω), mul_one]
      exact (mul_le_mul hh (hFb ω) (abs_nonneg _) (by positivity)).trans
        (le_add_of_nonneg_left (by positivity))
  rw [← integral_sub (hfi A hA) (hfi A' hA')]
  have heq : (fun ω => cavityCappedReplicaProduct (A ω) T (y ω) (ε ω) * F ω -
      cavityCappedReplicaProduct (A' ω) T (y ω) (ε ω) * F ω) =
      (fun ω => (cavityCappedReplicaProduct (A ω) T (y ω) (ε ω) -
        cavityCappedReplicaProduct (A' ω) T (y ω) (ε ω)) * F ω) := by
    funext ω
    ring
  rw [heq]
  have hbi : Integrable (fun ω => E * B * δ * W ω +
      2 * E * B * sᶜ.indicator (fun _ => (1 : ℝ)) ω) P :=
    (hi.const_mul _).add (((integrable_const (1 : ℝ)).indicator hs.compl).const_mul _)
  calc
    _ ≤ ∫ ω, |(cavityCappedReplicaProduct (A ω) T (y ω) (ε ω) -
        cavityCappedReplicaProduct (A' ω) T (y ω) (ε ω)) * F ω| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, E * B * δ * W ω + 2 * E * B * sᶜ.indicator (fun _ => (1 : ℝ)) ω ∂P :=
      integral_mono_of_nonneg (ae_of_all _ (fun _ => abs_nonneg _)) hbi (ae_of_all _ hb)
    _ = E * B * δ * (∫ ω, W ω ∂P) + 2 * E * B * P.real sᶜ := by
      rw [integral_add (hi.const_mul _)
        (((integrable_const (1 : ℝ)).indicator hs.compl).const_mul _),
        integral_const_mul, integral_const_mul, integral_indicator hs.compl]
      simp only [integral_const, smul_eq_mul, mul_one, W,
        measureReal_def, Measure.restrict_apply_univ]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hM (show 0 ≤ E * B * δ by positivity)
      dsimp only [W] at *
      nlinarith

end InvariantIsing

end

end OAI
