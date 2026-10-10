import OAI.Analysis.IrrationalRotation.Sampling.CircleDigitDensity
import OAI.Analysis.IrrationalRotation.Sampling.CircleDigitDisintegration
import OAI.Analysis.IrrationalRotation.Analysis.QuantizedDensity

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleDigitCoupling
open CouplingMarginalBounds CouplingMixture OneCoordinateCoupling

lemma endpointDensity_memLp (side : Bool) (m a b : ℝ) (l : Label) :
    MemLp (endpointDensity side m a b l) 2 baseLaw := by
  cases l with
  | none => exact memLp_const 1
  | some i => cases side <;> fin_cases i <;> exact intervalDensity_memLp _ _ 2

lemma marginalDensity_memLp (side : Bool) (κ m a b t : ℝ) :
    MemLp (marginalDensity side κ m a b t) 2 baseLaw := by
  apply (memLp_const (diagonalMass κ m a b t)).add
  exact memLp_finsetSum Finset.univ (fun i _ =>
    (endpointDensity_memLp side m a b (some i)).const_mul _)

lemma endpointDensity_integral {m a b : ℝ} (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4) (side : Bool) (l : Label) :
    (∫ x, endpointDensity side m a b l x ∂baseLaw) = 1 := by
  have := endpointLaw_isProbabilityMeasure hm ha ha' hb hb' side l
  have h := congrArg (fun ν : Measure ℝ => ν univ)
    (endpointLaw_eq_density hm ha ha' hb hb' side l)
  rw [measure_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal
      ((endpointDensity_memLp side m a b l).integrable (by norm_num))
      (Filter.Eventually.of_forall (endpointDensity_nonneg side m a b l))] at h
  have hn : 0 ≤ ∫ x, endpointDensity side m a b l x ∂baseLaw :=
    integral_nonneg (endpointDensity_nonneg side m a b l)
  exact (ENNReal.ofReal_eq_ofReal_iff hn (by norm_num)).mp (by simpa using h.symm)

lemma marginalDensity_integral {κ m a b t : ℝ} (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4) (side : Bool) :
    (∫ x, marginalDensity side κ m a b t x ∂baseLaw) = 1 := by
  have hi (i : Fin 5) : Integrable
      (fun x => componentProbabilities κ m a b t i * endpointDensity side m a b (some i) x)
      baseLaw :=
    ((endpointDensity_memLp side m a b (some i)).integrable (by norm_num)).const_mul _
  unfold marginalDensity
  rw [integral_add (integrable_const _) (integrable_finsetSum Finset.univ (fun i _ => hi i)),
    integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp only [integral_const, probReal_univ, one_smul, integral_const_mul,
    endpointDensity_integral hm ha ha' hb hb' side, mul_one]
  simp only [componentProbabilities, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, diagonalMass]
  ring

lemma marginalDensity_energy {κ m a b t : ℝ} (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) (side : Bool) :
    (∫ x, (marginalDensity side κ m a b t x - 1) ^ 2 ∂baseLaw) ≤
      50 * (κ ^ 2 / m + t / m) := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have hf (i : Fin 5) : MemLp
      (fun x => endpointDensity side m a b (some i) x - 1) 2 baseLaw :=
    (endpointDensity_memLp side m a b (some i)).sub (memLp_const 1)
  have hv (i : Fin 5) :
      (∫ x, (endpointDensity side m a b (some i) x - 1) ^ 2 ∂baseLaw) ≤
        componentVarianceBounds (2 * m) a b i := by
    cases side
    · exact leftDensity_variance_bound (by linarith) ha0 ha' hb0 hb' i
    · exact rightDensity_variance_bound (by linarith) ha0 ha' hb0 hb' i
  have hcs := integral_sq_weighted_sum_le hf (componentProbabilities κ m a b t)
  have hs : (∑ i, componentProbabilities κ m a b t i ^ 2 *
      ∫ x, (endpointDensity side m a b (some i) x - 1) ^ 2 ∂baseLaw) ≤
      ∑ i, componentProbabilities κ m a b t i ^ 2 *
        componentVarianceBounds (2 * m) a b i :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hv i) (sq_nonneg _))
  have he : (∑ i, componentProbabilities κ m a b t i ^ 2 *
      componentVarianceBounds (2 * m) a b i) = 8 * κ ^ 2 / m + 2 * t ^ 2 / m := by
    simp only [componentProbabilities, componentVarianceBounds, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    have hra := rho_sq_div_width (κ := κ) hm0 ha0
    have hrb := rho_sq_div_width (κ := κ) hm0 hb0
    have htag : (t / m) ^ 2 * (2 * m) = 2 * t ^ 2 / m := by field_simp
    rw [htag]
    simp only [div_eq_mul_inv] at hra hrb ⊢
    nlinarith
  have ht2 : t ^ 2 / m ≤ t / m :=
    div_le_div_of_nonneg_right (by nlinarith) hm0.le
  have hκ2 : 0 ≤ κ ^ 2 / m := div_nonneg (sq_nonneg _) hm0.le
  have htdiv : 0 ≤ t / m := div_nonneg ht0 hm0.le
  simp only [Fintype.card_fin] at hcs
  calc
    _ = ∫ x, (∑ i, componentProbabilities κ m a b t i *
        (endpointDensity side m a b (some i) x - 1)) ^ 2 ∂baseLaw := by
      congr 1
      funext x
      rw [marginalDensity, OneCoordinateCoupling.marginalDensity_sub_one]
    _ ≤ 5 * (∑ i, componentProbabilities κ m a b t i ^ 2 *
        componentVarianceBounds (2 * m) a b i) :=
      hcs.trans (mul_le_mul_of_nonneg_left hs (by norm_num))
    _ ≤ _ := by
      rw [he]
      simp only [div_eq_mul_inv] at ht2 hκ2 htdiv ⊢
      nlinarith

lemma rawLaw_map_endpoint {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) (side : Bool) :
    (rawLaw κ m a b t).map (endpoint side) =
      baseLaw.withDensity (fun x => ENNReal.ofReal (marginalDensity side κ m a b t x)) := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have hq0 : 0 ≤ diagonalMass κ m a b t :=
    (by norm_num : (0 : ℝ) ≤ 49 / 50).trans
      (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
  have : ∀ i, IsProbabilityMeasure (leftLaw (2 * m) a b i) :=
    leftLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  have : ∀ i, IsProbabilityMeasure (rightLaw (2 * m) a b i) :=
    rightLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  cases side
  · change (rawLaw κ m a b t).map (Prod.fst ∘ Prod.snd) = _
    rw [← Measure.map_map measurable_fst measurable_snd]
    unfold rawLaw
    rw [labelledMixture_map_snd]
    exact mixture_fst_real_density baseLaw _ _ _ _
      (leftDensity (2 * m) a b) hq0 (componentProbabilities_nonneg hκ0 hm0 ht0)
      (fun i x => (leftDensity_bound (by linarith) ha0 ha' hb0 hb' i x).1)
      (fun i => by fin_cases i <;> exact intervalDensity_measurable _ _)
      (leftLaw_eq_withDensity (by linarith) ha0 ha' hb0 hb')
  · change (rawLaw κ m a b t).map (Prod.snd ∘ Prod.snd) = _
    rw [← Measure.map_map measurable_snd measurable_snd]
    unfold rawLaw
    rw [labelledMixture_map_snd]
    exact mixture_snd_real_density baseLaw _ _ _ _
      (rightDensity (2 * m) a b) hq0 (componentProbabilities_nonneg hκ0 hm0 ht0)
      (fun i x => (rightDensity_bound (by linarith) ha0 ha' hb0 hb' i x).1)
      (fun i => by fin_cases i <;> exact intervalDensity_measurable _ _)
      (rightLaw_eq_withDensity (by linarith) ha0 ha' hb0 hb')

end Invariant233.CircleDigitCoupling

end

end OAI
