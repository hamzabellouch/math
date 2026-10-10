import OAI.Probability.InvariantIsing.Spectral.SpectralQuantilePaths

namespace OAI

/-! Finite linear relations pass to simultaneous overlap quantiles. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma finite_sum_square_eq {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∑ i, f i) ^ 2 = ∑ i, ∑ j, f i * f j := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

lemma integrable_finite_sum_square {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} {f : ι → Ω → ℝ}
    (hi : ∀ i j, Integrable (fun x => f i x * f j x) μ) :
    Integrable (fun x => (∑ i, f i x) ^ 2) μ := by
  simp_rw [finite_sum_square_eq]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))

lemma integral_finite_sum_square {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} {f : ι → Ω → ℝ}
    (hi : ∀ i j, Integrable (fun x => f i x * f j x) μ) :
    (∫ x, (∑ i, f i x) ^ 2 ∂μ) = ∑ i, ∑ j, ∫ x, f i x * f j x ∂μ := by
  simp_rw [finite_sum_square_eq]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  exact Finset.sum_congr rfl (fun i _ => integral_finsetSum _ (fun j _ => hi i j))

/-- Pair moments alone preserve every finite linear relation. This avoids
assuming a simultaneous vector law before it has been constructed. -/
lemma ae_sum_zero_of_pair_moments {Ω T ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace T] [Fintype ι]
    {μ : Measure Ω} {ν : Measure T} {f : ι → Ω → ℝ} {g : ι → T → ℝ}
    (hf : ∀ i j, Integrable (fun x => f i x * f j x) μ)
    (hg : ∀ i j, Integrable (fun x => g i x * g j x) ν)
    (he : ∀ i j, (∫ x, f i x * f j x ∂μ) = ∫ x, g i x * g j x ∂ν)
    (hz : ∀ᵐ x ∂ν, (∑ i, g i x) = 0) :
    ∀ᵐ x ∂μ, (∑ i, f i x) = 0 := by
  have hzero : (∫ x, (∑ i, f i x) ^ 2 ∂μ) = 0 := by
    calc
      _ = ∑ i, ∑ j, ∫ x, f i x * f j x ∂μ := integral_finite_sum_square hf
      _ = ∑ i, ∑ j, ∫ x, g i x * g j x ∂ν := by simp_rw [he]
      _ = ∫ x, (∑ i, g i x) ^ 2 ∂ν := (integral_finite_sum_square hg).symm
      _ = 0 := by
        rw [integral_congr_ae (hz.mono (fun x hx => by rw [hx, zero_pow (by decide)]))]
        exact integral_zero _ _
  have ha := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (∑ i, f i x))
    (integrable_finite_sum_square hf)).mp hzero
  filter_upwards [ha] with x hx
  exact (sq_eq_zero_iff).mp hx

lemma integral_scaled_product {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ℝ) (c d : ℝ) :
    (∫ x, (c * f x) * (d * g x) ∂μ) = c * d * ∫ x, f x * g x ∂μ := by
  have he (x : Ω) : (c * f x) * (d * g x) = (c * d) * (f x * g x) := by ring
  simp_rw [he]
  exact integral_const_mul _ _

/-- Every linear relation among nonnegative spectral combinations holds
almost everywhere for their common quantile parameter. -/
theorem spectralQuantilePath_linear_relation {m k : ℕ}
    {Q : ProbabilityMeasure (SpectralArray m)}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray m)))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), SpectralGram x)
    (q : Fin m → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : Equiv.Perm ℕ,
      (Q : Measure (SpectralArray m)).map (permuteSpectralArray e) = Q)
    (w : Fin k → Fin m → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (hs : ∀ i, ∀ᵐ x ∂(Q : Measure (SpectralArray m)),
      spectralLinearArray (w i) x 0 1 ∈ Icc (0 : ℝ) 1)
    (c : Fin k → ℝ) (hc : ∀ a, (∑ i, c i * w i a) = 0) :
    ∀ᵐ s ∂pathMeasure, (∑ i, c i * spectralQuantilePath Q (w i) (hs i) s) = 0 := by
  let f := fun i s => c i * spectralQuantilePath Q (w i) (hs i) s
  let g := fun i x => c i * spectralLinearArray (w i) x 0 1
  have hfi (i j : Fin k) : Integrable (fun s => f i s * f j s) pathMeasure := by
    refine integrable_of_measurable_abs_le (F := fun s => f i s * f j s)
      (c := |c i| * |c j|) ?_ ?_
    · exact (measurable_const.mul (spectralQuantilePath Q (w i) (hs i)).measurable).mul
        (measurable_const.mul (spectralQuantilePath Q (w j) (hs j)).measurable)
    intro s
    simp only [f, abs_mul, abs_of_nonneg ((spectralQuantilePath Q (w i) (hs i)).nonneg s),
      abs_of_nonneg ((spectralQuantilePath Q (w j) (hs j)).nonneg s)]
    exact mul_le_mul (mul_le_of_le_one_right (abs_nonneg _) ((spectralQuantilePath Q (w i) (hs i)).le_one s))
      (mul_le_of_le_one_right (abs_nonneg _) ((spectralQuantilePath Q (w j) (hs j)).le_one s))
      (mul_nonneg (abs_nonneg _) ((spectralQuantilePath Q (w j) (hs j)).nonneg s)) (abs_nonneg _)
  have hgi (i j : Fin k) : Integrable (fun x => g i x * g j x)
      (Q : Measure (SpectralArray m)) := by
    apply compact_integrable
    unfold g spectralLinearArray spectralLinearEntry
    fun_prop
  apply ae_sum_zero_of_pair_moments hfi hgi
  · intro i j
    dsimp only [f, g]
    rw [integral_scaled_product, integral_scaled_product]
    congr 1
    exact integral_of_pair_law pathMeasure (Q : Measure (SpectralArray m)) _ _ _ _
      (spectralQuantilePath Q (w i) (hs i)).measurable
      (spectralQuantilePath Q (w j) (hs j)).measurable
      (by unfold spectralLinearArray spectralLinearEntry; fun_prop)
      (by unfold spectralLinearArray spectralLinearEntry; fun_prop)
      (spectralQuantilePath_pair_law hgg hG q hq hd hE (w i) (w j) (hw i) (hw j) (hs i) (hs j))
  · exact ae_of_all _ fun x => by
      simp only [g, spectralLinearArray, spectralLinearEntry, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [← mul_assoc, ← Finset.sum_mul, hc, zero_mul, Finset.sum_const_zero]

end InvariantIsing

end

end OAI
