import OAI.Probability.SpanningForest.DenseBrownian

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal Topology

namespace Problem336.DenseBrownian

variable {Ω J : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {Y : J → Ω → ℝ} {τ : J → ℝ≥0}

lemma characteristic_of_gaussian_family [IsProbabilityMeasure P]
    (hY : IsGaussianProcess Y P) (hm : ∀ j, ∫ ω, Y j ω ∂P = 0)
    (hv : ∀ i j, cov[Y i, Y j; P] = min (τ i : ℝ) (τ j : ℝ))
    {ι : Type*} [Fintype ι] (b : ι → J) (a : ι → ℝ) :
    (∫ ω, Complex.exp ((((∑ i, a i * Y (b i) ω) : ℝ) : ℂ) * Complex.I) ∂P) =
      brownianChar a (τ ∘ b) := by
  classical
  let Z : Ω → ℝ := fun ω => ∑ i, a i * Y (b i) ω
  have hZ : HasGaussianLaw Z P := by
    simpa [Z, Function.comp_def, smul_eq_mul] using
      ((hY.comp_right b).smul a).hasGaussianLaw_fun_sum (I := Finset.univ)
  have hmean : ∫ ω, Z ω ∂P = 0 := by
    dsimp [Z]
    rw [integral_finsetSum]
    · simp [integral_const_mul, hm]
    · intro i _
      exact (hY.hasGaussianLaw_eval (b i)).integrable.const_mul (a i)
  have hmem (i : ι) : MemLp (fun ω => a i * Y (b i) ω) 2 P :=
    (hY.hasGaussianLaw_eval (b i)).memLp_two.const_mul (a i)
  have hvar : Var[Z; P] = ∑ i, ∑ j,
      a i * a j * min (τ (b i) : ℝ) (τ (b j) : ℝ) := by
    rw [← covariance_self hZ.aemeasurable]
    dsimp [Z]
    rw [covariance_fun_sum_fun_sum hmem hmem]
    simp_rw [covariance_const_mul_left, covariance_const_mul_right, hv]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hc := hZ.charFun_map_eq (1 : ℝ)
  simp only [Real.inner_apply, one_mul] at hc
  rw [hmean, hvar] at hc
  have hi : charFun (P.map Z) (1 : ℝ) =
      ∫ ω, Complex.exp (((Z ω : ℝ) : ℂ) * Complex.I) ∂P := by
    rw [charFun_apply, integral_map hZ.aemeasurable (by fun_prop)]
    simp
  rw [hi] at hc
  simpa [Z, brownianChar, Function.comp_def, neg_div] using hc

theorem isBrownian_of_dense_gaussian_modification [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → ℝ} {D : Set ℝ≥0} (hD : Dense D)
    (hX : ∀ t, Measurable (X t))
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hY : IsGaussianProcess Y P) (hm : ∀ j, ∫ ω, Y j ω ∂P = 0)
    (hv : ∀ i j, cov[Y i, Y j; P] = min (τ i : ℝ) (τ j : ℝ))
    (hmod : ∀ t ∈ D, ∃ j, τ j = t ∧ X t =ᵐ[P] Y j) :
    IsBrownianReal X P := by
  classical
  apply isBrownian_of_dense_characteristic_fin hD hX hc
  intro n a t ht
  choose b hb heq using fun i => hmod (t i) (ht i)
  have ha : ∀ᵐ ω ∂P, ∀ i, X (t i) ω = Y (b i) ω :=
    ae_all_iff.mpr heq
  have hi : evaluationChar X P a t =
      ∫ ω, Complex.exp ((((∑ i, a i * Y (b i) ω) : ℝ) : ℂ) * Complex.I) ∂P := by
    unfold evaluationChar
    apply integral_congr_ae
    filter_upwards [ha] with ω hω
    simp_rw [hω]
  rw [hi, characteristic_of_gaussian_family hY hm hv b a]
  congr 1
  funext i
  exact hb i

end Problem336.DenseBrownian

end

end OAI
