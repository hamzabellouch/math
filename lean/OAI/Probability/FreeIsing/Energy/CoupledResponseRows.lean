import OAI.Probability.FreeIsing.Energy.DiscrepancyRowEnergy
import OAI.Probability.FreeIsing.Estimates.RadialSummability
import OAI.Probability.FreeIsing.Trees.CoupledPathDrift
import OAI.Probability.FreeIsing.Trees.SubcriticalPathSums

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem367

theorem abs_tanh_weight_drift_le (h h' p p' : ℝ) :
    |(h - h') * (Real.tanh h * p ^ 2 - Real.tanh h' * p' ^ 2)| ≤
      (h - h') ^ 2 * p ^ 2 + |h - h'| * |p ^ 2 - p' ^ 2| := by
  have hdiff : |Real.tanh h - Real.tanh h'| ≤ |h - h'| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
      lipschitzWith_tanh_response.dist_le_mul h h'
  have hm : |Real.tanh h'| ≤ 1 := by
    have hsq := Real.tanh_sq_lt_one h'
    nlinarith [sq_abs (Real.tanh h'), abs_nonneg (Real.tanh h')]
  have hsplit : Real.tanh h * p ^ 2 - Real.tanh h' * p' ^ 2 =
      (Real.tanh h - Real.tanh h') * p ^ 2 +
        Real.tanh h' * (p ^ 2 - p' ^ 2) := by ring
  rw [abs_mul, hsplit]
  calc
    |h - h'| * |(Real.tanh h - Real.tanh h') * p ^ 2 +
        Real.tanh h' * (p ^ 2 - p' ^ 2)| ≤
      |h - h'| * (|(Real.tanh h - Real.tanh h') * p ^ 2| +
        |Real.tanh h' * (p ^ 2 - p' ^ 2)|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
    _ = |h - h'| * (|Real.tanh h - Real.tanh h'| * p ^ 2 +
        |Real.tanh h'| * |p ^ 2 - p' ^ 2|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg p)]
    _ ≤ |h - h'| * (|h - h'| * p ^ 2 + |p ^ 2 - p' ^ 2|) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply add_le_add (mul_le_mul_of_nonneg_right hdiff (sq_nonneg p))
      exact mul_le_of_le_one_left (abs_nonneg _) hm
    _ = _ := by rw [mul_add, ← mul_assoc, ← sq, sq_abs]

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_abs_tanh_path_drift_le
    {ι : Type*} (s : Finset ι) {theta : ℝ} (hθ : theta ^ 2 ≤ 1)
    {X Y : ι → Ω → ℝ} {H H' : Ω → ℝ}
    (hX : ∀ i ∈ s, Measurable (X i)) (hY : ∀ i ∈ s, Measurable (Y i))
    (hInt : ∀ i ∈ s, Integrable (fun ω => (X i ω - Y i ω) ^ 2) μ)
    (hH : Measurable H) (hH' : Measurable H')
    (hU : MemLp (fun ω => H ω - H' ω) 2 μ) :
    let P := fun ω => ∏ i ∈ s, responseAttenuation theta (X i ω)
    let P' := fun ω => ∏ i ∈ s, responseAttenuation theta (Y i ω)
    let Z := fun ω => ∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
      Real.log (responseAttenuation theta (Y i ω)))
    Integrable (fun ω => (H ω - H' ω) *
      (Real.tanh (H ω) * P ω ^ 2 - Real.tanh (H' ω) * P' ω ^ 2)) μ ∧
    (∫ ω, |(H ω - H' ω) *
      (Real.tanh (H ω) * P ω ^ 2 - Real.tanh (H' ω) * P' ω ^ 2)| ∂μ) ≤
      (∫ ω, (H ω - H' ω) ^ 2 * P ω ^ 2 ∂μ) +
        2 * Real.sqrt (2 * ∫ ω, (H ω - H' ω) ^ 2 ∂μ) *
          Real.sqrt (∫ ω, (P ω ^ 2 + P' ω ^ 2) * Z ω ^ 2 ∂μ) := by
  dsimp only
  let U := fun ω => H ω - H' ω
  let P := fun ω => ∏ i ∈ s, responseAttenuation theta (X i ω)
  let P' := fun ω => ∏ i ∈ s, responseAttenuation theta (Y i ω)
  let Z := fun ω => ∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
    Real.log (responseAttenuation theta (Y i ω)))
  let D := fun ω => U ω *
    (Real.tanh (H ω) * P ω ^ 2 - Real.tanh (H' ω) * P' ω ^ 2)
  have hP : Measurable P := measurable_prod_responseAttenuation s theta hX
  have hP' : Measurable P' := measurable_prod_responseAttenuation s theta hY
  have hL := (integral_mul_prod_responseAttenuation_sq_le s hθ hX hU).1
  have hB := integral_abs_mul_prod_responseAttenuation_sq_sub_sq_le s hθ hX hY hInt hU
  have htanh := lipschitzWith_tanh_response.continuous.measurable
  have hDm : Measurable D := (hH.sub hH').mul
    (((htanh.comp hH).mul (hP.pow_const 2)).sub
      ((htanh.comp hH').mul (hP'.pow_const 2)))
  have hpoint (ω : Ω) : |D ω| ≤ U ω ^ 2 * P ω ^ 2 +
      |U ω| * |P ω ^ 2 - P' ω ^ 2| :=
    abs_tanh_weight_drift_le (H ω) (H' ω) (P ω) (P' ω)
  have hD : Integrable D μ := by
    apply (hL.add hB.1).mono' hDm.aestronglyMeasurable
    filter_upwards [] with ω
    exact (show ‖D ω‖ ≤ _ by simpa only [Real.norm_eq_abs, Pi.add_apply, U, P, P'] using hpoint ω)
  refine ⟨hD, ?_⟩
  calc
    (∫ ω, |D ω| ∂μ) ≤ ∫ ω, U ω ^ 2 * P ω ^ 2 + |U ω| * |P ω ^ 2 - P' ω ^ 2| ∂μ :=
      integral_mono hD.abs (hL.add hB.1) hpoint
    _ = (∫ ω, U ω ^ 2 * P ω ^ 2 ∂μ) +
        ∫ ω, |U ω| * |P ω ^ 2 - P' ω ^ 2| ∂μ := integral_add hL hB.1
    _ ≤ _ := add_le_add le_rfl hB.2

theorem integrable_series_of_summable_integral_abs
    {ι : Type*} [Countable ι] {F : ι → Ω → ℝ}
    (hF : ∀ i, Integrable (F i) μ)
    (hs : Summable (fun i => ∫ ω, |F i ω| ∂μ)) :
    (∀ᵐ ω ∂μ, Summable (fun i => |F i ω|)) ∧
      Integrable (fun ω => ∑' i, F i ω) μ ∧
      (∫ ω, (∑' i, F i ω) ∂μ) = ∑' i, ∫ ω, F i ω ∂μ := by
  have hm (i : ι) : AEMeasurable (fun ω => ENNReal.ofReal |F i ω|) μ :=
    (hF i).abs.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hfin : (∫⁻ ω, ∑' i, ENNReal.ofReal |F i ω| ∂μ) < ∞ := by
    rw [lintegral_tsum hm]
    calc
      (∑' i, ∫⁻ ω, ENNReal.ofReal |F i ω| ∂μ) =
          ∑' i, ENNReal.ofReal (∫ ω, |F i ω| ∂μ) := by
        apply tsum_congr
        intro i
        exact (ofReal_integral_eq_lintegral_ofReal (hF i).abs
          (Filter.Eventually.of_forall (fun ω => abs_nonneg (F i ω)))).symm
      _ < ∞ := hs.tsum_ofReal_lt_top
  have hAe : ∀ᵐ ω ∂μ, Summable (fun i => |F i ω|) := by
    filter_upwards [ae_lt_top' (AEMeasurable.tsum hm) hfin.ne] with ω hω
    simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using
      ENNReal.summable_toReal hω.ne
  have hIabs : Integrable (fun ω => ∑' i, |F i ω|) μ := by
    have h := integrable_toReal_of_lintegral_ne_top (AEMeasurable.tsum hm) hfin.ne
    simpa only [ENNReal.tsum_toReal_eq (fun i => ENNReal.ofReal_ne_top),
      ENNReal.toReal_ofReal (abs_nonneg _)] using h
  refine ⟨hAe, ?_, ?_⟩
  · apply hIabs.mono' (AEStronglyMeasurable.tsum (fun i => (hF i).aestronglyMeasurable))
    filter_upwards [hAe] with ω hω
    simpa only [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (show Summable (fun i => ‖F i ω‖) by
        simpa only [Real.norm_eq_abs] using hω)
  · exact (integral_tsum_of_summable_integral_norm hF
      (by simpa only [Real.norm_eq_abs] using hs)).symm

theorem integral_series_le_of_abs_majorant
    {ι : Type*} [Countable ι] {F : ι → Ω → ℝ} {B : ι → ℝ}
    (hF : ∀ i, Integrable (F i) μ) (hB : Summable B)
    (hbound : ∀ i, (∫ ω, |F i ω| ∂μ) ≤ B i) :
    Integrable (fun ω => ∑' i, F i ω) μ ∧
      |∫ ω, (∑' i, F i ω) ∂μ| ≤ ∑' i, B i := by
  have hs : Summable (fun i => ∫ ω, |F i ω| ∂μ) :=
    Summable.of_nonneg_of_le (fun i => integral_nonneg (fun ω => abs_nonneg _)) hbound hB
  have hseries := integrable_series_of_summable_integral_abs hF hs
  refine ⟨hseries.2.1, ?_⟩
  rw [hseries.2.2]
  have hnorm : Summable (fun i => |∫ ω, F i ω ∂μ|) :=
    Summable.of_nonneg_of_le (fun i => abs_nonneg _)
      (fun i => abs_integral_le_integral_abs) hs
  calc
    |∑' i, ∫ ω, F i ω ∂μ| ≤ ∑' i, |∫ ω, F i ω ∂μ| := by
      simpa only [Real.norm_eq_abs] using
        norm_tsum_le_tsum_norm (show Summable (fun i => ‖∫ ω, F i ω ∂μ‖) by
          simpa only [Real.norm_eq_abs] using hnorm)
    _ ≤ ∑' i, B i := hnorm.tsum_le_tsum
      (fun i => abs_integral_le_integral_abs.trans (hbound i)) hB

theorem integral_response_row_density_le
    {ι : Type*} [Countable ι]
    {c c' : ι → Ω → ℝ} {U m m' : Ω → ℝ} {N D : ι → ℝ}
    (hnoise : ∀ i, Integrable (fun ω => (c i ω - c' i ω) ^ 2) μ)
    (hdrift : ∀ i, Integrable (fun ω => U ω *
      (m ω * (c i ω) ^ 2 - m' ω * (c' i ω) ^ 2)) μ)
    (hN : Summable N) (hD : Summable D)
    (hNb : ∀ i, (∫ ω, (c i ω - c' i ω) ^ 2 ∂μ) ≤ N i)
    (hDb : ∀ i, (∫ ω, |U ω *
      (m ω * (c i ω) ^ 2 - m' ω * (c' i ω) ^ 2)| ∂μ) ≤ D i)
    (hrows : ∀ᵐ ω ∂μ, Summable (fun i => (c i ω) ^ 2) ∧
      Summable (fun i => (c' i ω) ^ 2)) :
    Integrable (DiscrepancyEnergy.density c c' U m m') μ ∧
      (∫ ω, DiscrepancyEnergy.density c c' U m m' ω ∂μ) ≤
        (∑' i, N i) + 2 * ∑' i, D i := by
  let A := fun ω => ∑' i, (c i ω - c' i ω) ^ 2
  let B := fun ω => ∑' i, U ω * (m ω * (c i ω) ^ 2 - m' ω * (c' i ω) ^ 2)
  have hAb : ∀ i, (∫ ω, |(c i ω - c' i ω) ^ 2| ∂μ) ≤ N i := by
    simpa only [abs_sq] using hNb
  have hA := integral_series_le_of_abs_majorant hnoise hN hAb
  have hB := integral_series_le_of_abs_majorant hdrift hD hDb
  have heq : DiscrepancyEnergy.density c c' U m m' =ᵐ[μ]
      (fun ω => A ω + 2 * B ω) := by
    filter_upwards [hrows] with ω hω
    have hs : Summable (fun i => (U ω * m ω) * (c i ω) ^ 2) :=
      hω.1.mul_left (U ω * m ω)
    have hs' : Summable (fun i => (U ω * m' ω) * (c' i ω) ^ 2) :=
      hω.2.mul_left (U ω * m' ω)
    have hBω : B ω = U ω *
        (m ω * (∑' i, (c i ω) ^ 2) - m' ω * (∑' i, (c' i ω) ^ 2)) := by
      calc
        B ω = ∑' i, ((U ω * m ω) * (c i ω) ^ 2 -
            (U ω * m' ω) * (c' i ω) ^ 2) := by
          apply tsum_congr
          intro i
          ring
        _ = _ := by rw [hs.tsum_sub hs', tsum_mul_left, tsum_mul_left]; ring
    dsimp only [DiscrepancyEnergy.density, A]
    rw [hBω]
    ring
  have hint : Integrable (DiscrepancyEnergy.density c c' U m m') μ :=
    (hA.1.add (hB.1.const_mul 2)).congr heq.symm
  refine ⟨hint, ?_⟩
  rw [integral_congr_ae heq, integral_add hA.1 (hB.1.const_mul 2), integral_const_mul]
  exact add_le_add ((le_abs_self _).trans hA.2)
    (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hB.2) (by norm_num))

namespace ResponseRows

def pathProduct {ι : Type*} (theta : ℝ) (s : Finset ι) (X : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  ∏ i ∈ s, responseAttenuation theta (X i ω)

def pathLogDiff {ι : Type*} (theta : ℝ) (s : Finset ι)
    (X Y : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
    Real.log (responseAttenuation theta (Y i ω)))

def pathNoiseEnergy {ι : Type*} (μ : Measure Ω) (theta : ℝ) (s : Finset ι)
    (X Y : ι → Ω → ℝ) : ℝ :=
  ∫ ω, (pathProduct theta s X ω ^ 2 + pathProduct theta s Y ω ^ 2) *
    pathLogDiff theta s X Y ω ^ 2 ∂μ

def pathLinearEnergy {ι : Type*} (μ : Measure Ω) (theta : ℝ) (s : Finset ι)
    (X : ι → Ω → ℝ) (U : Ω → ℝ) : ℝ :=
  ∫ ω, U ω ^ 2 * pathProduct theta s X ω ^ 2 ∂μ

def coefficient {J ι : Type*} (theta : ℝ) (a : J → ℝ) (s : J → Finset ι)
    (X : J → ι → Ω → ℝ) (j : J) (ω : Ω) : ℝ :=
  a j * pathProduct theta (s j) (X j) ω

theorem integral_density_le_path_energies
    {J ι : Type*} [Countable J]
    (s : J → Finset ι) (a : J → ℝ) {theta : ℝ} (hθ : theta ^ 2 ≤ 1)
    {X Y : J → ι → Ω → ℝ} {H H' : Ω → ℝ}
    (hX : ∀ j i, i ∈ s j → Measurable (X j i))
    (hY : ∀ j i, i ∈ s j → Measurable (Y j i))
    (hInt : ∀ j i, i ∈ s j → Integrable (fun ω => (X j i ω - Y j i ω) ^ 2) μ)
    (hH : Measurable H) (hH' : Measurable H')
    (hU : MemLp (fun ω => H ω - H' ω) 2 μ)
    (hQsum : Summable (fun j => (a j) ^ 2 * pathNoiseEnergy μ theta (s j) (X j) (Y j)))
    (hLsum : Summable (fun j => (a j) ^ 2 *
      pathLinearEnergy μ theta (s j) (X j) (fun ω => H ω - H' ω)))
    (hRsum : Summable (fun j => (a j) ^ 2 *
      Real.sqrt (pathNoiseEnergy μ theta (s j) (X j) (Y j))))
    (hrows : ∀ᵐ ω ∂μ, Summable (fun j => (coefficient theta a s X j ω) ^ 2) ∧
      Summable (fun j => (coefficient theta a s Y j ω) ^ 2)) :
    Integrable (DiscrepancyEnergy.density (coefficient theta a s X)
      (coefficient theta a s Y) (fun ω => H ω - H' ω)
      (fun ω => Real.tanh (H ω)) (fun ω => Real.tanh (H' ω))) μ ∧
    (∫ ω, DiscrepancyEnergy.density (coefficient theta a s X)
      (coefficient theta a s Y) (fun ω => H ω - H' ω)
      (fun ω => Real.tanh (H ω)) (fun ω => Real.tanh (H' ω)) ω ∂μ) ≤
      (∑' j, (a j) ^ 2 * pathNoiseEnergy μ theta (s j) (X j) (Y j)) +
      2 * (∑' j, (a j) ^ 2 * pathLinearEnergy μ theta (s j) (X j) (fun ω => H ω - H' ω)) +
      4 * Real.sqrt (2 * ∫ ω, (H ω - H' ω) ^ 2 ∂μ) *
        (∑' j, (a j) ^ 2 * Real.sqrt (pathNoiseEnergy μ theta (s j) (X j) (Y j))) := by
  let U := fun ω => H ω - H' ω
  let P := fun j => pathProduct theta (s j) (X j)
  let P' := fun j => pathProduct theta (s j) (Y j)
  let Q := fun j => pathNoiseEnergy μ theta (s j) (X j) (Y j)
  let L := fun j => pathLinearEnergy μ theta (s j) (X j) U
  let V := ∫ ω, U ω ^ 2 ∂μ
  let K := 2 * Real.sqrt (2 * V)
  let F := fun j ω => U ω *
    (Real.tanh (H ω) * P j ω ^ 2 - Real.tanh (H' ω) * P' j ω ^ 2)
  have hfiniteN (j : J) := integral_prod_responseAttenuation_sub_sq_le
    (s j) hθ (hX j) (hY j) (hInt j)
  have hfiniteD (j : J) := integral_abs_tanh_path_drift_le
    (s j) hθ (hX j) (hY j) (hInt j) hH hH' hU
  have hnoiseEq (j : J) (ω : Ω) :
      (coefficient theta a s X j ω - coefficient theta a s Y j ω) ^ 2 =
        (a j) ^ 2 * (P j ω - P' j ω) ^ 2 := by
    dsimp only [coefficient, P, P']
    ring
  have hdriftEq (j : J) (ω : Ω) : U ω *
      (Real.tanh (H ω) * coefficient theta a s X j ω ^ 2 -
        Real.tanh (H' ω) * coefficient theta a s Y j ω ^ 2) =
      (a j) ^ 2 * F j ω := by
    dsimp only [coefficient, F, P, P']
    ring
  have hnoise (j : J) : Integrable (fun ω =>
      (coefficient theta a s X j ω - coefficient theta a s Y j ω) ^ 2) μ := by
    simp_rw [hnoiseEq]
    exact (hfiniteN j).2.1.const_mul _
  have hdrift (j : J) : Integrable (fun ω => U ω *
      (Real.tanh (H ω) * coefficient theta a s X j ω ^ 2 -
        Real.tanh (H' ω) * coefficient theta a s Y j ω ^ 2)) μ := by
    simp_rw [hdriftEq]
    exact (hfiniteD j).1.const_mul _
  have hNb (j : J) : (∫ ω,
      (coefficient theta a s X j ω - coefficient theta a s Y j ω) ^ 2 ∂μ) ≤
        (a j) ^ 2 * Q j := by
    simp_rw [hnoiseEq]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hfiniteN j).2.2 (sq_nonneg _)
  have hDb (j : J) : (∫ ω, |U ω *
      (Real.tanh (H ω) * coefficient theta a s X j ω ^ 2 -
        Real.tanh (H' ω) * coefficient theta a s Y j ω ^ 2)| ∂μ) ≤
        (a j) ^ 2 * (L j + K * Real.sqrt (Q j)) := by
    simp_rw [hdriftEq, abs_mul, abs_sq]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hfiniteD j).2 (sq_nonneg _)
  have hDsum : Summable (fun j => (a j) ^ 2 * (L j + K * Real.sqrt (Q j))) := by
    convert hLsum.add (hRsum.mul_left K) using 1
    funext j
    dsimp only [L, Q, U]
    ring
  have hb := integral_response_row_density_le hnoise hdrift hQsum hDsum hNb hDb hrows
  refine ⟨hb.1, hb.2.trans_eq ?_⟩
  have hsumD : (∑' j, (a j) ^ 2 * (L j + K * Real.sqrt (Q j))) =
      (∑' j, (a j) ^ 2 * L j) + K * ∑' j, (a j) ^ 2 * Real.sqrt (Q j) := by
    calc
      _ = ∑' j, ((a j) ^ 2 * L j + K * ((a j) ^ 2 * Real.sqrt (Q j))) := by
        apply tsum_congr
        intro j
        ring
      _ = _ := by rw [hLsum.tsum_add (hRsum.mul_left K), tsum_mul_left]
  rw [hsumD]
  dsimp only [K, V, Q, L, U]
  ring

end ResponseRows

end Probability

end Problem367

end

end OAI
