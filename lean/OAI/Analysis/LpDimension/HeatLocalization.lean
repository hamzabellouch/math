import OAI.Analysis.LpDimension.SpectralProjection

namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace
open scoped BigOperators Topology Matrix Matrix.Norms.Operator
universe u uE uV

namespace SubpolynomialLp

section GraphHeat
variable {E : Type uE} {V : Type uV} [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]

lemma graphHeat_entry_hasDerivAt (src dst : E → V) (μ d : V → ℝ)
    (ce : E → ℝ) (hμ : ∀ i, 0 < μ i) (hrel : ∀ i, μ i * (d i * d i) = 1)
    (t : ℝ) (i v : V) :
    HasDerivAt (fun s => weightedHeatKernel (laplacianMatrix src dst ce) d s i v)
      (-graphLaplacian src dst ce
        (fun j => weightedHeatKernel (laplacianMatrix src dst ce) d t j v) i / μ i) t := by
  have hh := weightedHeatKernel_entry_hasDerivAt (laplacianMatrix src dst ce) d t i v
  rw [laplacianMatrix_mulVec] at hh
  convert hh using 1
  have he : d i * d i = 1 / μ i := by
    apply (eq_div_iff (hμ i).ne').mpr
    simpa only [mul_comm] using hrel i
  rw [he]
  ring

lemma graphHeat_mass (src dst : E → V) (ce : E → ℝ) (μ d : V → ℝ)
    (hμ : ∀ i, 0 < μ i) (hrel : ∀ i, μ i * (d i * d i) = 1) (t : ℝ) (v : V) :
    ∑ i, μ i * weightedHeatKernel (laplacianMatrix src dst ce) d t i v = 1 := by
  let K := weightedHeatKernel (laplacianMatrix src dst ce) d
  let f : ℝ → ℝ := fun s => ∑ i, μ i * K s i v
  have hf (s : ℝ) : HasDerivAt f 0 s := by
    have hh := HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => (graphHeat_entry_hasDerivAt src dst μ d ce hμ hrel s i v).const_mul (μ i))
    have he : (∑ i, μ i * (-graphLaplacian src dst ce (fun j => K s j v) i / μ i)) = 0 := by
      calc
        _ = -∑ i, graphLaplacian src dst ce (fun j => K s j v) i := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i _
          field_simp [(hμ i).ne']
        _ = 0 := by rw [graphLaplacian_sum, neg_zero]
    exact he ▸ hh
  have heq := is_const_of_deriv_eq_zero (fun s => (hf s).differentiableAt)
    (fun s => (hf s).deriv) t 0
  change f t = 1
  rw [heq]
  simp only [f, K, weightedHeatKernel_zero, Matrix.diagonal_apply, mul_ite, mul_zero]
  simpa using hrel v

lemma graphHeat_tendsto (src dst : E → V) (ce : E → ℝ) (μ d : V → ℝ)
    (hc : ∀ e, 0 < ce e) (hμ : ∀ i, 0 < μ i) (hd : ∀ i, 0 < d i)
    (hrel : ∀ i, μ i * (d i * d i) = 1) (hsum : ∑ i, μ i = 1)
    (hconn : ∀ i j : V, i ≠ j → ∃ e,
      (src e = i ∧ dst e = j) ∨ (src e = j ∧ dst e = i)) :
    Tendsto (weightedHeatKernel (laplacianMatrix src dst ce) d) atTop
      (𝓝 (fun _ _ => (1 : ℝ))) := by
  let L := laplacianMatrix src dst ce
  have hL : L.PosSemidef := laplacianMatrix_posSemidef src dst ce (fun e => (hc e).le)
  let T := diagonal d * spectralKernelProjection (symmetricGenerator L d)
    (symmetricGenerator_posSemidef L hL d).1 * diagonal d
  have ht : Tendsto (weightedHeatKernel L d) atTop (𝓝 T) := weightedHeatKernel_tendsto L hL d
  have hz : L * T = 0 := weightedHeatKernel_limit_ker L hL.1 d (fun i => (hd i).ne')
  have hconst (v i j : V) : T i v = T j v := by
    apply graphLaplacian_kernel_constant src dst ce hc hconn (fun k => T k v)
    funext k
    rw [← laplacianMatrix_mulVec]
    exact congrFun₂ hz k v
  have hmass (v : V) : ∑ i, μ i * T i v = 1 := by
    have hh := tendsto_finsetSum Finset.univ (fun i _ =>
      ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp ht i)) v).const_mul (μ i))
    have he : (fun t : ℝ => ∑ i, μ i * weightedHeatKernel L d t i v) = (fun _ => 1) := by
      funext t
      exact graphHeat_mass src dst ce μ d hμ hrel t v
    rw [he] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  have he : T = (fun _ _ => (1 : ℝ)) := by
    ext i v
    have hh := hmass v
    simp_rw [hconst v _ i] at hh
    rw [← Finset.sum_mul, hsum, one_mul] at hh
    exact hh
  simpa only [he] using ht

lemma graphHeat_entropy_integral (src dst : E → V) (ce : E → ℝ) (μ d : V → ℝ)
    (hc : ∀ e, 0 < ce e) (hμ : ∀ i, 0 < μ i) (hd : ∀ i, 0 < d i)
    (hrel : ∀ i, μ i * (d i * d i) = 1) (hsum : ∑ i, μ i = 1)
    (hconn : ∀ i j : V, i ≠ j → ∃ e,
      (src e = i ∧ dst e = j) ∨ (src e = j ∧ dst e = i)) (v : V) :
    IntegrableOn (fun t => electricalEnergy src dst ce
      (fun i => weightedHeatKernel (laplacianMatrix src dst ce) d t i v)) (Set.Ioi 0) ∧
    (∫ t in Set.Ioi (0 : ℝ), electricalEnergy src dst ce
      (fun i => weightedHeatKernel (laplacianMatrix src dst ce) d t i v)) = Real.log (1 / μ v) := by
  apply heatEntropy_integral src dst ce μ _ v (fun e => (hc e).le) hμ
  · apply continuous_pi
    intro i
    exact (continuous_apply v).comp ((continuous_apply i).comp
      (weightedHeatKernel_continuous (laplacianMatrix src dst ce) d))
  · intro t ht i
    exact weightedHeatKernel_pos _ d hd (fun i j hij =>
      laplacianMatrix_offdiag_neg src dst ce hc hij (hconn i j hij)) t ht i v
  · intro t _ i
    exact graphHeat_entry_hasDerivAt src dst μ d ce hμ hrel t i v
  · funext i
    simp only [weightedHeatKernel_zero, Matrix.diagonal_apply, Pi.single_apply]
    by_cases hiv : i = v
    · subst i
      simp only [ite_true]
      apply (eq_div_iff (hμ v).ne').mpr
      simpa only [mul_comm] using hrel v
    · simp [hiv]
  · apply tendsto_pi_nhds.mpr
    intro i
    exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp
      (graphHeat_tendsto src dst ce μ d hc hμ hd hrel hsum hconn) i) v

end GraphHeat

section LocalizationIntegral
variable {E : Type uE} {V : Type uV} [Fintype E] [Fintype V]

lemma sum_abs_outer_le (μ : V → ℝ) (w : E → ℝ) (z : E → V → ℝ)
    (hμ : ∀ v, 0 ≤ μ v) (hw : ∀ e, 0 ≤ w e) :
    (∑ e, ∑ f, w e * w f * |∑ v, μ v * z e v * z f v|) ≤
      ∑ v, μ v * (∑ e, w e * |z e v|)^2 := by
  calc
    _ ≤ ∑ e, ∑ f, ∑ v, μ v * (w e * |z e v|) * (w f * |z f v|) := by
      apply Finset.sum_le_sum
      intro e _
      apply Finset.sum_le_sum
      intro f _
      calc
        _ ≤ w e * w f * ∑ v, |μ v * z e v * z f v| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (mul_nonneg (hw e) (hw f))
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro v _
          rw [abs_mul, abs_mul, abs_of_nonneg (hμ v)]
          ring
    _ = _ := by
      rw [Finset.sum_comm]
      conv_lhs => arg 2; ext f; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      simp only [sq, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro f _
      ring

lemma localization_integral_bound (Q : E → E → ℝ) (F : ℝ → E → E → ℝ)
    (I : ℝ → V → ℝ) (μ : V → ℝ) (w : E → ℝ) (S : ℝ)
    (hw : ∀ e, 0 ≤ w e)
    (hrep : ∀ e f, Q e f = 2 * ∫ t in Set.Ioi (0 : ℝ), F t e f)
    (hiF : ∀ e f, IntegrableOn (fun t => F t e f) (Set.Ioi 0))
    (hiI : ∀ v, IntegrableOn (fun t => I t v) (Set.Ioi 0))
    (hint : ∀ v, (∫ t in Set.Ioi (0 : ℝ), I t v) = Real.log (1 / μ v))
    (hb : ∀ t : ℝ, 0 < t →
      (∑ e, ∑ f, w e * w f * |F t e f|) ≤ S * ∑ v, μ v * I t v) :
    (∑ e, ∑ f, w e * w f * |Q e f|) ≤
      2 * S * ∑ v, μ v * Real.log (1 / μ v) := by
  have hiF' (e f : E) : IntegrableOn (fun t => w e * w f * |F t e f|) (Set.Ioi 0) :=
    (hiF e f).abs.const_mul _
  have hsumF : IntegrableOn (fun t => ∑ e, ∑ f, w e * w f * |F t e f|) (Set.Ioi 0) :=
    integrable_finsetSum _ (fun e _ => integrable_finsetSum _ (fun f _ => hiF' e f))
  have hsumI : IntegrableOn (fun t => ∑ v, μ v * I t v) (Set.Ioi 0) :=
    integrable_finsetSum _ (fun v _ => (hiI v).const_mul _)
  calc
    _ ≤ 2 * (∑ e, ∑ f, w e * w f * ∫ t in Set.Ioi (0 : ℝ), |F t e f|) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro e _
      apply Finset.sum_le_sum
      intro f _
      rw [hrep, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have hh := mul_le_mul_of_nonneg_left
        (abs_integral_le_integral_abs (f := fun t => F t e f) (μ := volume.restrict (Set.Ioi 0)))
        (mul_nonneg (hw e) (hw f))
      nlinarith
    _ = 2 * ∫ t in Set.Ioi (0 : ℝ), ∑ e, ∑ f, w e * w f * |F t e f| := by
      congr 1
      rw [integral_finsetSum _ (fun e _ => integrable_finsetSum _ (fun f _ => hiF' e f))]
      apply Finset.sum_congr rfl
      intro e _
      rw [integral_finsetSum _ (fun f _ => hiF' e f)]
      simp only [integral_const_mul]
    _ ≤ 2 * ∫ t in Set.Ioi (0 : ℝ), S * ∑ v, μ v * I t v := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply integral_mono_ae hsumF (hsumI.const_mul S)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hb t ht
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun v _ => (hiI v).const_mul _)]
      simp only [integral_const_mul, hint, mul_assoc]

end LocalizationIntegral

end SubpolynomialLp

end

end OAI
