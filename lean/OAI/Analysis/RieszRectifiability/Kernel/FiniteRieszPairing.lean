import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.TruncationIntegrability
import OAI.Analysis.RieszRectifiability.Kernel.RieszPairingIdentification

namespace OAI

/-!
# Finite-measure truncated Riesz pairings

The scalar truncated kernel is measurable and bounded away from its singularity.
Symmetrization expresses finite-measure pairings as interior double integrals,
whose integrability yields convergence as the truncation scale tends to zero.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

def scalarTruncatedKernel {d : ℕ} (m : ℕ) (e : Ambient d) (ε : ℝ)
    (q : Ambient d × Ambient d) : ℝ :=
  if ε < dist q.1 q.2 then inner ℝ e (kernel m q.1 q.2) else 0

theorem scalarTruncatedKernel_measurable {d : ℕ} (m : ℕ) (e : Ambient d) (ε : ℝ) :
    Measurable (scalarTruncatedKernel m e ε) := by
  let : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  unfold scalarTruncatedKernel kernel
  apply Measurable.ite (measurableSet_lt measurable_const (continuous_fst.dist continuous_snd).measurable)
  · fun_prop
  · exact measurable_const

theorem scalarTruncatedKernel_bound {d : ℕ} (m : ℕ) (e : Ambient d) (ε : ℝ)
    (hε : 0 < ε) (q : Ambient d × Ambient d) :
    |scalarTruncatedKernel m e ε q| ≤ ‖e‖ * (ε ^ m)⁻¹ := by
  unfold scalarTruncatedKernel
  split_ifs with h
  · have hi : |inner ℝ e (kernel m q.1 q.2)| ≤ ‖e‖ * ‖kernel m q.1 q.2‖ := by
      simpa only [Real.norm_eq_abs] using! norm_inner_le_norm (𝕜 := ℝ) e (kernel m q.1 q.2)
    apply hi.trans
    exact mul_le_mul_of_nonneg_left (kernel_norm_le_truncation m q.1 q.2 ε hε h.le) (norm_nonneg e)
  · simp only [abs_zero]
    positivity

theorem scalarTruncatedKernel_swap {d : ℕ} (m : ℕ) (e : Ambient d) (ε : ℝ)
    (q : Ambient d × Ambient d) :
    scalarTruncatedKernel m e ε q.swap = -scalarTruncatedKernel m e ε q := by
  unfold scalarTruncatedKernel
  dsimp only [Prod.swap]
  simp only [dist_comm q.2 q.1]
  split_ifs
  · rw [kernel_antisymm, inner_neg_right]
  · exact neg_zero.symm

theorem truncated_inner_eq_scalar_integral {d : ℕ} (m : ℕ) (e : Ambient d)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (ε : ℝ) (hε : 0 < ε) (x : Ambient d) :
    inner ℝ e (truncated m ν ε (fun _ => 1) x) =
      ∫ y, scalarTruncatedKernel m e ε (x, y) ∂ν := by
  have hi : IntegrableOn (kernel m x) {y | ε < dist x y} ν := by
    simpa only [one_smul] using! truncation_integrable_of_finiteMeasure m ν (fun _ => 1)
      (memLp_const 1) x ε hε
  unfold truncated
  simp only [one_smul]
  rw [← integral_inner (𝕜 := ℝ) hi e]
  have hs : MeasurableSet {y : Ambient d | ε < dist x y} :=
    measurableSet_lt measurable_const (continuous_const.dist continuous_id).measurable
  rw [← integral_indicator hs]
  rfl

theorem truncated_weighted_pair_integrable {d : ℕ} (m : ℕ) (e : Ambient d)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (ε : ℝ) (hε : 0 < ε)
    (φ : Ambient d → ℝ) (hφm : Measurable φ) (hφ : Integrable φ ν) :
    Integrable (fun q : Ambient d × Ambient d => φ q.1 * scalarTruncatedKernel m e ε q) (ν.prod ν) := by
  have hdom := (hφ.abs.mul_prod (integrable_const (μ := ν) (1 : ℝ))).mul_const (‖e‖ * (ε ^ m)⁻¹)
  apply hdom.mono' ((hφm.comp measurable_fst).mul (scalarTruncatedKernel_measurable m e ε)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro q
  simp only [Pi.mul_apply, Function.comp_apply, Real.norm_eq_abs, abs_mul, mul_one]
  exact mul_le_mul_of_nonneg_left (scalarTruncatedKernel_bound m e ε hε q) (abs_nonneg _)

theorem finite_truncated_pairing_symmetrization {d : ℕ} (m : ℕ) (e : Ambient d)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (ε : ℝ) (hε : 0 < ε)
    (φ : Ambient d → ℝ) (hφm : Measurable φ) (hφ : Integrable φ ν) :
    (∫ x, φ x * inner ℝ e (truncated m ν ε (fun _ => 1) x) ∂ν) =
      (1 / 2 : ℝ) * (∫ q in {q : Ambient d × Ambient d | ε < dist q.1 q.2},
        rieszInteriorIntegrand m e φ q ∂ν.prod ν) := by
  let F := fun q : Ambient d × Ambient d => φ q.1 * scalarTruncatedKernel m e ε q
  let G := fun q : Ambient d × Ambient d => scalarTruncatedKernel m e ε q * (φ q.1 - φ q.2)
  have hF : Integrable F (ν.prod ν) := truncated_weighted_pair_integrable m e ν ε hε φ hφm hφ
  have hswap : Integrable (fun q : Ambient d × Ambient d => F q.swap) (ν.prod ν) := hF.swap
  have heq : G = fun q => F q + F q.swap := by
    funext q
    dsimp only [F, G]
    rw [scalarTruncatedKernel_swap]
    dsimp only [Prod.swap]
    ring
  have hG : (∫ q, G q ∂ν.prod ν) = 2 * (∫ q, F q ∂ν.prod ν) := by
    rw [heq, integral_add hF hswap, integral_prod_swap]
    ring
  have hleft : (∫ x, φ x * inner ℝ e (truncated m ν ε (fun _ => 1) x) ∂ν) =
      ∫ q, F q ∂ν.prod ν := by
    calc
      _ = ∫ x, ∫ y, F (x, y) ∂ν ∂ν := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro x
        change φ x * inner ℝ e (truncated m ν ε (fun _ => 1) x) = ∫ y, F (x, y) ∂ν
        rw [truncated_inner_eq_scalar_integral m e ν ε hε x]
        exact (integral_const_mul (φ x) _).symm
      _ = _ := (integral_prod F hF).symm
  have hright : (∫ q in {q : Ambient d × Ambient d | ε < dist q.1 q.2},
      rieszInteriorIntegrand m e φ q ∂ν.prod ν) = ∫ q, G q ∂ν.prod ν := by
    rw [← integral_indicator (measurableSet_lt measurable_const (continuous_fst.dist continuous_snd).measurable)]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro q
    by_cases h : ε < dist q.1 q.2
    · rw [Set.indicator_of_mem (show q ∈ {q : Ambient d × Ambient d | ε < dist q.1 q.2} from h)]
      simp only [G, scalarTruncatedKernel, ite_eq_left h, rieszInteriorIntegrand]
    · rw [Set.indicator_of_notMem (show q ∉ {q : Ambient d × Ambient d | ε < dist q.1 q.2} from h)]
      simp only [G, scalarTruncatedKernel, ite_eq_right h, zero_mul]
  rw [hleft, hright, hG]
  ring

theorem finite_truncated_pairing_tendsto_of_integrable {d : ℕ} (m : ℕ) (e : Ambient d)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν]
    (φ : Ambient d → ℝ) (hφm : Measurable φ) (hφ : Integrable φ ν)
    (hpair : Integrable (rieszInteriorIntegrand m e φ) (ν.prod ν)) :
    Tendsto (fun k : ℕ => ∫ x, φ x * inner ℝ e (truncated m ν ((1 / 2 : ℝ) ^ k) (fun _ => 1) x) ∂ν)
      atTop (𝓝 ((1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand m e φ q ∂ν.prod ν))) := by
  let s := fun k : ℕ => {q : Ambient d × Ambient d | (1 / 2 : ℝ) ^ k < dist q.1 q.2}
  have hs (k : ℕ) : MeasurableSet (s k) :=
    measurableSet_lt measurable_const (continuous_fst.dist continuous_snd).measurable
  have hmono : Monotone s := by
    intro k l hkl q hq
    exact lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hkl) hq
  have hcover : Function.support (rieszInteriorIntegrand m e φ) ⊆ ⋃ k, s k := by
    intro q hq
    have hne : q.1 ≠ q.2 := by
      intro heq
      apply hq
      simp only [rieszInteriorIntegrand, heq, kernel_self, inner_zero_right, zero_mul]
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (dist_pos.mpr hne) (by norm_num : (1 / 2 : ℝ) < 1)
    exact mem_iUnion.mpr ⟨k, hk⟩
  have hfull : (∫ q in ⋃ k, s k, rieszInteriorIntegrand m e φ q ∂ν.prod ν) =
      ∫ q, rieszInteriorIntegrand m e φ q ∂ν.prod ν := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro q hq
    by_contra hn
    exact hq (hcover hn)
  have ht := tendsto_setIntegral_of_monotone hs hmono hpair.restrict
  rw [hfull] at ht
  have heq : (fun k : ℕ => ∫ x, φ x * inner ℝ e (truncated m ν ((1 / 2 : ℝ) ^ k) (fun _ => 1) x) ∂ν) =
      fun k => (1 / 2 : ℝ) * (∫ q in s k, rieszInteriorIntegrand m e φ q ∂ν.prod ν) := by
    funext k
    exact finite_truncated_pairing_symmetrization m e ν _ (by positivity) φ hφm hφ
  rw [heq]
  exact ht.const_mul (1 / 2 : ℝ)

theorem rieszInteriorIntegrand_integrable_of_lipschitz {d : ℕ} (p : ℕ) (C : ℝ)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (hg : GlobalUpperGrowth (p + 1) C ν)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (r : ℝ) (hr : 0 < r) (hdiam : ∀ᵐ q ∂ν.prod ν, dist q.1 q.2 ≤ r) :
    Integrable (rieszInteriorIntegrand (p + 1) e φ) (ν.prod ν) := by
  let w := affineNormalHeight e 0 0
  have hw : LipschitzWith ‖e‖₊ w := affineNormalHeight_lipschitz e 0 0
  have hI := fractionalBilinear_integrable_of_ae_lipschitz p C ν hg w φ
    hw.continuous.measurable hφ.continuous.measurable ‖e‖₊ L
    (Filter.Eventually.of_forall fun q => by simpa only [Real.dist_eq] using! hw.dist_le_mul q.1 q.2)
    (Filter.Eventually.of_forall fun q => by simpa only [Real.dist_eq] using! hφ.dist_le_mul q.1 q.2)
    r hr hdiam
  have heq : rieszInteriorIntegrand (p + 1) e φ =
      fun q => fractionalBilinear (p + 1) w φ q.1 q.2 := by
    funext q
    exact rieszInteriorIntegrand_eq_fractionalBilinear (p + 1) e w φ
      (affineNormalHeight_difference e 0 0) q
  rw [heq]
  exact hI

theorem finite_localized_pairing_limit {d : ℕ} (p : ℕ) (C : ℝ)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (hg : GlobalUpperGrowth (p + 1) C ν)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφLip : LipschitzWith L φ)
    (hφ : Integrable φ ν) (r : ℝ) (hr : 0 < r)
    (hdiam : ∀ᵐ q ∂ν.prod ν, dist q.1 q.2 ≤ r) :
    Tendsto (fun k : ℕ => ∫ x, φ x * inner ℝ e (truncated (p + 1) ν ((1 / 2 : ℝ) ^ k) (fun _ => 1) x) ∂ν)
      atTop (𝓝 ((1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand (p + 1) e φ q ∂ν.prod ν))) :=
  finite_truncated_pairing_tendsto_of_integrable (p + 1) e ν φ hφLip.continuous.measurable hφ
    (rieszInteriorIntegrand_integrable_of_lipschitz p C ν hg e φ L hφLip r hr hdiam)

theorem truncated_restriction_eq_indicator {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (ε : ℝ) (x : Ambient d) :
    truncated m (μ.restrict s) ε (fun _ => 1) x = truncated m μ ε (s.indicator (fun _ => 1)) x := by
  classical
  have ht : MeasurableSet {y : Ambient d | ε < dist x y} :=
    measurableSet_lt measurable_const (continuous_const.dist continuous_id).measurable
  have heq : (fun y => s.indicator (fun _ => (1 : ℝ)) y • kernel m x y) = s.indicator (kernel m x) := by
    funext y
    by_cases hy : y ∈ s
    · simp only [Set.indicator_of_mem hy, one_smul]
    · simp only [Set.indicator_of_notMem hy, zero_smul]
  unfold truncated
  simp only [one_smul]
  rw [heq, integral_indicator hs, Measure.restrict_restrict ht, Measure.restrict_restrict hs, inter_comm]

end

end RieszRectifiability

end OAI
