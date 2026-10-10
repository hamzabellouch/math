import OAI.Dynamics.StandardMap.Lyapunov.ActualLyapunov
import OAI.Dynamics.StandardMap.Components.Definitions

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

def MainContinuationObligation : Prop :=
  ∃ k₀ : ℝ, 0 < k₀ ∧ ∀ k : ℝ, k₀ ≤ k →
    (∃ L : Torus → ℝ, Measurable L ∧ Integrable L area ∧
      (∀ z, L (standardMap k z) = L z) ∧
      (∀ᵐ z ∂area, LyapunovSpectrumAt k z (L z)) ∧
      (∀ᵐ z ∂area, Tendsto
        (fun n : ℕ => Real.log ‖standardDerivativeProduct k z n‖ / (n : ℝ))
        atTop (𝓝 (L z))) ∧
      0 < area {z | 0 < L z} ∧
      metricEntropy area (standardMap k) = ENNReal.ofReal (∫ z, L z ∂area)) ∧
    HyperbolicBernoulliComponent k

end StandardMapEntropy
end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

def hyperbolicRegion (k : ℝ) (hk : 0 ≤ k) : Set Torus :=
  {z | 0 < standardLyapunov k hk z}

lemma measurableSet_hyperbolicRegion (k : ℝ) (hk : 0 ≤ k) :
    MeasurableSet (hyperbolicRegion k hk) :=
  measurableSet_lt measurable_const (measurable_standardLyapunov k hk)

lemma preimage_hyperbolicRegion (k : ℝ) (hk : 0 ≤ k) :
    standardMap k ⁻¹' hyperbolicRegion k hk = hyperbolicRegion k hk := by
  ext z
  simp only [hyperbolicRegion, mem_preimage, mem_ofPred_eq, standardLyapunov_invariant]

lemma normalizedArea_probability {E : Set Torus} (hE : 0 < area E) :
    IsProbabilityMeasure (normalizedArea E) := by
  constructor
  simp only [normalizedArea, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel hE.ne' (measure_lt_top area E).ne

lemma normalizedArea_absolutelyContinuous (E : Set Torus) : normalizedArea E ≪ area :=
  Measure.absolutelyContinuous_restrict.smul_left _

lemma normalizedArea_ae_mem {E : Set Torus} (hE : MeasurableSet E) :
    ∀ᵐ z ∂normalizedArea E, z ∈ E :=
  (ae_restrict_mem hE).filter_mono (Measure.ae_smul_measure_le _)

lemma normalizedArea_integrable {E : Set Torus} (hE : 0 < area E)
    {f : Torus → ℝ} (hf : Integrable f area) : Integrable f (normalizedArea E) :=
  hf.integrableOn.smul_measure (ENNReal.inv_ne_top.mpr hE.ne')

lemma measurePreserving_normalizedArea {k : ℝ} {E : Set Torus}
    (hE : MeasurableSet E) (hinv : standardMap k ⁻¹' E = E) :
    MeasurePreserving (standardMap k) (normalizedArea E) (normalizedArea E) := by
  have hh := (measurePreserving_standardMap k).restrict_preimage hE
  rw [hinv] at hh
  exact hh.smul_measure _

theorem hyperbolic_probability_of_deficit (k : ℝ) (hk : 0 ≤ k)
    (hdef : ∀ n : ℕ, 0 < n → meanDeficit k n < (1/8 : ℝ)) :
    let H := hyperbolicRegion k hk
    MeasurableSet H ∧ 0 < area H ∧ standardMap k ⁻¹' H = H ∧
    IsProbabilityMeasure (normalizedArea H) ∧ normalizedArea H ≪ area ∧
    MeasurePreserving (standardMap k) (normalizedArea H) (normalizedArea H) ∧
    Integrable (fun z => Real.log ‖standardDerivative k z‖) (normalizedArea H) ∧
    Integrable (fun z => Real.log ‖standardInverseDerivative k z‖) (normalizedArea H) ∧
    (∀ᵐ z ∂normalizedArea H, ∃ l : ℝ, 0 < l ∧ LyapunovSpectrumAt k z l) := by
  dsimp only
  have hm := measurableSet_hyperbolicRegion k hk
  have hp := positive_standardLyapunov_of_deficit k hk hdef
  have hi := preimage_hyperbolicRegion k hk
  refine ⟨hm, hp, hi, normalizedArea_probability hp,
    normalizedArea_absolutelyContinuous _, measurePreserving_normalizedArea hm hi,
    normalizedArea_integrable hp (integrable_log_standardDerivative k),
    normalizedArea_integrable hp (integrable_log_standardInverseDerivative k), ?_⟩
  have hs : ∀ᵐ z ∂normalizedArea (hyperbolicRegion k hk),
      LyapunovSpectrumAt k z (standardLyapunov k hk z) :=
    (ae_standardLyapunov_spectrum k hk).filter_mono
      (normalizedArea_absolutelyContinuous _).ae_le
  filter_upwards [normalizedArea_ae_mem hm, hs] with z hz hspec
  exact ⟨standardLyapunov k hk z, hz, hspec⟩

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter BoundedSubadditive
open scoped Topology ENNReal

lemma measurePreserving_torusSwap : MeasurePreserving (Prod.swap : Torus → Torus) area area :=
  Measure.measurePreserving_swap

lemma torusIter_neg_nat_apply (k : ℝ) (n : ℕ) (z : Torus) :
    torusIter k (-(n : ℤ)) z = (torusStep k).symm^[n] z := by
  simp only [torusIter, zpow_neg, zpow_natCast, ← inv_pow,
    Equiv.Perm.inv_def, Equiv.Perm.coe_pow]

lemma transfer_lowerRate_inverse_iterate (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (z : Torus) :
    (transferCocycle k hk).lowerRate (torusIter k (-(n : ℤ)) z) =
      (transferCocycle k hk).lowerRate z := by
  have hi (w : Torus) : (transferCocycle k hk).lowerRate ((torusStep k).symm w) =
      (transferCocycle k hk).lowerRate w := by
    simpa only [Equiv.apply_symm_apply] using
      ((transferCocycle k hk).lowerRate_shift ((torusStep k).symm w)).symm
  rw [torusIter_neg_nat_apply]
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', hi, ih]

lemma transfer_average_reverse (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (z : Torus) :
    (transferCocycle k hk).average n z.swap =
      (transferCocycle k hk).average n (torusIter k (-(n : ℤ)) z) := by
  apply mul_left_cancel₀ (log_growthBase_pos k hk).ne'
  rw [← lognorm_average_eq, ← lognorm_average_eq]
  rw [torusSegmentTransfer_shift, zero_add, torusSegmentTransfer_reverse_norm]

lemma transfer_lowerRate_swap_ae (k : ℝ) (hk : 0 ≤ k) :
    ∀ᵐ z ∂area, (transferCocycle k hk).lowerRate z.swap =
      (transferCocycle k hk).lowerRate z := by
  let f := transferCocycle k hk
  have hconv := f.ae_tendsto_average (measurePreserving_torusStep k)
  have hconvSwap := measurePreserving_torusSwap.quasiMeasurePreserving.ae hconv
  have hbound (n : ℕ) (z : Torus) : |f.average n z - f.lowerRate z| ≤ 1 := by
    rcases f.average_bounds n z with ⟨h0,h1⟩
    rcases f.lowerRate_bounds z with ⟨l0,l1⟩
    exact abs_le.mpr (by constructor <;> linarith)
  have hboundSwap (n : ℕ) (z : Torus) : |f.average n z.swap - f.lowerRate z| ≤ 1 := by
    rcases f.average_bounds n z.swap with ⟨h0,h1⟩
    rcases f.lowerRate_bounds z with ⟨l0,l1⟩
    exact abs_le.mpr (by constructor <;> linarith)
  have hlim : Tendsto (fun n => ∫ z, |f.average n z - f.lowerRate z| ∂area)
      atTop (𝓝 0) := by
    have hh := tendsto_integral_of_dominated_convergence (μ := area) (fun _ : Torus => (1 : ℝ))
      (F := fun n z => |f.average n z-f.lowerRate z|) (f := fun _ => (0 : ℝ))
      (fun n => ((f.measurable_average n).sub f.measurable_lowerRate).abs.aestronglyMeasurable)
      (integrable_const 1)
      (fun n => Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_abs]; exact hbound n z) ?_
    · simpa only [integral_zero] using hh
    · filter_upwards [hconv] with z hz
      simpa only [sub_self, abs_zero] using (hz.sub (tendsto_const_nhds (x := f.lowerRate z))).abs
  have hlimSwap : Tendsto
      (fun n => ∫ z, |f.average n z.swap - f.lowerRate z| ∂area) atTop
      (𝓝 (∫ z, |f.lowerRate z.swap - f.lowerRate z| ∂area)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : Torus => (1 : ℝ))
      (fun n => (((f.measurable_average n).comp measurable_swap).sub
        f.measurable_lowerRate).abs.aestronglyMeasurable) (integrable_const 1)
      (fun n => Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_abs]; exact hboundSwap n z)
    filter_upwards [hconvSwap] with z hz
    exact (hz.sub (tendsto_const_nhds (x := f.lowerRate z))).abs
  have heq (n : ℕ) : (∫ z, |f.average n z.swap-f.lowerRate z| ∂area) =
      ∫ z, |f.average n z-f.lowerRate z| ∂area := by
    calc
      _ = ∫ z, |f.average n (torusIter k (-(n : ℤ)) z)-
          f.lowerRate (torusIter k (-(n : ℤ)) z)| ∂area := by
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by
          dsimp only
          rw [show f.average n z.swap = f.average n (torusIter k (-(n : ℤ)) z) from
            transfer_average_reverse k hk n z,
            show f.lowerRate (torusIter k (-(n : ℤ)) z) = f.lowerRate z from
            transfer_lowerRate_inverse_iterate k hk n z]
      _ = _ := integral_torusIter k (-(n : ℤ)) (fun z => |f.average n z-f.lowerRate z|)
  have hzero : (∫ z, |f.lowerRate z.swap-f.lowerRate z| ∂area) = 0 :=
    tendsto_nhds_unique hlimSwap (hlim.congr (fun n => (heq n).symm))
  have hint : Integrable (fun z => |f.lowerRate z.swap-f.lowerRate z|) area :=
    ((measurePreserving_torusSwap.integrable_comp_of_integrable f.integrable_lowerRate).sub
      f.integrable_lowerRate).abs
  have h := (integral_eq_zero_iff_of_nonneg (fun z => abs_nonneg _) hint).mp hzero
  filter_upwards [h] with z hz
  exact sub_eq_zero.mp (abs_eq_zero.mp hz)

lemma transferLyapunov_swap_ae (k : ℝ) (hk : 0 ≤ k) :
    ∀ᵐ z ∂area, transferLyapunov k hk z.swap = transferLyapunov k hk z := by
  filter_upwards [transfer_lowerRate_swap_ae k hk] with z hz
  exact congrArg (fun t => Real.log (growthBase k)*t) hz

lemma ae_transfer_inverse_rate (k : ℝ) (hk : 0 ≤ k) :
    ∀ᵐ z ∂area, Tendsto
      (fun n : ℕ => Real.log ‖torusSegmentTransfer k z (-(n : ℤ)) n‖ / (n : ℝ))
      atTop (𝓝 (transferLyapunov k hk z)) := by
  have hconv := measurePreserving_torusSwap.quasiMeasurePreserving.ae
    (transferLyapunov_limit k hk).2.2.2.2
  filter_upwards [hconv, transferLyapunov_swap_ae k hk] with z hz heq
  rw [← heq]
  simpa only [torusSegmentTransfer_reverse_norm] using hz

end StandardMapEntropy

end
end

end OAI
