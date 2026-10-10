import OAI.Analysis.CircleDomains.Rigidity.TraceIntegralNull
import OAI.Analysis.CircleDomains.Rigidity.TraceCompressionPayment
import OAI.Analysis.CircleDomains.Rigidity.TraceMaskAEPayment
import OAI.Analysis.CircleDomains.Sobolev.SobolevTypicalLinePayment
import OAI.Analysis.CircleDomains.Rigidity.TraceLineTails

namespace OAI

/-! Local inactivity of each finite prefix, vanishing active tails and
actual line payments force the unmasked trace of a null set to be null. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem null_image_of_masked_line_payments
    {C : Set ℝ} (hC : volume C = 0) (b : ℝ → ℝ)
    {I A : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j))
    (hIf : ∀ j, volume (I j) ≠ ∞) (τ : ℝ)
    (htail : Tendsto (fun N => volume (lineTailIntervals I A τ N)) atTop (𝓝 0))
    (cut : ℕ → ℕ → ℝ → ℝ) (hc : ∀ m j, ContDiff ℝ 1 (cut m j))
    (hunit : ∀ m j x, cut m j x ∈ Icc (0:ℝ) 1)
    (P Q : ℕ → ℝ → ℝ)
    (hPloc : ∀ m, LocallyIntegrable (P m) volume)
    (hQloc : ∀ m, LocallyIntegrable (Q m) volume)
    (hP0 : ∀ m t, 0 ≤ P m t) (hQ0 : ∀ m t, 0 ≤ Q m t)
    (hdom : ∀ m, ∀ᵐ t ∂volume, ∀ n, ∑ j ∈ Finset.range n,
      volume.real (I j)*|deriv (cut m j) t| ≤ P m t)
    (hpay : ∀ m x y, |infiniteTracePrimitive (cut m) I 0 x (b x)-
      infiniteTracePrimitive (cut m) I 0 y (b y)| ≤ ∫ t in uIoc x y, Q m t)
    (houter : ∀ m j, τ ∉ A j → ∀ x, cut m j x = 1)
    (hprefix : ∀ N x, x ∈ C → ∃ m V, IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, ∀ j < N, cut m j y = 1) : volume (b '' C) = 0 := by
  classical
  apply null_of_local_compressed_integral_payments hC b
    (fun N => lineTailIntervals_measurable hI τ N) 0 htail
  intro N x hx
  obtain ⟨m,V,hV,hxV,hpre⟩ := hprefix N x hx
  let J := Ioo (x-1) (x+1)
  let K := Icc (x-1) (x+1)
  let g := K.indicator (fun t => Q m t+P m t)
  have hK : MeasurableSet K := measurableSet_Icc
  have hg : Integrable g volume :=
    (integrable_indicator_iff hK).mpr (((hQloc m).add (hPloc m)).integrableOn_isCompact isCompact_Icc)
  refine ⟨V ∩ J,hV.inter isOpen_Ioo,⟨hxV,by dsimp only [J]; constructor <;> linarith⟩,
    g,hg,Eventually.of_forall (fun t => ?_),?_⟩
  · exact indicator_nonneg (fun t _ => add_nonneg (hQ0 m t) (hP0 m t)) _
  intro y hy z hz hyz _
  have hactive : ∀ w ∈ V, ∀ j t, t ∈ I j → t ∉ lineTailIntervals I A τ N → cut m j w = 1 := by
    intro w hw j t ht hnot
    by_cases hj : j < N
    · exact hpre w hw j hj
    by_cases hτ : τ ∈ A j
    · exfalso
      apply hnot
      apply mem_iUnion.mpr
      refine ⟨j-N,?_⟩
      simpa only [Nat.sub_add_cancel (Nat.le_of_not_gt hj),ite_eq_left hτ] using ht
    · exact houter m j hτ w
  have hPint : IntervalIntegrable (P m) volume y z :=
    intervalIntegrable_iff.mpr (((hPloc m).integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)
  have hQint : IntervalIntegrable (Q m) volume y z :=
    intervalIntegrable_iff.mpr (((hQloc m).integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)
  have hsp (t : ℝ) : |infiniteTracePrimitive (cut m) I 0 y t-
      infiniteTracePrimitive (cut m) I 0 z t| ≤ ∫ s in uIoc y z, P m s := by
    apply trace_primitive_line_payment_ae (hunit m) hI hIf
      (fun j => (hc m j).continuous_deriv_one.abs.intervalIntegrable y z) hPint
      (fun j a _ d _ => smooth_line_increment_payment_ae (hc m j)
        ((hc m j).continuous_deriv_one.abs.intervalIntegrable a d)
        (Eventually.of_forall (fun _ => le_rfl)))
      (fun n => ae_restrict_of_ae ((hdom m).mono (fun _ ht => ht n))) 0 t
      (left_mem_uIcc) (right_mem_uIcc)
  have hp := masked_trace_compression_payment (hunit m) hI
    (lineTailIntervals_measurable hI τ N) hactive 0 b hy.2.1 hz.2.1 hsp
  have hp' : |traceCompression (lineTailIntervals I A τ N) 0 (b z)-
      traceCompression (lineTailIntervals I A τ N) 0 (b y)| ≤
      ∫ t in Icc y z, Q m t+P m t := by
    rw [abs_sub_comm]
    apply hp.trans
    apply (add_le_add (hpay m y z) le_rfl).trans_eq
    rw [← integral_add hQint.def' hPint.def',uIoc_of_le hyz,← integral_Icc_eq_integral_Ioc]
  apply hp'.trans_eq
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only [g]
  rw [indicator_of_mem]
  constructor
  · exact le_trans (show x-1 ≤ y from hy.2.2.1.le) ht.1
  · exact le_trans ht.2 (show z ≤ x+1 from hz.2.2.2.le)

end CircleDomainRigidity

end

end OAI
