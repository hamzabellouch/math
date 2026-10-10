import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.ShellTelescoping

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter Set Metric
open scoped BigOperators
open CoulombObservation

lemma masterWidth_le_half_bound {c r₀ s R : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1/2)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (hrR : r₀ ≤ R)
    {x : Space} (hx : ‖x‖ ≤ R) : masterWidth c r₀ s x ≤ R/2 := by
  have hpow : s^masterExponent ≤ 1 := Real.rpow_le_one hs.le hs1 masterExponent_nonneg
  have hbase : masterBaseDistance r₀ x ≤ R := max_le hx hrR
  have hp : 0 ≤ masterBaseDistance r₀ x := (norm_nonneg x).trans (le_max_left _ _)
  calc
    _ ≤ c*masterBaseDistance r₀ x*s^masterExponent := masterWidth_upper hc hr hs x
    _ ≤ c*masterBaseDistance r₀ x*1 := mul_le_mul_of_nonneg_left hpow (mul_nonneg hc hp)
    _ ≤ R/2 := by nlinarith [hr.le.trans hrR]

lemma masterKernel_zero_outer {c r₀ s R : ℝ} (hc : 0 < c) (hc1 : c ≤ 1/2)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (hrR : r₀ ≤ R)
    {g : Space → ℝ} (hgs : tsupport g ⊆ ball 0 1)
    {x y : Space} (hx : ‖x‖ ≤ R) (hy : 2*R < ‖y‖) : masterKernel c r₀ s g x y = 0 := by
  have hb := masterWidth_le_half_bound hc.le hc1 hr hs hs1 hrR hx
  have hn : ‖y‖ ≤ ‖y-x‖+‖x‖ := norm_le_norm_sub_add y x
  have he : scaledRealPacket (masterWidth c r₀ s x) g (y-x) = 0 := by
    by_contra hh
    have hv := scaledRealPacket_support (masterWidth_pos hc hr hs x) hgs hh
    linarith [hr.le.trans hrR]
  simp only [masterKernel,he,zero_pow (by norm_num : (2:ℕ) ≠ 0)]

def masterTailTest (c r₀ s R : ℝ) (g : Space → ℝ) (x : Space) : ℝ :=
  ∫ y in {y : Space | R < ‖y‖}, masterKernel c r₀ s g x y

lemma masterTailTest_nonneg (c r₀ s R : ℝ) (g : Space → ℝ) (x : Space) :
    0 ≤ masterTailTest c r₀ s R g x :=
  integral_nonneg (fun y => masterKernel_nonneg c r₀ s g x y)

lemma masterTailTest_measurable {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    (R : ℝ) {g : Space → ℝ} (hg : Continuous g) : Measurable (masterTailTest c r₀ s R g) :=
  (masterKernel_joint_continuous hc hr hs hg).measurable.stronglyMeasurable.integral_prod_right.measurable

lemma masterTailTest_le_one {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    (R : ℝ) {g : Space → ℝ} (hgn : ∫ z, (g z)^2 = 1) (x : Space) :
    masterTailTest c r₀ s R g x ≤ 1 :=
  (setIntegral_le_integral (masterKernel_integrable hc hr hs hgn x)
    (ae_of_all _ (fun y => masterKernel_nonneg c r₀ s g x y))).trans_eq
      (masterKernel_mass hc hr hs hgn x)

lemma masterTailTest_zero_inner {c r₀ s R : ℝ} (hc : 0 < c) (hc1 : c ≤ 1/2)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (hrR : r₀ ≤ R)
    {g : Space → ℝ} (hgs : tsupport g ⊆ ball 0 1) {x : Space} (hx : ‖x‖ ≤ R) :
    masterTailTest c r₀ s (2*R) g x = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  exact masterKernel_zero_outer hc hc1 hr hs hs1 hrR hgs hx hy

lemma masterTailTest_count_le {c r₀ s R : ℝ} (hc : 0 < c) (hc1 : c ≤ 1/2)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (hrR : r₀ ≤ R)
    {g : Space → ℝ} (hgs : tsupport g ⊆ ball 0 1) (hgn : ∫ z, (g z)^2 = 1)
    {N : ℕ} (x : Configuration N) :
    (∑ i, masterTailTest c r₀ s (2*R) g (x i)) ≤ rawExteriorCount R x := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : R ≤ ‖x i‖
  · rw [ite_eq_left hi]
    exact masterTailTest_le_one hc hr hs _ hgn _
  · rw [ite_eq_right hi, masterTailTest_zero_inner hc hc1 hr hs hs1 hrR hgs (le_of_not_ge hi)]

open MeasureTheory Filter Set Metric
open scoped BigOperators
open CoulombObservation

lemma masterTailTest_graph_integrable {N : ℕ} (F : fermionGraph N)
    {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    (R : ℝ) {g : Space → ℝ} (hg : Continuous g) (hgn : ∫ z, (g z)^2 = 1) :
    Integrable (fun x : Configuration N => ∑ i, masterTailTest c r₀ s R g (x i)) (graphRawLaw F) := by
  apply graph_weight_integrable F _
    (Finset.measurable_sum _ (fun i _ => (masterTailTest_measurable hc hr hs R hg).comp (measurable_pi_apply i)))
  intro x
  change ‖∑ i, masterTailTest c r₀ s R g (x i)‖ ≤ (N:ℝ)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => masterTailTest_nonneg c r₀ s R g (x i)))]
  calc
    _ ≤ ∑ i : Fin N, (1:ℝ) := Finset.sum_le_sum (fun i _ => masterTailTest_le_one hc hr hs R hgn (x i))
    _ = N := by simp

lemma jointMasterPosterior_tail {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    (R : ℝ) {g : Space → ℝ} (hg : Continuous g) (hgn : ∫ z, (g z)^2 = 1)
    (z : OriginalDatum N K ell j) :
    (∫ y in {y : Space | R < ‖y‖}, jointMasterPosterior μ ell j c r₀ s g z y) =
      kernelPosteriorTest μ ell j (masterTailTest c r₀ s R g) z := by
  have hi := masterConfigurationKernel_integrable (originalRawKernel μ ell j z) hc hr hs hg hgn
  have hi' : Integrable (fun p : Configuration N × Space => ∑ i, masterKernel c r₀ s g (p.1 i) p.2)
      ((originalRawKernel μ ell j z).prod (volume.restrict {y : Space | R < ‖y‖})) :=
    hi.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  change (∫ y in {y : Space | R < ‖y‖}, ∫ x, ∑ i, masterKernel c r₀ s g (x i) y
    ∂originalRawKernel μ ell j z) = _
  rw [←integral_integral_swap hi']
  unfold kernelPosteriorTest masterTailTest
  apply integral_congr_ae
  exact ae_of_all _ (fun x => integral_finsetSum _ (fun i _ =>
    (masterKernel_integrable hc hr hs hgn (x i)).integrableOn))

lemma original_master_tail_integrable {N K : ℕ} (F : fermionGraph N)
    (ell : Fin K → ℝ) (j : ℕ) {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    (R : ℝ) {g : Space → ℝ} (hg : Continuous g) (hgn : ∫ z, (g z)^2 = 1) :
    Integrable (fun z => ∫ y in {y : Space | R < ‖y‖},
      jointMasterPosterior (graphRawLaw F) ell j c r₀ s g (originalDatum ell j z) y)
      (physicalObservationLaw (graphRawLaw F) K) := by
  simp_rw [jointMasterPosterior_tail _ ell j hc hr hs R hg hgn]
  exact kernelPosteriorTest_integrable _ ell j (masterTailTest_measurable hc hr hs R hg)
    (masterTailTest_graph_integrable F hc hr hs R hg hgn)

lemma original_master_tail_mean_le {N K : ℕ} (F : fermionGraph N)
    (ell : Fin K → ℝ) (j : ℕ) {c r₀ s R : ℝ} (hc : 0 < c) (hc1 : c ≤ 1/2)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (hrR : r₀ ≤ R)
    {g : Space → ℝ} (hg : Continuous g) (hgs : tsupport g ⊆ ball 0 1)
    (hgn : ∫ z, (g z)^2 = 1) :
    (∫ z, (∫ y in {y : Space | 2*R < ‖y‖},
      jointMasterPosterior (graphRawLaw F) ell j c r₀ s g (originalDatum ell j z) y)
      ∂physicalObservationLaw (graphRawLaw F) K) ≤
      ∫ x, rawExteriorCount R x ∂graphRawLaw F := by
  simp_rw [jointMasterPosterior_tail _ ell j hc hr hs (2*R) hg hgn]
  rw [kernelPosteriorTest_mean _ ell j (masterTailTest_measurable hc hr hs (2*R) hg)
    (masterTailTest_graph_integrable F hc hr hs (2*R) hg hgn)]
  exact integral_mono (masterTailTest_graph_integrable F hc hr hs (2*R) hg hgn)
    (rawExteriorCount_integrable F R) (masterTailTest_count_le hc hc1 hr hs hs1 hrR hgs hgn)

end CoulombAtom

end

end OAI
