import Mathlib
import OAI.Probability.SKValue.Evolution.BurgersDerivative

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma monotoneOn_ae_continuousAt_interior {T : ℝ} {γ : ℝ → ℝ}
    (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) :
    ∀ᵐ t : ℝ, t∈Ioo (0 : ℝ) T → ContinuousAt γ t := by
  filter_upwards [hγ.countable_not_continuousWithinAt.ae_notMem volume] with t ht hti
  have hc : ContinuousWithinAt γ (Icc (0 : ℝ) T) t := by
    by_contra hc
    exact ht ⟨⟨hti.1.le,hti.2.le⟩,hc⟩
  exact hc.continuousAt (Icc_mem_nhds hti.1 hti.2)

lemma SmoothEvolution.heat_nonlinearity_continuousOn {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (a x : ℝ) :
    ContinuousOn (fun t ↦ heat (t-a) (fun y ↦ deriv (V t) y*deriv (deriv (V t)) y) x)
      (Icc (0 : ℝ) T) := by
  obtain ⟨C,hC,hb⟩ := h.bound 0
  obtain ⟨D,hD,hd⟩ := h.bound 1
  simp only [iteratedDeriv_zero] at hb
  simp only [iteratedDeriv_one] at hd
  apply heat_family_continuousOn (C := C*D)
  · simpa only [iteratedDeriv_zero,iteratedDeriv_one,Pi.mul_def] using
      (h.jet_joint_continuousOn 0).mul (h.jet_joint_continuousOn 1)
  · positivity
  · intro t ht y
    rw [abs_mul]
    exact mul_le_mul (hb t ht y) (hd t ht y) (abs_nonneg _) hC

lemma SmoothEvolution.heat_gradient_interval {T a q b : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hm : Measurable γ) (hγ : MonotoneOn γ (Icc (0 : ℝ) T))
    (ha : 0≤a) (haq : a<q) (hqb : q≤b) (hb : b≤T) (x : ℝ) :
    heat (b-a) (deriv (V b)) x-heat (q-a) (deriv (V q)) x =
      -(∫ s in q..b, γ s*heat (s-a) (fun y ↦ deriv (V s) y*deriv (deriv (V s)) y) x) := by
  obtain ⟨L,hL⟩ := h.heat_gradient_lipschitzOn ha haq hqb hb x
  have hL' : LipschitzOnWith L (fun t ↦ heat (t-a) (deriv (V t)) x) (uIcc q b) := by
    simpa only [uIcc_of_le hqb] using hL
  rw [←hL'.absolutelyContinuousOnInterval.integral_deriv_eq_sub,←intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [monotoneOn_ae_continuousAt_interior hγ,(Set.countable_singleton b).ae_notMem volume] with s hs hsb hsi
  rw [uIoc_of_le hqb] at hsi
  have hst : s<T := (lt_of_le_of_ne hsi.2 (by simpa only [mem_singleton_iff] using hsb)).trans_le hb
  have has : a<s := haq.trans hsi.1
  have hd := h.heat_gradient_hasDerivAt hm ha has hst (hs ⟨ha.trans_lt has,hst⟩) x
  simpa only [neg_mul] using hd.deriv

lemma SmoothEvolution.burgers_mild {T a b : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hm : Measurable γ) (hγ : MonotoneOn γ (Icc (0 : ℝ) T))
    (hi : IntervalIntegrable γ volume 0 T) (ha : 0≤a) (hab : a≤b) (hb : b≤T) (x : ℝ) :
    deriv (V a) x=heat (b-a) (deriv (V b)) x+
      ∫ s in a..b, γ s*heat (s-a) (fun y ↦ deriv (V s) y*deriv (deriv (V s)) y) x := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  have haT : a∈Icc (0 : ℝ) T := ⟨ha,hab.le.trans hb⟩
  have hT : 0≤T := ha.trans haT.2
  let g := fun s ↦ γ s*heat (s-a) (fun y ↦ deriv (V s) y*deriv (deriv (V s)) y) x
  have hg : IntervalIntegrable g volume a b := by
    apply (hi.mono_set ?_).mul_continuousOn
    · simpa only [uIcc_of_le hab.le] using
        (h.heat_nonlinearity_continuousOn a x).mono (Icc_subset_Icc ha hb)
    · simp only [uIcc_of_le hab.le,uIcc_of_le hT]
      exact Icc_subset_Icc ha hb
  have hF : Tendsto (fun q ↦ heat (q-a) (deriv (V q)) x) (𝓝[>] a) (𝓝 (deriv (V a) x)) := by
    have hh := (h.heat_gradient_continuousOn a x a haT).mono_of_mem_nhdsWithin
      (mem_of_superset (Ioo_mem_nhdsGT hab) (fun s hs ↦ ⟨ha.trans hs.1.le,hs.2.le.trans hb⟩))
    simpa only [sub_self,heat_zero] using hh.tendsto
  have hI : Tendsto (fun q ↦ ∫ s in q..b, g s) (𝓝[>] a) (𝓝 (∫ s in a..b, g s)) := by
    have hgI : IntegrableOn g (uIcc a b) volume := (intervalIntegrable_iff').mp hg
    have hh := (intervalIntegral.continuousOn_primitive_interval_left hgI a
      (by simp only [uIcc_of_le hab.le]; exact ⟨le_rfl,hab.le⟩)).mono_of_mem_nhdsWithin
      (mem_of_superset (Ioo_mem_nhdsGT hab) (by intro s hs; simpa only [uIcc_of_le hab.le] using ⟨hs.1.le,hs.2.le⟩))
    exact hh.tendsto
  have he : (fun q ↦ heat (q-a) (deriv (V q)) x) =ᶠ[𝓝[>] a]
      (fun q ↦ heat (b-a) (deriv (V b)) x+∫ s in q..b, g s) := by
    filter_upwards [Ioo_mem_nhdsGT hab] with q hq
    have hh := h.heat_gradient_interval hm hγ ha hq.1 hq.2.le hb x
    change _ = -(∫ s in q..b, g s) at hh
    linarith
  exact tendsto_nhds_unique hF ((tendsto_const_nhds.add hI).congr' he.symm)

end SKValue

end

end OAI
