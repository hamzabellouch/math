import OAI.Probability.SLE.Geometry.HalfPlaneCayleyCompactification

namespace OAI

/-! A proper half-plane ray becomes an injective compact disk crosscut
from `-1` to `1`. The endpoint at infinity is filled by the proved Cayley
limit, preserving the prescribed ray parameter. -/
noncomputable section
open Set Filter Complex
open scoped Topology NNReal

namespace SLEExactGauge

def crosscutParameter (s : ℝ) : ℝ≥0 := (s/(1-s)).toNNReal

lemma crosscutParameter_injectiveOn : InjOn crosscutParameter (Ico 0 1) := by
  intro s hs t ht he
  have he' := congrArg (fun r : ℝ≥0 => (r : ℝ)) he
  have hsval : (crosscutParameter s : ℝ)=s/(1-s) :=
    Real.coe_toNNReal _ (div_nonneg hs.1 (sub_pos.mpr hs.2).le)
  have htval : (crosscutParameter t : ℝ)=t/(1-t) :=
    Real.coe_toNNReal _ (div_nonneg ht.1 (sub_pos.mpr ht.2).le)
  rw [hsval,htval] at he'
  have hh := (div_eq_div_iff (sub_pos.mpr hs.2).ne' (sub_pos.mpr ht.2).ne').mp he'
  nlinarith

lemma crosscutParameter_continuousOn : ContinuousOn crosscutParameter (Ico 0 1) := by
  apply continuous_real_toNNReal.comp_continuousOn
  exact continuousOn_id.div (continuousOn_const.sub continuousOn_id)
    (fun _ hs => (sub_pos.mpr hs.2).ne')

lemma crosscutParameter_tendsto : Tendsto crosscutParameter (𝓝[<] 1) atTop := by
  have hid : Tendsto (fun s : ℝ => s) (𝓝[<] 1) (𝓝 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hsub : Tendsto (fun s : ℝ => 1-s) (𝓝[<] 1) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa only [sub_self] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1:ℝ)) (𝓝[<] 1) (𝓝 1)).sub hid
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change 0 < 1-s
      exact sub_pos.mpr hs
  have hh := hid.pos_mul_atTop zero_lt_one (tendsto_inv_nhdsGT_zero.comp hsub)
  exact tendsto_real_toNNReal_atTop.comp
    (by simpa only [div_eq_mul_inv,Function.comp_apply] using hh)

def compactifiedCrosscut (β : ℝ≥0 → ℂ) : ℝ → ℂ :=
  Function.update (fun s => halfPlaneCayley (β (crosscutParameter s))) 1 1

lemma compactifiedCrosscut_one (β : ℝ≥0 → ℂ) : compactifiedCrosscut β 1=1 :=
  Function.update_self ..

lemma compactifiedCrosscut_eq (β : ℝ≥0 → ℂ) {s : ℝ} (hs : s < 1) :
    compactifiedCrosscut β s=halfPlaneCayley (β (crosscutParameter s)) :=
  Function.update_of_ne hs.ne _ _

lemma compactifiedCrosscut_zero (β : ℝ≥0 → ℂ) (h0 : β 0=0) :
    compactifiedCrosscut β 0 = -1 := by
  rw [compactifiedCrosscut_eq β zero_lt_one]
  simp only [crosscutParameter,zero_div,Real.toNNReal_zero,h0,halfPlaneCayley_zero]

theorem compactifiedCrosscut_properties
    (β : ℝ≥0 → ℂ) (hc : Continuous β) (hi : Function.Injective β) (h0 : β 0=0)
    (hH : ∀ t : ℝ≥0, 0 < t → β t ∈ upperHalfPlane)
    (hinfty : Tendsto β atTop (cocompact ℂ)) :
    ContinuousOn (compactifiedCrosscut β) (Icc 0 1) ∧
      InjOn (compactifiedCrosscut β) (Icc 0 1) ∧
      ∀ s ∈ Ioo 0 1, ‖compactifiedCrosscut β s‖ < 1 := by
  have hH' (t : ℝ≥0) : 0 ≤ (β t).im := by
    by_cases ht : t=0
    · simp [ht,h0]
    · exact (hH t (pos_iff_ne_zero.mpr ht)).le
  have hbase : ContinuousOn (fun s => halfPlaneCayley (β (crosscutParameter s)))
      (Ico 0 1) := by
    apply halfPlaneCayley_continuousOn.comp
      (hc.comp_continuousOn crosscutParameter_continuousOn)
    intro s _
    exact hH' _
  have hceq : Icc (0:ℝ) 1 \ {1} = Ico 0 1 := by
    ext s
    simp only [Set.mem_sdiff,mem_Icc,mem_singleton_iff,mem_Ico]
    constructor
    · rintro ⟨⟨hs,hs1⟩,hn⟩
      exact ⟨hs,lt_of_le_of_ne hs1 hn⟩
    · rintro ⟨hs,hs1⟩
      exact ⟨⟨hs,hs1.le⟩,hs1.ne⟩
  refine ⟨?_,?_,?_⟩
  · apply continuousOn_update_iff.mpr
    rw [hceq]
    refine ⟨hbase,fun _ => ?_⟩
    exact (halfPlaneCayley_tendsto_infinity.comp (hinfty.comp crosscutParameter_tendsto)).mono_left
      (nhdsWithin_mono _ Ico_subset_Iio_self)
  · intro s hs t ht he
    by_cases hs1 : s=1
    · subst s
      by_contra ht1
      rw [compactifiedCrosscut_one,
        compactifiedCrosscut_eq β (lt_of_le_of_ne ht.2 (fun h => ht1 h.symm))] at he
      exact halfPlaneCayley_ne_one (hH' _) he.symm
    · by_cases ht1 : t=1
      · subst t
        rw [compactifiedCrosscut_one,compactifiedCrosscut_eq β (lt_of_le_of_ne hs.2 hs1)] at he
        exact False.elim (halfPlaneCayley_ne_one (hH' _) he)
      · have hslt := lt_of_le_of_ne hs.2 hs1
        have htlt := lt_of_le_of_ne ht.2 ht1
        rw [compactifiedCrosscut_eq β hslt,compactifiedCrosscut_eq β htlt] at he
        exact crosscutParameter_injectiveOn ⟨hs.1,hslt⟩ ⟨ht.1,htlt⟩
          (hi (halfPlaneCayley_injOn (hH' _) (hH' _) he))
  · intro s hs
    rw [compactifiedCrosscut_eq β hs.2]
    apply halfPlaneCayley_norm_lt
    apply hH
    change 0 < (s/(1-s)).toNNReal
    exact Real.toNNReal_pos.mpr (div_pos hs.1 (sub_pos.mpr hs.2))

end SLEExactGauge

end

end OAI
