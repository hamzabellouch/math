import Mathlib

namespace OAI

universe uIota

open Set Filter
open scoped Topology

namespace Problem326

/-- A positive derivative gives strict increase immediately to the right. -/
lemma eventually_lt_right_of_hasDerivAt_pos {f : ℝ → ℝ} {f' t : ℝ}
    (hf : HasDerivAt f f' t) (hpos : 0 < f') :
    ∀ᶠ u in 𝓝[>] t, f t < f u := by
  have hs := hf.tendsto_slope.mono_left (nhdsGT_le_nhdsNE t)
  filter_upwards [hs.eventually (Ioi_mem_nhds hpos), self_mem_nhdsWithin] with u hu htu
  have hdiv : 0 < (f u - f t) / (u - t) := by
    simpa only [slope_def_field] using hu
  exact sub_pos.mp ((div_pos_iff_of_pos_right (sub_pos.mpr htu)).mp hdiv)

/-- Finite lower envelopes increase to the right when every active branch has
strictly positive derivative. Inactive branches only need continuity. -/
lemma finite_minimum_eventually_lt_right {ι : Type uIota} (s : Finset ι)
    (hne : s.Nonempty) (f : ι → ℝ → ℝ) (t : ℝ)
    (hcont : ∀ i ∈ s, ContinuousWithinAt (f i) (Ioi t) t)
    (hderiv : ∀ i ∈ s, s.inf' hne (fun j => f j t) = f i t →
      ∃ v : ℝ, HasDerivAt (f i) v t ∧ 0 < v) :
    ∀ᶠ u in 𝓝[>] t, s.inf' hne (fun j => f j t) < s.inf' hne (fun j => f j u) := by
  have heach : ∀ i ∈ s, ∀ᶠ u in 𝓝[>] t, s.inf' hne (fun j => f j t) < f i u := by
    intro i hi
    by_cases heq : s.inf' hne (fun j => f j t) = f i t
    · rcases hderiv i hi heq with ⟨v, hv, hpos⟩
      simpa only [heq] using eventually_lt_right_of_hasDerivAt_pos hv hpos
    · have hlt : s.inf' hne (fun j => f j t) < f i t :=
        lt_of_le_of_ne (Finset.inf'_le _ hi) heq
      exact (hcont i hi).eventually (Ioi_mem_nhds hlt)
  filter_upwards [(s.eventually_all).mpr heach] with u hu
  exact (Finset.lt_inf'_iff hne).mpr hu

/-- Adding the same constant commutes with a finite minimum. -/
lemma finite_minimum_add_const {ι : Type uIota} (s : Finset ι) (hne : s.Nonempty)
    (f : ι → ℝ) (c : ℝ) :
    s.inf' hne (fun i => f i + c) = s.inf' hne f + c := by
  apply le_antisymm
  · rcases s.exists_mem_eq_inf' hne f with ⟨i, hi, heq⟩
    rw [heq]
    exact Finset.inf'_le _ hi
  · exact (Finset.le_inf'_iff hne _).mpr fun i hi =>
      by simpa only [add_comm] using add_le_add_right (Finset.inf'_le f hi) c

/-- A finite minimum whose active branches have nonnegative derivatives is
nondecreasing. The left endpoint is included in the derivative hypothesis. -/
theorem finite_minimum_monotoneOn_Icc_of_active_deriv_nonneg
    {ι : Type uIota} (s : Finset ι) (hne : s.Nonempty)
    (f : ι → ℝ → ℝ) (a b : ℝ)
    (hcont : ∀ i ∈ s, ContinuousOn (f i) (Icc a b))
    (hderiv : ∀ t ∈ Ico a b, ∀ i ∈ s,
      s.inf' hne (fun j => f j t) = f i t →
      ∃ v : ℝ, HasDerivAt (f i) v t ∧ 0 ≤ v) :
    MonotoneOn (fun t => s.inf' hne (fun i => f i t)) (Icc a b) := by
  let F : ℝ → ℝ := fun t => s.inf' hne (fun i => f i t)
  have hF : ContinuousOn F (Icc a b) := ContinuousOn.finset_inf'_apply hne hcont
  intro u hu v hv huv
  change F u ≤ F v
  have hpert : ∀ ε : ℝ, 0 < ε → F u + ε * u ≤ F v + ε * v := by
    intro ε hε
    let g : ι → ℝ → ℝ := fun i t => f i t + ε * t
    let G : ℝ → ℝ := fun t => F t + ε * t
    have hG : ContinuousOn G (Icc u v) :=
      (hF.add (continuousOn_const.mul continuousOn_id)).mono
        (Icc_subset_Icc hu.1 hv.2)
    obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr huv) hG
    have htv : t = v := by
      by_contra hne_tv
      have hlt : t < v := lt_of_le_of_ne ht.2 hne_tv
      have htab : t ∈ Ico a b := ⟨hu.1.trans ht.1, hlt.trans_le hv.2⟩
      have hevent : ∀ᶠ z in 𝓝[>] t, G t < G z := by
        have hm := finite_minimum_eventually_lt_right s hne g t
          (fun i hi => ((hcont i hi).add
            (continuousOn_const.mul continuousOn_id) t (Ico_subset_Icc_self htab)).mono_of_mem_nhdsWithin
              (Icc_mem_nhdsGT_of_mem htab))
          (by
            intro i hi hactive
            have hactive' : s.inf' hne (fun j => f j t) = f i t := by
              simpa only [g, finite_minimum_add_const, add_left_inj] using hactive
            obtain ⟨w, hw, hwpos⟩ := hderiv t htab i hi hactive'
            refine ⟨w + ε, ?_, by linarith⟩
            convert! hw.add ((hasDerivAt_id t).const_mul ε) using 1; simp)
        simpa only [g, finite_minimum_add_const, G, F] using hm
      obtain ⟨z, hz, htz⟩ := (hevent.and (Ioc_mem_nhdsGT hlt)).exists
      exact (not_lt_of_ge (hmax ⟨ht.1.trans htz.1.le, htz.2⟩)) hz
    subst t
    exact hmax (left_mem_Icc.mpr huv)
  have hlim : ContinuousWithinAt (fun ε : ℝ => F v + ε * (v - u)) (Ioi 0) 0 := by
    fun_prop
  have hle : ∀ ε ∈ Ioi (0 : ℝ), F u ≤ F v + ε * (v - u) := by
    intro ε hε
    have := hpert ε hε
    nlinarith
  have := ContinuousWithinAt.closure_le (by simp : (0 : ℝ) ∈ closure (Ioi 0))
    continuousWithinAt_const hlim hle
  simpa using this

/-- Endpoint-continuous version: no derivatives are required at the endpoints. -/
theorem finite_minimum_monotoneOn_Icc_of_active_deriv_nonneg_Ioo
    {ι : Type uIota} (s : Finset ι) (hne : s.Nonempty)
    (f : ι → ℝ → ℝ) (a b : ℝ)
    (hcont : ∀ i ∈ s, ContinuousOn (f i) (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, ∀ i ∈ s,
      s.inf' hne (fun j => f j t) = f i t →
      ∃ v : ℝ, HasDerivAt (f i) v t ∧ 0 ≤ v) :
    MonotoneOn (fun t => s.inf' hne (fun i => f i t)) (Icc a b) := by
  let F : ℝ → ℝ := fun t => s.inf' hne (fun i => f i t)
  have hF : ContinuousOn F (Icc a b) := ContinuousOn.finset_inf'_apply hne hcont
  intro u hu v hv huv
  change F u ≤ F v
  rcases eq_or_lt_of_le huv with rfl | huv
  · exact le_rfl
  have hle : ∀ t ∈ Ioo u v, F t ≤ F v := by
    intro t ht
    have htv : t ≤ v := ht.2.le
    have hat : a < t := hu.1.trans_lt ht.1
    have hm := finite_minimum_monotoneOn_Icc_of_active_deriv_nonneg s hne f t v
      (fun i hi => (hcont i hi).mono (Icc_subset_Icc hat.le hv.2))
      (fun r hr i hi hactive => hderiv r ⟨hat.trans_le hr.1, hr.2.trans_le hv.2⟩
        i hi hactive)
    exact hm (left_mem_Icc.mpr htv) (right_mem_Icc.mpr htv) htv
  exact ContinuousWithinAt.closure_le
    (by rw [closure_Ioo huv.ne]; exact left_mem_Icc.mpr huv.le)
    ((hF u hu).mono (Ioo_subset_Icc_self.trans (Icc_subset_Icc hu.1 hv.2)))
    continuousWithinAt_const hle

end Problem326

end OAI
