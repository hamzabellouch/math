import OAI.Probability.SLE.Loewner.RawForwardHeight
import OAI.Probability.SLE.Geometry.ComplexLipschitzExtension

namespace OAI

/-! A raw forward flow whose height stays uniformly positive survives
the limiting finite time. -/
noncomputable section
open Set Filter Complex
open scoped Topology

namespace SLEExactGauge.Target

theorem survives_of_uniform_height_before (b : Driver) (z : ℂ) (hz : z ∈ upperHalfPlane)
    {T m : ℝ} (hT : 0 < T) (hm : 0 < m)
    (hs : ∀ t ∈ Ico 0 T, Surviving 1 b z t)
    (hh : ∀ t ∈ Ico 0 T, m ≤ (flow 1 b z t).im) :
    Surviving 1 b z T := by
  have hlater (t : ℝ) (ht : t ∈ Ico 0 T) :
      HasDerivWithinAt (flow 1 b z)
        ((a 1 : ℂ)/(flow 1 b z t-(driverValue b t : ℂ))) (Ici 0) t := by
    let S : ℝ := (t+T)/2
    have htS : t < S := by dsimp [S]; linarith [ht.2]
    have hST : S < T := by dsimp [S]; linarith [ht.2]
    exact flow_hasDerivWithinAt_of_later_survival 1 b z t S ht.1 htS
      (hs S ⟨ht.1.trans htS.le,hST⟩)
  have hd (t : ℝ) (ht : t ∈ Ico 0 T) : HasDerivWithinAt (flow 1 b z)
      ((a 1 : ℂ)/(flow 1 b z t-(driverValue b t : ℂ))) (Ico 0 T) t :=
    (hlater t ht).mono Ico_subset_Ici_self
  have hnorm (t : ℝ) (ht : t ∈ Ico 0 T) :
      ‖(a 1 : ℂ)/(flow 1 b z t-(driverValue b t : ℂ))‖ ≤ 2/m := by
    have hden : m ≤ ‖flow 1 b z t-(driverValue b t : ℂ)‖ := by
      calc
        m ≤ (flow 1 b z t).im := hh t ht
        _ ≤ |(flow 1 b z t-(driverValue b t : ℂ)).im| := by
          simp only [Complex.sub_im,Complex.ofReal_im,sub_zero]
          exact le_abs_self _
        _ ≤ _ := Complex.abs_im_le_norm _
    calc
      _ = 2/‖flow 1 b z t-(driverValue b t : ℂ)‖ := by norm_num [norm_div,a]
      _ ≤ 2/m := div_le_div_of_nonneg_left (by norm_num) hm hden
  have hLip : LipschitzOnWith ⟨2/m,by positivity⟩ (flow 1 b z) (Ico 0 T) := by
    apply (convex_Ico (0 : ℝ) T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hd
    intro t ht
    exact_mod_cast hnorm t ht
  obtain ⟨g,hg,hge⟩ := exists_continuous_complex_extension (flow 1 b z) hLip
  have hheight : ∀ t ∈ Icc 0 T, m ≤ (g t).im := by
    have hc : IsClosed {t : ℝ | m ≤ (g t).im} :=
      isClosed_le continuous_const (Complex.continuous_im.comp hg)
    have hsub : Ico 0 T ⊆ {t : ℝ | m ≤ (g t).im} := by
      intro t ht
      change m ≤ (g t).im
      rw [hge ht]
      exact hh t ht
    have hcsub := closure_minimal hsub hc
    rw [closure_Ico hT.ne] at hcsub
    exact fun t ht => hcsub ht
  have hzero : g 0=z := (hge ⟨le_rfl,hT⟩).trans (flow_zero 1 b z hz)
  apply surviving_of_positive_trajectory 1 b z T hT.le g hg.continuousOn hzero m hm hheight
  intro t ht
  have he : g =ᶠ[𝓝[Ici t] t] flow 1 b z := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds ht.2)] with s hs hsT
    exact hge ⟨ht.1.trans hs,hsT⟩
  have hv := hge ht
  have hh' := ((hlater t ht).mono (Ici_subset_Ici.mpr ht.1)).congr_of_eventuallyEq he hv
  simpa only [← hv] using hh'

end SLEExactGauge.Target

end

end OAI
