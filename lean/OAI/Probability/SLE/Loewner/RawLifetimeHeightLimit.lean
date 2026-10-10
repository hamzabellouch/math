import OAI.Probability.SLE.Loewner.RawHeightContinuation

namespace OAI

/-! The height of a raw point tends to zero at its finite lifetime.
A positive limiting height would continue the exact cutoff trajectory. -/
noncomputable section
open Set Filter Complex
open scoped Topology

namespace SLEExactGauge.Target

theorem flow_height_tendsto_zero_at_lifetime
    (b : Driver) (z : ℂ) (hz : z ∈ upperHalfPlane) {τ : ℝ} (hτ : 0 < τ)
    (hsurvive : ∀ t, 0 ≤ t → t < τ → Surviving 1 b z t)
    (hdead : ¬Surviving 1 b z τ) :
    Tendsto (fun t => (flow 1 b z t).im) (𝓝[<] τ) (𝓝 0) := by
  let f (t : ℝ) := (flow 1 b z t).im
  have hp (t : ℝ) (ht : t ∈ Ioo 0 τ) : 0 < f t :=
    surviving_flow_mem_upperHalfPlane 1 b z t ht.1.le (hsurvive t ht.1.le ht.2)
  have hmono : AntitoneOn f (Ioo 0 τ) := by
    intro s hs t ht hst
    exact flow_height_antitone_of_survival b z ht.1.le (hsurvive t ht.1.le ht.2)
      ⟨hs.1.le,hst⟩ ⟨ht.1.le,le_rfl⟩ hst
  have hne : (Ioo (0 : ℝ) τ).Nonempty := nonempty_Ioo.mpr hτ
  have himage : (f '' Ioo 0 τ).Nonempty := hne.image f
  have hbelow : BddBelow (f '' Ioo 0 τ) := by
    refine ⟨0,?_⟩
    rintro y ⟨t,ht,rfl⟩
    exact (hp t ht).le
  have hy : 0 ≤ sInf (f '' Ioo 0 τ) := by
    apply le_csInf himage
    rintro y ⟨t,ht,rfl⟩
    exact (hp t ht).le
  have hmin (t : ℝ) (ht : t ∈ Ioo 0 τ) : sInf (f '' Ioo 0 τ) ≤ f t :=
    csInf_le hbelow ⟨t,ht,rfl⟩
  have hzero : sInf (f '' Ioo 0 τ)=0 := by
    apply le_antisymm _ hy
    by_contra hn
    have hyp : 0 < sInf (f '' Ioo 0 τ) := lt_of_not_ge hn
    apply hdead
    apply survives_of_uniform_height_before b z hz hτ hyp
      (fun t ht => hsurvive t ht.1 ht.2)
    intro t ht
    by_cases ht0 : t=0
    · subst t
      have hhalf : τ/2 ∈ Ioo (0 : ℝ) τ := ⟨half_pos hτ,half_lt_self hτ⟩
      exact (hmin _ hhalf).trans
        (flow_height_antitone_of_survival b z (half_pos hτ).le
          (hsurvive _ (half_pos hτ).le (half_lt_self hτ))
          ⟨le_rfl,(half_pos hτ).le⟩ ⟨(half_pos hτ).le,le_rfl⟩ (half_pos hτ).le)
    · exact hmin t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),ht.2⟩
  simpa only [hzero] using hmono.tendsto_nhdsWithin_Ioo_left hne hbelow

end SLEExactGauge.Target

end

end OAI
