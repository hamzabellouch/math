import OAI.Probability.SLE.Loewner.VanishingHeightRealBounds

namespace OAI

/-! At a finite lifetime, vanishing height and continuity of the driver
force the forward real coordinate to approach the driver. -/
noncomputable section
open Set Filter
open scoped Topology

namespace SLEExactGauge

theorem forward_real_tendsto_driver_of_height_zero {τ : ℝ} (hτ : 0 < τ)
    (X y u : ℝ → ℝ)
    (hX : ContinuousOn X (Ico 0 τ)) (hyc : ContinuousOn y (Ico 0 τ))
    (hXd : ∀ t ∈ Ico 0 τ, HasDerivWithinAt X
      (2*(X t-u t)/((X t-u t)^2+(y t)^2)) (Ici t) t)
    (hyd : ∀ t ∈ Ico 0 τ, HasDerivWithinAt y
      (-2*y t/((X t-u t)^2+(y t)^2)) (Ici t) t)
    (hyp : ∀ t ∈ Ico 0 τ, 0 < y t)
    (hu : ContinuousAt u τ)
    (hlim : Tendsto y (𝓝[<] τ) (𝓝 0)) :
    Tendsto X (𝓝[<] τ) (𝓝 (u τ)) := by
  apply tendsto_order.mpr
  constructor
  · intro c hc
    let d : ℝ := (c+u τ)/2
    have hcd : c < d := by dsimp [d]; linarith
    have hdu : d < u τ := by dsimp [d]; linarith
    have he : ∀ᶠ t in 𝓝[<] τ, d < u t :=
      (hu.tendsto.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds hdu)
    obtain ⟨l,hl,hle⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp he
    filter_upwards [Ioo_mem_nhdsLT (max_lt hl hτ)] with a ha
    have hasub : Ico a τ ⊆ Ico 0 τ :=
      fun t ht => ⟨(le_max_right l 0).trans (ha.1.le.trans ht.1),ht.2⟩
    have hh := future_driver_lower_le_real_of_height_zero ha.2 X y u
      (hX.mono hasub) (hyc.mono hasub)
      (fun t ht => hXd t (hasub ht)) (fun t ht => hyd t (hasub ht))
      (fun t ht => hyp t (hasub ht))
      (fun t ht => (hle ⟨(le_max_left l 0).trans_lt (ha.1.trans_le ht.1),ht.2⟩).le) hlim
    exact hcd.trans_le hh
  · intro c hc
    let d : ℝ := (c+u τ)/2
    have hdc : d < c := by dsimp [d]; linarith
    have hud : u τ < d := by dsimp [d]; linarith
    have he : ∀ᶠ t in 𝓝[<] τ, u t < d :=
      (hu.tendsto.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hud)
    obtain ⟨l,hl,hle⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp he
    filter_upwards [Ioo_mem_nhdsLT (max_lt hl hτ)] with a ha
    have hasub : Ico a τ ⊆ Ico 0 τ :=
      fun t ht => ⟨(le_max_right l 0).trans (ha.1.le.trans ht.1),ht.2⟩
    have hh := real_le_future_driver_bound_of_height_zero ha.2 X y u
      (hX.mono hasub) (hyc.mono hasub)
      (fun t ht => hXd t (hasub ht)) (fun t ht => hyd t (hasub ht))
      (fun t ht => hyp t (hasub ht))
      (fun t ht => (hle ⟨(le_max_left l 0).trans_lt (ha.1.trans_le ht.1),ht.2⟩).le) hlim
    exact hh.trans_lt hdc

end SLEExactGauge

end

end OAI
