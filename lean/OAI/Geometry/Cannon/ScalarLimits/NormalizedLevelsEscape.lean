import Mathlib
import OAI.Geometry.Cannon.ScalarLimits.EscapingLevelsAlong
import OAI.Geometry.Cannon.Flows.FarDiam

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
open Set MeasureTheory
open scoped BigOperators
open Set Topology
open Set Metric Filter Topology

namespace CannonComparison

open Set Metric Filter Topology CannonMagnification

theorem normalized_levels_escape {X : Type*} [MetricSpace X]
    (H : ℕ → X → ℝ) (Ω : Set X)
    (hH : ∀ n y, y ∈ Ω → H n y ∈ Icc (0:ℝ) 1)
    (d₁ : ℝ) (hd₁ : 0 < d₁)
    (hlevels : ∀ n τ, τ ∈ Ioo (0:ℝ) 1 →
      ∃ A : Set X, IsCompact A ∧ IsConnected A ∧ d₁ ≤ diam A ∧
        (∀ y ∈ A, H n y = τ) ∧
        ∀ v w : X, ∀ γ : Path v w, range γ ⊆ Ω → H n v < τ → τ < H n w →
          (A ∩ range γ).Nonempty)
    (h : ℕ → X ≃ₜ X) (x : ℕ → X) (z₀ b : X) (r : ℕ → ℝ)
    (C L d₀ : ℝ) (hC : 0 ≤ C) (hd₀ : 0 < d₀)
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hexp : ∀ n, Expansion (h n) (x n) (r n) C L)
    (hz₀ : ∀ n, d₀ ≤ dist (x n) z₀)
    (hdiam : ∀ y z : X, dist y z ≤ 1)
    (hb : Tendsto (fun n => h n z₀) atTop (𝓝 b))
    (c σ : ℕ → ℝ) (hσ : ∀ n, 0 < σ n) (W : X → ℝ)
    (hpre : ∀ K : Set X, IsCompact K → b ∉ K →
      ∀ᶠ n in atTop, (h n).symm '' K ⊆ Ω)
    (hlim : ∀ K : Set X, IsCompact K → b ∉ K →
      TendstoUniformlyOn (fun n z => (H n ((h n).symm z)-c n)/σ n) W atTop K) :
    EscapingLevelsAlong (fun n z => (H n ((h n).symm z)-c n)/σ n) W b := by
  intro v w γ a d ρ hγ hva had hdw hρ
  have hP : IsCompact (range γ) := isCompact_range γ.continuous
  have hbP : b ∉ range γ := fun h => by simpa using hγ h
  have hvP : v ∈ range γ := ⟨0,γ.source⟩
  have hwP : w ∈ range γ := ⟨1,γ.target⟩
  have hvl : Tendsto (fun n => (H n ((h n).symm v)-c n)/σ n) atTop (𝓝 (W v)) :=
    (hlim _ hP hbP).tendsto_at hvP
  have hwl : Tendsto (fun n => (H n ((h n).symm w)-c n)/σ n) atTop (𝓝 (W w)) :=
    (hlim _ hP hbP).tendsto_at hwP
  filter_upwards [hvl.eventually_lt_const hva,hwl.eventually_const_lt hdw,hpre _ hP hbP,
    wide_level_images_escape h x z₀ b r C L d₁ d₀ hC hd₁ hd₀ hr hrlim hexp hz₀ hdiam hb ρ hρ]
    with n hnv hnw hnpre hnesc
  intro t ht
  let τ := c n+σ n*t
  have hvτ : H n ((h n).symm v) < τ := by
    have hh := (div_lt_iff₀ (hσ n)).mp (hnv.trans_le ht.1)
    dsimp [τ]; nlinarith
  have hτw : τ < H n ((h n).symm w) := by
    have hh := (lt_div_iff₀ (hσ n)).mp (ht.2.trans_lt hnw)
    dsimp [τ]; nlinarith
  have hτ : τ ∈ Ioo (0:ℝ) 1 :=
    ⟨(hH n _ (hnpre (mem_image_of_mem _ hvP))).1.trans_lt hvτ,
      hτw.trans_le (hH n _ (hnpre (mem_image_of_mem _ hwP))).2⟩
  obtain ⟨A,hA,hAconn,hAd,hAlev,hAhit⟩ := hlevels n τ hτ
  let γ' := γ.map (h n).symm.continuous
  have hγ' : range γ' ⊆ Ω := by
    rintro _ ⟨s,rfl⟩
    exact hnpre (mem_image_of_mem _ (mem_range_self s))
  obtain ⟨y,hyA,s,hs⟩ := hAhit _ _ γ' hγ' hvτ hτw
  refine ⟨(h n) '' A,hA.image (h n).continuous,
    hAconn.image _ (h n).continuous.continuousOn,?_,?_,hnesc A hAd⟩
  · refine ⟨h n y,mem_image_of_mem _ hyA,s,?_⟩
    have hh : (h n).symm (γ s) = y := hs
    exact ((h n).apply_symm_apply (γ s)).symm.trans (congrArg (h n) hh)
  · rintro z ⟨y,hy,rfl⟩
    rw [(h n).symm_apply_apply,hAlev y hy]
    apply (div_eq_iff (ne_of_gt (hσ n))).mpr
    dsimp [τ]
    ring

end CannonComparison

end
end
end
end
end
end
end
end
end
end

end OAI
