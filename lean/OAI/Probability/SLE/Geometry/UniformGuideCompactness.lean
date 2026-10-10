import OAI.Probability.SLE.Geometry.PublishedConformalCompactness
import OAI.Probability.SLE.Geometry.GuideTipCollapse

namespace OAI

/-! Uniform access-guide collapse from the univalent normal-family
theorem and conformal localization. This supplies the boundary control
in `es:guide-compactness` under waypoint normalization bounds. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

theorem uniform_tip_collapse_of_published_compactness
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (hpublished : PublishedHalfPlaneUnivalentCompactness)
    (Fₙ : ℕ → ℂ → ℂ) (Fbar : ℕ → ℂ → OnePoint ℂ)
    (hFn : ∀ n, DifferentiableOn ℂ (Fₙ n) upperHalfPlane)
    (hinjn : ∀ n, InjOn (Fₙ n) upperHalfPlane)
    (hbar : ∀ n, ContinuousOn (Fbar n) {z : ℂ | 0 ≤ z.im})
    (hext : ∀ n z, z ∈ upperHalfPlane → Fbar n z = (Fₙ n z : OnePoint ℂ))
    (zₙ aₙ : ℕ → ℂ) (s m M : ℝ) (hs : 0 < s) (hm : 0 < m)
    (hz : ∀ n, ‖zₙ n‖ = 1 ∧ s ≤ (zₙ n).im)
    (hwaypoint : ∀ n, ‖Fₙ n (zₙ n)‖ ≤ M)
    (hderiv : ∀ n, m ≤ ‖deriv (Fₙ n) (zₙ n)‖ ∧ ‖deriv (Fₙ n) (zₙ n)‖ ≤ M)
    (htip : ∀ n, ‖aₙ n‖ ≤ M)
    (β : ℕ → ℝ → ℂ) (T C : ℝ) (hT : 0 < T) (hC : 0 < C)
    (hβ : ∀ n, ContinuousOn (β n) (Icc 0 T)) (hβ0 : ∀ n, β n 0 = 0)
    (hβH : ∀ n t, t ∈ Icc 0 T → 0 ≤ (β n t).im)
    (himage : ∀ n t, t ∈ Icc 0 T → ∃ w : ℂ,
      Fbar n (β n t) = (w : OnePoint ℂ) ∧ ‖w - aₙ n‖ ≤ C * t) :
    ∀ ε : ℝ, 0 < ε → ∃ h : ℝ, 0 < h ∧ h ≤ T ∧
      ∀ n t, t ∈ Icc 0 h → ‖β n t‖ < ε := by
  intro ε hε
  by_contra! hnone
  let h : ℕ → ℝ := fun j => min T (1 / ((j : ℝ) + 1))
  have hh : ∀ j, 0 < h j := fun j => lt_min hT (by positivity)
  have hhT : ∀ j, h j ≤ T := fun _ => min_le_left _ _
  have hbad : ∀ j, ∃ n t, t ∈ Icc 0 (h j) ∧ ε ≤ ‖β n t‖ :=
    fun j => hnone (h j) (hh j) (hhT j)
  choose index t ht hlarge using hbad
  have htlim : Tendsto t atTop (𝓝 0) :=
    squeeze_zero (fun j => (ht j).1)
      (fun j => (ht j).2.trans (min_le_right _ _))
      tendsto_one_div_add_atTop_nhds_zero_nat
  have htipball : ∀ j, aₙ (index j) ∈ closedBall 0 M := by
    intro j
    simpa only [mem_closedBall, dist_zero_right] using htip (index j)
  obtain ⟨a, _, φ, hφ, halim⟩ := (isCompact_closedBall (0 : ℂ) M).tendsto_subseq htipball
  obtain ⟨ψ, F, hψ, hF, hinj, _hne, hconv⟩ := hpublished
    (fun j => Fₙ (index (φ j))) (fun j => zₙ (index (φ j))) s m M hs hm
    (fun j => hFn _) (fun j => hinjn _) (fun j => hz _)
    (fun j => hwaypoint _) (fun j => hderiv _)
  let seq : ℕ → ℕ := fun j => index (φ (ψ j))
  have halim' : Tendsto (fun j => aₙ (seq j)) atTop (𝓝 a) := by
    simpa only [Function.comp_def, seq] using halim.comp hψ.tendsto_atTop
  have htlim' : Tendsto (fun j => t (φ (ψ j))) atTop (𝓝 0) :=
    htlim.comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop)
  obtain ⟨δ, hδ, _, hδbound⟩ := uniform_tip_collapse P κ hκ hκ8 γ hSLE
    (fun j => Fₙ (seq j)) (fun j => Fbar (seq j)) F
    (fun j => hFn _) (fun j => hinjn _) (fun j => hbar _) (fun j => hext _)
    hconv hF.continuousOn hinj (fun j => aₙ (seq j)) a halim'
    (fun j => β (seq j)) T C hT hC (fun j => hβ _) (fun j => hβ0 _)
    (fun j => hβH _) (fun j => himage _) ε hε
  obtain ⟨j, hj⟩ := (htlim'.eventually (Iio_mem_nhds hδ)).exists
  have htj : t (φ (ψ j)) ∈ Icc 0 δ := ⟨(ht _).1, hj.le⟩
  exact (not_lt_of_ge (hlarge _)) (hδbound j _ htj)

end SLEExactGauge

end

end OAI
