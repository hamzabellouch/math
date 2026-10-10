import OAI.MeasureTheory.Falconer.Angular.GraphAngleCharts

namespace OAI

namespace PlanarFalconer
open Set Filter
open scoped ContDiff Topology

theorem graphAngularPullback_eventually_chart {f : ℝ → ℂ}
    (hp : Function.Periodic f (2*Real.pi)) (positive plus : Bool) (c : ℝ)
    {p : Plane × ℝ} (hη : p.1 ≠ 0) :
    graphAngularPullback f plus c =ᶠ[𝓝 p]
      fun q => f (graphAngleCoordinate positive plus q + (if positive then 0 else Real.pi)+c) := by
  have he : ∀ᶠ q : Plane × ℝ in 𝓝 p, q.1 ≠ 0 :=
    continuousAt_fst.eventually_ne hη
  filter_upwards [he] with q hq
  exact graphAngularPullback_chart hp positive plus c hq

theorem graphAngularPullback_contDiffAt {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f (2*Real.pi))
    (plus : Bool) (c : ℝ) {p : Plane × ℝ} (hη : p.1 ≠ 0) :
    ContDiffAt ℝ ∞ (graphAngularPullback f plus c) p := by
  have hw : graphComplexCoordinate p.1 ≠ 0 := by
    intro he
    apply hη
    apply norm_eq_zero.mp
    rw [← graphComplexCoordinate_norm, he, norm_zero]
  have hs : ∃ positive : Bool,
      (if positive then graphComplexCoordinate p.1 else -graphComplexCoordinate p.1)
        ∈ Complex.slitPlane := by
    by_cases hi : (graphComplexCoordinate p.1).im = 0
    · have hr : (graphComplexCoordinate p.1).re ≠ 0 := by
        intro hr
        exact hw (Complex.ext (by simpa using hr) (by simpa using hi))
      rcases lt_or_gt_of_ne hr with hr | hr
      · exact ⟨false, Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using neg_pos.mpr hr))⟩
      · exact ⟨true, Complex.mem_slitPlane_iff.mpr (Or.inl hr)⟩
    · exact ⟨true, Complex.mem_slitPlane_iff.mpr (Or.inr hi)⟩
  obtain ⟨positive,hs⟩ := hs
  have hg : ContDiffAt ℝ ∞ (fun q => graphAngleCoordinate positive plus q +
      (if positive then 0 else Real.pi)+c) p :=
    ((graphAngleCoordinate_contDiffAt positive plus hs).add contDiffAt_const).add contDiffAt_const
  exact (hf.contDiffAt.comp p hg).congr_of_eventuallyEq
    (graphAngularPullback_eventually_chart hp positive plus c hη)

theorem graph_mixed_composition_scale (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (f : ℝ → ℂ), ContDiff ℝ ∞ f →
      Function.Periodic f (2*Real.pi) → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ k ≤ n, ∀ θ, ‖iteratedDeriv k f θ‖ ≤ C*D^k) →
      ∀ (plus : Bool) (c : ℝ) (η : Plane) (z : ℝ),
      ‖η‖ ≤ 8 → |z| ≤ 4 → 1/8 ≤ ‖η‖ →
      ‖iteratedFDeriv ℝ n (graphAngularPullback f plus c) (η,z)‖ ≤ A*C*D^n := by
  choose A hA hb using fun positive plus => compact_frechet_composition_scale
    (graphAngleCompact_isCompact positive)
    (fun p hp => graphAngleCoordinate_contDiffAt positive plus (graphAngleCompact_slit positive hp)) n
  let B := max (max (A true true) (A true false)) (max (A false true) (A false false))
  have hAB (positive plus : Bool) : A positive plus ≤ B := by
    cases positive <;> cases plus <;> dsimp [B] <;> order
  refine ⟨B, (hA true true).trans (hAB true true), ?_⟩
  intro f hf hp C D hC hD hbound plus c η z hhi hz hlo
  obtain ⟨positive,hmem⟩ := graphAngleCompact_cover hhi hz hlo
  let shift : ℝ := (if positive then 0 else Real.pi)+c
  let fshift : ℝ → ℂ := fun t => f (t+shift)
  have hfshift : ContDiff ℝ ∞ fshift := hf.comp (contDiff_id.add contDiff_const)
  have hshift : ∀ k ≤ n, ∀ θ, ‖iteratedDeriv k fshift θ‖ ≤ C*D^k := by
    intro k hk θ
    dsimp [fshift]
    rw [iteratedDeriv_comp_add_const]
    exact hbound k hk _
  have he : graphAngularPullback f plus c =ᶠ[𝓝 (η,z)]
      fshift ∘ graphAngleCoordinate positive plus := by
    have hη : η ≠ 0 := norm_pos_iff.mp (by linarith)
    simpa only [fshift,shift,Function.comp_def,add_assoc] using
      graphAngularPullback_eventually_chart hp positive plus c (p := (η,z)) hη
  rw [(he.iteratedFDeriv ℝ n).eq_of_nhds]
  exact (hb positive plus fshift hfshift C D hC hD hshift (η,z) hmem).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hAB positive plus) hC)
      (pow_nonneg (zero_le_one.trans hD) _))

end PlanarFalconer

end OAI
