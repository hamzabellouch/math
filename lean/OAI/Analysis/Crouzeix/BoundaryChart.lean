import Mathlib
import OAI.Analysis.Crouzeix.BoundaryModulus
import OAI.Analysis.Crouzeix.HolomorphicReflection

namespace OAI

/-! Boundary Chart. -/

noncomputable section

open Set Filter Metric Topology Function Complex InnerProductSpace Real

open scoped Classical ComplexConjugate

namespace CrouzeixHilbert.Conformal

structure BoundaryChart (U : Set ℂ) (p : ℂ) where
  e : OpenPartialHomeomorph ℂ ℂ
  zero_mem : (0 : ℂ) ∈ e.source
  at_zero : e 0 = p
  analytic : AnalyticOnNhd ℂ e e.source
  inverse_analytic : AnalyticOnNhd ℂ e.symm e.target
  side : ∀ z ∈ e.source, e z ∈ U ↔ 0 < z.im
  closed_side : ∀ z ∈ e.source, e z ∈ closure U ↔ 0 ≤ z.im

theorem exists_extension_at_boundary {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U (ball 0 1))
    {p : ℂ} (hp : p ∈ frontier U) (c : BoundaryChart U p) :
    ∃ (r : ℝ) (g : ℂ → ℂ), 0 < r ∧ AnalyticOnNhd ℂ g (ball p r) ∧
      EqOn g f (U ∩ ball p r) ∧ deriv g p ≠ 0 := by
  obtain ⟨a, ha, hfa⟩ := hbij.surjOn (mem_ball_self (by norm_num) : (0 : ℂ) ∈ ball 0 1)
  have hpa : p ≠ a := by
    rintro rfl
    exact hp.2 (hU.interior_eq.symm ▸ ha)
  have hχa : ∀ᶠ z in 𝓝 (0 : ℂ), c.e z ≠ a :=
    (c.analytic 0 c.zero_mem).continuousAt.preimage_mem_nhds
      (isClosed_singleton.isOpen_compl.mem_nhds (by simpa only [mem_compl_iff, mem_singleton_iff, c.at_zero] using hpa))
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (c.e.open_source.mem_nhds c.zero_mem) hχa)
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hsub : closedBall (0 : ℂ) r ⊆ c.e.source := fun z hz =>
    (hball ((closedBall_subset_ball (by dsimp [r]; linarith)) hz)).1
  have hne : ∀ z ∈ closedBall (0 : ℂ) r, c.e z ≠ a := fun z hz =>
    (hball ((closedBall_subset_ball (by dsimp [r]; linarith)) hz)).2
  have hfu : ∀ z ∈ closedBall (0 : ℂ) r, 0 < z.im → f (c.e z) ≠ 0 := by
    intro z hz hi he
    exact hne z hz (hbij.injOn ((c.side z (hsub hz)).mpr hi) ha (he.trans hfa.symm))
  let M : ℂ → ℝ := fun z => if z ∈ U then ‖f z‖ else 1
  let u : ℂ → ℝ := fun z => Real.log (M (c.e z))
  have huEq : EqOn u (fun z => Real.log ‖f (c.e z)‖) (upperHalfBall r) := by
    intro z hz
    simp only [u, M, ite_eq_left ((c.side z (hsub (ball_subset_closedBall hz.1))).mpr hz.2)]
  have hχU : MapsTo c.e (upperHalfBall r) U := fun z hz =>
    (c.side z (hsub (ball_subset_closedBall hz.1))).mpr hz.2
  have hfχ : DifferentiableOn ℂ (f ∘ c.e) (upperHalfBall r) :=
    hf.comp (c.analytic.differentiableOn.mono (inter_subset_left.trans (ball_subset_closedBall.trans hsub))) hχU
  have hu : HarmonicOnNhd u (upperHalfBall r) := by
    intro z hz
    have hg := (hfχ.analyticOnNhd (isOpen_upperHalfBall r) z hz).harmonicAt_log_norm
      (hfu z (ball_subset_closedBall hz.1) hz.2)
    exact (harmonicAt_congr_nhds (huEq.eventuallyEq_of_mem ((isOpen_upperHalfBall r).mem_nhds hz))).mpr hg
  have hχclosed : MapsTo c.e (closedUpperHalfBall r) (closure U) := fun z hz =>
    (c.closed_side z (hsub hz.1)).mpr hz.2
  have hMn : ∀ z ∈ closedUpperHalfBall r, M (c.e z) ≠ 0 := by
    intro z hz
    by_cases hi : c.e z ∈ U
    · simp only [M, ite_eq_left hi]
      exact norm_ne_zero_iff.mpr (hfu z hz.1 ((c.side z (hsub hz.1)).mp hi))
    · simp only [M, ite_eq_right hi, ne_eq, one_ne_zero, not_false_eq_true]
  have huc : ContinuousOn u (closedUpperHalfBall r) :=
    ((continuousOn_closed_modulus hU hf hbij).comp
      (c.analytic.continuousOn.mono (inter_subset_left.trans hsub)) hχclosed).log hMn
  have hu0 : ∀ z ∈ closedBall (0 : ℂ) r, z.im = 0 → u z = 0 := by
    intro z hz hi
    have hn : c.e z ∉ U := fun he => (lt_irrefl (0 : ℝ)) (hi ▸ (c.side z (hsub hz)).mp he)
    simp only [u, M, ite_eq_right hn, Real.log_one]
  have hneg : ∀ z ∈ sphere (0 : ℂ) r, 0 < z.im → u z < 0 := by
    intro z hz hi
    have hzU := (c.side z (hsub (sphere_subset_closedBall hz))).mpr hi
    simp only [u, M, ite_eq_left hzU]
    exact Real.log_neg (norm_pos_iff.mpr (hfu z (sphere_subset_closedBall hz) hi))
      (mem_ball_zero_iff.mp (hbij.mapsTo hzU))
  obtain ⟨g, hga, hge, hgd, _⟩ := holomorphic_reflection hr hu huc hu0 hneg hfχ
    (fun z hz => hfu z (ball_subset_closedBall hz.1) hz.2) huEq.symm
  have hpT : p ∈ c.e.target := by simpa only [c.at_zero] using c.e.map_source c.zero_mem
  have hpInv : c.e.symm p = 0 := by simpa only [c.at_zero] using c.e.left_inv c.zero_mem
  have hcont := (c.inverse_analytic p hpT).continuousAt
  have hnb : ∀ᶠ z in 𝓝 p, c.e.symm z ∈ ball 0 r :=
    hcont.preimage_mem_nhds (hpInv.symm ▸ ball_mem_nhds (0 : ℂ) hr)
  obtain ⟨s, hs, hsSub⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (c.e.open_target.mem_nhds hpT) hnb)
  refine ⟨s, g ∘ c.e.symm, hs, ?_, ?_, ?_⟩
  · intro z hz
    exact (hga _ (hsSub hz).2).comp (c.inverse_analytic z (hsSub hz).1)
  · intro z hz
    have hzt := (hsSub hz.2).1
    have hzs := c.e.map_target hzt
    have hi : 0 < (c.e.symm z).im := (c.side _ hzs).mp (by simpa only [c.e.right_inv hzt] using hz.1)
    simpa only [Function.comp_apply, c.e.right_inv hzt] using hge ⟨(hsSub hz.2).2, hi⟩
  · rw [deriv_comp p (hga _ (hpInv.symm ▸ mem_ball_self hr)).differentiableAt
      (c.inverse_analytic p hpT).differentiableAt, hpInv]
    exact mul_ne_zero hgd (deriv_ne_zero_of_injOn c.e.open_target
      c.inverse_analytic.differentiableOn c.e.symm.injOn hpT)

end CrouzeixHilbert.Conformal

end

end OAI
