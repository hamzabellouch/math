import OAI.Probability.SLE.Gauge.ConformalSausageTransfer
import Mathlib.Analysis.Complex.LocallyUniformLimit

namespace OAI

/-! Uniform sausage transport on retained compact parameter sets. Local
uniform convergence supplies derivative bounds and a common positive mesh;
the actual Jacobian and convex local patches supply the area comparison. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

theorem eventually_derivative_norm_bounds_on_compact
    (Fₙ : ℕ → ℂ → ℂ) (F : ℂ → ℂ)
    (hFn : ∀ n, DifferentiableOn ℂ (Fₙ n) upperHalfPlane)
    (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hconv : TendstoLocallyUniformlyOn Fₙ F atTop upperHalfPlane)
    (K : Set ℂ) (hK : IsCompact K) (hKn : K.Nonempty) (hKH : K ⊆ upperHalfPlane)
    (hne : ∀ z ∈ K, deriv F z ≠ 0) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n in atTop,
      ∀ z ∈ K, c ≤ ‖deriv (Fₙ n) z‖ ∧ ‖deriv (Fₙ n) z‖ ≤ C := by
  have hc : ContinuousOn (fun z => ‖deriv F z‖) K :=
    ((hF.deriv isOpen_upperHalfPlane).continuousOn.mono hKH).norm
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hKn hc
  let c₀ := ‖deriv F z₀‖
  have hc₀ : 0 < c₀ := norm_pos_iff.mpr (hne z₀ hz₀)
  obtain ⟨C₀, hC₀, hmax⟩ :=
    (hK.image_of_continuousOn ((hF.deriv isOpen_upperHalfPlane).continuousOn.mono hKH)).isBounded.exists_pos_norm_lt
  have hderconv := hconv.deriv (Eventually.of_forall hFn) isOpen_upperHalfPlane
  have hu : TendstoUniformlyOn (fun n => deriv (Fₙ n)) (deriv F) atTop K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp (hderconv.mono hKH)
  have he : ∀ᶠ n in atTop, ∀ z ∈ K,
      dist (deriv F z) (deriv (Fₙ n) z) < min (c₀ / 2) 1 :=
    hu _ (Metric.dist_mem_uniformity (lt_min (by positivity) (by norm_num)))
  refine ⟨c₀ / 2, C₀ + 1, by positivity, by positivity, ?_⟩
  filter_upwards [he] with n hn
  intro z hz
  have hd := hn z hz
  have hlow := hmin hz
  change c₀ ≤ ‖deriv F z‖ at hlow
  have hup := hmax _ (mem_image_of_mem (deriv F) hz)
  have hdiff := norm_sub_norm_le (deriv F z) (deriv (Fₙ n) z)
  have hdiff' := norm_sub_norm_le (deriv (Fₙ n) z) (deriv F z)
  rw [← dist_eq_norm] at hdiff hdiff'
  rw [dist_comm] at hdiff'
  constructor <;> dsimp only [c₀] at * <;>
    linarith [min_le_left (c₀ / 2) 1, min_le_right (c₀ / 2) 1]

theorem eventually_image_compact_subset_open
    (Fₙ : ℕ → ℂ → ℂ) (F : ℂ → ℂ)
    (hconv : TendstoLocallyUniformlyOn Fₙ F atTop upperHalfPlane)
    (hF : ContinuousOn F upperHalfPlane)
    (K : Set ℂ) (hK : IsCompact K) (hKH : K ⊆ upperHalfPlane)
    (R : Set ℂ) (hR : IsOpen R) (himage : F '' K ⊆ R) :
    ∀ᶠ n in atTop, Fₙ n '' K ⊆ R := by
  have hFK : IsCompact (F '' K) := hK.image_of_continuousOn (hF.mono hKH)
  obtain ⟨ε, hε, hεR⟩ := hFK.exists_thickening_subset_open hR himage
  have hu : TendstoUniformlyOn Fₙ F atTop K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp (hconv.mono hKH)
  have he : ∀ᶠ n in atTop, ∀ z ∈ K, dist (F z) (Fₙ n z) < ε :=
    hu _ (Metric.dist_mem_uniformity hε)
  filter_upwards [he] with n hn
  rintro w ⟨z, hz, rfl⟩
  apply hεR
  apply mem_thickening_iff.mpr
  exact ⟨F z, mem_image_of_mem F hz, by simpa only [dist_comm] using hn z hz⟩

/-- All sufficiently late conformal maps transport every interval retained
in `K`, at every sufficiently small deterministic mesh, with common constants.
The compact set itself need not be convex. -/
theorem eventually_compact_sausage_transfer
    (κ : ℝ) (Fₙ : ℕ → ℂ → ℂ) (F : ℂ → ℂ)
    (hFn : ∀ n, DifferentiableOn ℂ (Fₙ n) upperHalfPlane)
    (hinj : ∀ n, InjOn (Fₙ n) upperHalfPlane)
    (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hne : ∀ z ∈ upperHalfPlane, deriv F z ≠ 0)
    (hconv : TendstoLocallyUniformlyOn Fₙ F atTop upperHalfPlane)
    (K : Set ℂ) (hK : IsCompact K) (hKn : K.Nonempty) (hKH : K ⊆ upperHalfPlane)
    (R : Set ℂ) (hR : IsOpen R) (himage : F '' K ⊆ R) :
    ∃ c ell v₀ : ℝ, 0 < c ∧ 0 < ell ∧ 0 < v₀ ∧
      ∀ᶠ n in atTop, ∀ (γ : ℝ≥0 → ℂ) (s t : ℝ≥0), γ '' Icc s t ⊆ K →
        ∀ v : ℝ, 0 < v → v < v₀ →
        ENNReal.ofReal (c ^ 2 * ell ^ codimension κ) *
          sourceSausageMass κ γ s t (ell * v) ≤
        ENNReal.ofReal (v ^ (-codimension κ)) *
          volume (R ∩ sourceSausageSet (fun u => Fₙ n (γ u)) s t v) := by
  let U := upperHalfPlane ∩ F ⁻¹' R
  have hU : IsOpen U := hF.continuousOn.isOpen_inter_preimage isOpen_upperHalfPlane hR
  have hKU : K ⊆ U := fun z hz => ⟨hKH hz, himage (mem_image_of_mem F hz)⟩
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  let L := cthickening δ K
  have hL : IsCompact L := hK.cthickening
  have hKL : K ⊆ L := self_subset_cthickening K
  have hLn : L.Nonempty := hKn.mono hKL
  have hLH : L ⊆ upperHalfPlane := fun z hz => (hδU hz).1
  have hLR : F '' L ⊆ R := by
    rintro w ⟨z, hz, rfl⟩
    exact (hδU hz).2
  obtain ⟨c, C, hc, hC, hbounds⟩ := eventually_derivative_norm_bounds_on_compact
    Fₙ F hFn hF hconv L hL hLn hLH (fun z hz => hne z (hLH hz))
  have hmaps := eventually_image_compact_subset_open Fₙ F hconv hF.continuousOn
    L hL hLH R hR hLR
  let ell := min 1 (1 / (C + 1))
  have hell : 0 < ell := lt_min zero_lt_one (by positivity)
  have hell1 : ell ≤ 1 := min_le_left _ _
  have hscale : C * ell ≤ 1 := by
    have he := (le_div_iff₀ (by positivity : 0 < C + 1)).mp (min_le_right 1 (1 / (C + 1)))
    dsimp only [ell] at *
    nlinarith
  refine ⟨c, ell, δ, hc, hell, hδ, ?_⟩
  filter_upwards [hbounds, hmaps] with n hn hmap
  intro γ s t hγK v hv hvδ
  have hsmall : ell * v < δ := (mul_le_of_le_one_left hv.le hell1).trans_lt hvδ
  have hSL : sourceSausageSet γ s t (ell * v) ⊆ L := by
    rintro z ⟨u, hu, hdist⟩
    exact mem_cthickening_of_dist_le z (γ u) δ K
      (hγK (mem_image_of_mem γ hu)) (hdist.le.trans hsmall.le)
  apply sourceSausageMass_conformal_transfer κ (Fₙ n) (deriv (Fₙ n)) γ s t R
    hc.le hv hell ((hinj n).mono (hSL.trans hLH))
    (fun z hz => ((hFn n).differentiableAt (isOpen_upperHalfPlane.mem_nhds (hLH (hSL hz)))).hasDerivAt)
    (fun z hz => (hn z (hSL hz)).1) ⟨C, hC.le⟩ hscale
    (image_mono hSL |>.trans hmap)
  rintro z ⟨u, hu, hdist⟩
  have huK := hγK (mem_image_of_mem γ hu)
  have hballL : closedBall (γ u) δ ⊆ L := closedBall_subset_cthickening huK δ
  refine ⟨u, hu, hdist, closedBall (γ u) δ, convex_closedBall _ _,
    mem_closedBall.mpr (hdist.le.trans hsmall.le), mem_closedBall_self hδ.le, ?_, ?_⟩
  · intro w hw
    exact ((hFn n).differentiableAt
      (isOpen_upperHalfPlane.mem_nhds (hLH (hballL hw)))).hasDerivAt.hasDerivWithinAt
  · intro w hw
    exact_mod_cast (hn w (hballL hw)).2

end SLEExactGauge

end

end OAI
