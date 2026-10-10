import OAI.Geometry.Perimeter.Regularity.WeakHarmonicRadial
import OAI.Geometry.Perimeter.Regularity.HarmonicApproxIdentity

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Convolution InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n : ℕ}

def harmonicRegularization (u : Euc n → ℝ) (t : ℝ) : Euc n → ℝ :=
  scaledHarmonicKernel t ⋆[lsmul ℝ ℝ,volume] u

theorem harmonicRegularization_eq_integral (u : Euc n → ℝ) (t : ℝ) (c : Euc n) :
    harmonicRegularization u t c = ∫ x, scaledHarmonicKernel t (c-x)*u x := by
  rw [harmonicRegularization,convolution_eq_swap]
  rfl

theorem harmonicRegularization_contDiff {u : Euc n → ℝ} (hu : LocallyIntegrable u volume)
    {t : ℝ} (ht : 0 < t) : ContDiff ℝ ∞ (harmonicRegularization u t) := by
  have hc : HasCompactSupport (scaledHarmonicKernel (n := n) t) :=
    (isCompact_closedBall 0 (1/t)).of_isClosed_subset (isClosed_tsupport _)
      (scaledHarmonicKernel_tsupport ht)
  exact hc.contDiff_convolution_left _ (scaledHarmonicKernel_contDiff t) hu

theorem harmonicRegularization_eq_radial (u : Euc n → ℝ) (c : Euc n)
    {R t : ℝ} (hR : 0 < R) (ht : 1/R < t) :
    harmonicRegularization u t c =
      (harmonicKernelMass n)⁻¹ * ∫ x in Metric.ball c R,
        u x*radialDensityIntegrand c n (densityProfile 1) t x := by
  have ht0 : 0 < t := (one_div_pos.mpr hR).trans ht
  have htR : 1/t < R := (div_lt_iff₀ ht0).mpr (by
    have := (div_lt_iff₀ hR).mp ht; nlinarith)
  have hs : Function.support (fun x ↦ scaledHarmonicKernel t (c-x)*u x) ⊆ Metric.ball c R :=
    (Function.support_mul_subset_left _ _).trans
      ((shifted_scaledHarmonicKernel_support ht0 c).trans (Metric.closedBall_subset_ball htR))
  rw [harmonicRegularization_eq_integral,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦
      Function.notMem_support.mp (fun hh ↦ hx (hs hh))), ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_ball
  intro x hx
  dsimp only
  rw [scaledHarmonicKernel_eq ht0,norm_sub_rev]
  dsimp only [radialDensityIntegrand]
  ring

theorem weakHarmonic_regularization_eq {u : Euc n → ℝ} {U : Set (Euc n)}
    (hu : LocallyIntegrable u volume) (hw : WeakHarmonicOn u U) (hn : 0 < n)
    (c : Euc n) {R : ℝ} (hR : 0 < R) (hU : Metric.ball c R ⊆ U)
    {s t : ℝ} (hs : 1/R < s) (ht : 1/R < t) :
    harmonicRegularization u s c = harmonicRegularization u t c := by
  rw [harmonicRegularization_eq_radial u c hR hs,harmonicRegularization_eq_radial u c hR ht,
    weakHarmonic_radial_average_eq hw hn c hR
      ((hu.integrableOn_isCompact (isCompact_closedBall c R)).mono_set Metric.ball_subset_closedBall)
      hU 1 hs ht]

theorem weakHarmonic_ae_eq_regularization {u : Euc n → ℝ} {U : Set (Euc n)}
    (hu : LocallyIntegrable u volume) (hw : WeakHarmonicOn u U) (hn : 0 < n) :
    ∀ᵐ c ∂volume, ∀ R : ℝ, 0 < R → Metric.ball c R ⊆ U →
      ∀ t : ℝ, 1/R < t → u c = harmonicRegularization u t c := by
  filter_upwards [scaledHarmonicKernel_ae_tendsto hu] with c hc
  intro R hR hU t ht
  have hl : Tendsto (fun i : ℕ ↦ harmonicRegularization u ((i:ℝ)+1) c) atTop (𝓝 (u c)) := by
    simpa only [harmonicRegularization_eq_integral] using hc
  obtain ⟨N,hN⟩ := exists_nat_gt (1/R)
  have he : ∀ᶠ i : ℕ in atTop,
      harmonicRegularization u ((i:ℝ)+1) c = harmonicRegularization u t c := by
    filter_upwards [eventually_ge_atTop N] with i hi
    apply weakHarmonic_regularization_eq hu hw hn c hR hU _ ht
    have hni : (N:ℝ) ≤ i := by exact_mod_cast hi
    linarith
  exact tendsto_nhds_unique hl (tendsto_const_nhds.congr' (he.mono (fun _ h ↦ h.symm)))

theorem weakHarmonic_smooth_representative_ball {u : Euc n → ℝ} {U : Set (Euc n)}
    (hu : LocallyIntegrable u volume) (hw : WeakHarmonicOn u U) (hn : 0 < n)
    (c : Euc n) {r : ℝ} (hr : 0 < r) (hU : Metric.ball c (2*r) ⊆ U) :
    ∃ f : Euc n → ℝ, ContDiff ℝ ∞ f ∧
      u =ᵐ[volume.restrict (Metric.ball c r)] f := by
  refine ⟨harmonicRegularization u (2/r),harmonicRegularization_contDiff hu (by positivity),?_⟩
  filter_upwards [ae_restrict_of_ae (weakHarmonic_ae_eq_regularization hu hw hn),
    ae_restrict_mem measurableSet_ball] with x hx hxB
  apply hx r hr _ (2/r) (by exact div_lt_div_of_pos_right (by norm_num) hr)
  intro y hy
  apply hU
  have hxy := dist_triangle y x c
  rw [Metric.mem_ball] at hxB hy ⊢
  linarith

end RPISingularHarnack

end

end OAI
