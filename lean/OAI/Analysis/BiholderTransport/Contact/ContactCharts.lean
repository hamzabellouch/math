import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.SmoothUpperTest
import OAI.Analysis.BiholderTransport.Coordinates.CoordinateExpansion
import OAI.Analysis.BiholderTransport.Geodesics.GoodContact

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ContactCharts
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance tangentFiniteContactCharts (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
end ContactCharts
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter MeasureTheory Manifold Bundle Metric
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section RegularContact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance tangentFiniteRegularContact (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

omit [MeasurableSpace M] [BorelSpace M] in
lemma cTransform_normal_expansion_active {v : M → ℝ} (hv : Continuous v) {x : M}
    (hD : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x)
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    {A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (hexp : HasQuadraticExpansion (fun h => cTransform v (riemannianExp x h)) p A) :
    p∈activeLogs (n := n) v x := by
  obtain ⟨y,hy⟩ := cTransform_gap_zero hv x
  obtain ⟨q,hq,heq⟩ := exists_minimizing_vector (n := n) x y
  have hqa : q∈activeLogs (n := n) v x := ⟨hq,by simpa only [heq] using hy⟩
  have hDerivative : HasFDerivAt (fun offset => cTransform v (riemannianExp x offset))
      ((innerSL ℝ) p) 0 := by
    obtain ⟨radius,hradius,hbound⟩ := hexp 1 zero_lt_one
    let bound : ℝ := 1+‖A‖/2
    have hpositive : 0<bound := by dsimp [bound]; positivity
    rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
    intro epsilon hepsilon
    have hsmall : 0 < min radius (epsilon/bound) := by positivity
    filter_upwards [Metric.ball_mem_nhds (0:TangentSpace 𝓘(ℝ,Model n) x) hsmall]
      with offset hoffset
    have hnorm : ‖offset‖ < min radius (epsilon/bound) := by
      simpa only [Metric.mem_ball,dist_zero_right] using hoffset
    have hremainder := hbound offset (lt_of_lt_of_le hnorm (min_le_left _ _))
    have hquadratic : |inner ℝ (A offset) offset|≤‖A‖*‖offset‖^2 := by
      calc
        _ ≤ ‖A offset‖*‖offset‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖A‖*‖offset‖)*‖offset‖ :=
          mul_le_mul_of_nonneg_right (A.le_opNorm offset) (norm_nonneg _)
        _ = _ := by ring
    have hlinear : |cTransform v (riemannianExp x offset)-
        cTransform v (riemannianExp (n := n) x 0)-inner ℝ p offset|≤bound*‖offset‖^2 := by
      have htriangle := abs_add_le
        (cTransform v (riemannianExp x offset)-
          quadraticTaylor (cTransform v (riemannianExp (n := n) x 0)) p A offset)
        (inner ℝ (A offset) offset/2)
      rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)] at htriangle
      simp only [quadraticTaylor] at hremainder htriangle
      dsimp [bound]
      have hcancel : cTransform v (riemannianExp x offset)-
          (cTransform v (riemannianExp (n := n) x 0)+inner ℝ p offset+
            inner ℝ (A offset) offset/2)+inner ℝ (A offset) offset/2 =
          cTransform v (riemannianExp x offset)-
            cTransform v (riemannianExp (n := n) x 0)-inner ℝ p offset := by ring
      rw [hcancel] at htriangle
      nlinarith
    have hscale : ‖offset‖*bound≤epsilon := (le_div_iff₀ hpositive).mp
      (le_of_lt (lt_of_lt_of_le hnorm (min_le_right _ _)))
    have hfinal : bound*‖offset‖^2≤epsilon*‖offset‖ := by
      nlinarith [mul_le_mul_of_nonneg_right hscale (norm_nonneg offset)]
    simpa only [zero_add,innerSL_apply_apply,Real.norm_eq_abs] using hlinear.trans hfinal
  have H := hDerivative.unique (active_log_derivative hv hD hqa)
  have hpq : p=q := by
    apply ext_inner_right ℝ
    intro h
    exact congrArg (fun D : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ => D h) H
  rwa [hpq]

omit [MeasurableSpace M] [BorelSpace M] in
lemma contactSelection_continuousAt_of_mdifferentiable {v : M → ℝ} (hv : Continuous v)
    {x : M} (hD : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x) :
    ContinuousAt (contactSelection hv) x := by
  apply contact_selection_continuousAt (continuous_cTransform hv) hv (contactSelection_mem hv)
  exact fun y hy => contact_unique_of_mdifferentiable hv hD hy (contactSelection_mem hv x)

lemma minimizing_dualPair_regular_contact_set {lam cap : ℝ} (hlam : 0<lam) (hcap : lam≤cap)
    {rho0 rho1 : M → ℝ}
    (h0 : AdmissibleDensity (metricVolume n) lam cap rho0)
    (h1 : AdmissibleDensity (metricVolume n) lam cap rho1)
    {u v : M →ᵇ ℝ} (huv : IsCostDualPair u v)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y,0≤contactGap a b x y) →
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (u,v) ≤
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (a,b)) :
    ∃ G : Set M, MeasurableSet G ∧ (∀ᵐ x ∂metricVolume n, x∈G) ∧
      InjOn (contactSelection v.continuous) G ∧
      (∀ x∈G, MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x) ∧
      (∀ x∈G, ContinuousAt (contactSelection v.continuous) x) ∧
      (∀ x∈G, ∃ p : TangentSpace 𝓘(ℝ,Model n) x,
        ∃ A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x,
        p∈activeLogs (n := n) v x ∧ p∈injectivityDomain x ∧
        (∀ h k, inner ℝ (A h) k=inner ℝ h (A k)) ∧
        HasQuadraticExpansion (fun h => cTransform v (riemannianExp x h)) p A) ∧
      (∀ B : Set M, MeasurableSet B → B⊆G →
        ENNReal.ofReal (lam/cap)*metricVolume n B ≤
          metricVolume n (contactSelection v.continuous '' B) ∧
        metricVolume n (contactSelection v.continuous '' B) ≤
          ENNReal.ofReal (cap/lam)*metricVolume n B) := by
  obtain ⟨G,hGm,hGae,hGi,hGD,hGmass⟩ :=
    minimizing_dualPair_good_contact_set hlam hcap h0 h1 huv hmin
  obtain ⟨H,hHm,hHae,hH⟩ := exists_measurable_full_subset
    ((cTransform_ae_normal_quadraticExpansion (n := n) v.continuous).and
      (cTransform_ae_active_before_cut (n := n) v.continuous))
  refine ⟨G∩H,hGm.inter hHm,hGae.and hHae,hGi.mono inter_subset_left,
    fun x hx => hGD x hx.1,fun x hx =>
      contactSelection_continuousAt_of_mdifferentiable v.continuous (hGD x hx.1),?_,?_⟩
  · intro x hx
    obtain ⟨p,A,hAs,hA⟩ := (hH x hx.2).1
    have hp := cTransform_normal_expansion_active v.continuous (hGD x hx.1) hA
    exact ⟨p,A,hp,(hH x hx.2).2 p hp,hAs,hA⟩
  · intro B hBm hBG
    exact hGmass B hBm (hBG.trans inter_subset_left)

end RegularContact
end WeakMTWTransport

end

end

end

end OAI
