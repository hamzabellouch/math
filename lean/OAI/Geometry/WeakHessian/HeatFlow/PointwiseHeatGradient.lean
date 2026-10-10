import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.GradientProbes

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile94
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma memLp_localSlope_sq_compact (hfin : FiniteOnBoundedSets m) {f : X → ℝ}
    {L : ℝ≥0} (hf : LipschitzWith L f) (hfc : HasCompactSupport f) :
    MemLp (fun x => (localSlope f x).toReal^2) 2 m := by
  have hb := memLp_indicator_const (μ := m) 2 (isClosed_tsupport f).measurableSet ((L:ℝ)^2)
    (Or.inr (hfin (tsupport f) hfc.isBounded).ne)
  apply hb.mono ((measurable_localSlope hf.continuous).ennreal_toReal.pow_const 2).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    by_cases hx : x ∈ tsupport f
    · rw [indicator_of_mem hx,Real.norm_of_nonneg (sq_nonneg _),Real.norm_of_nonneg (sq_nonneg _)]
      exact sq_le_sq₀ ENNReal.toReal_nonneg L.coe_nonneg |>.mpr
        ((ENNReal.toReal_mono ENNReal.coe_ne_top (localSlope_le_lipschitz hf x)).trans_eq (ENNReal.coe_toReal L))
    · simp [hx,localSlope_eq_zero_of_notMem_tsupport hx]

omit [SigmaFinite m] in
lemma integrableOn_weakGradient_sq (hfin : FiniteOnBoundedSets m) {F : X → ℝ}
    {L : ℝ≥0} (hF : LipschitzWith L F) {S : Set X} (hS : m S < ∞) :
    IntegrableOn (fun x => (weakGradient m F x)^2) S m := by
  apply (integrableOn_const (C := (L:ℝ)^2) hS.ne).mono'
    ((weakGradient_isMinimal (localSobolev_of_lipschitz hfin hF).2).1.1.aestronglyMeasurable.pow 2).restrict
  filter_upwards [ae_restrict_of_ae (weakGradient_le_localSlope hfin hF),
    ae_restrict_of_ae (weakGradient_nonneg (m := m) F)] with x hx hn
  change ‖(weakGradient m F x)^2‖ ≤ (L:ℝ)^2
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  apply sq_le_sq₀ hn L.coe_nonneg |>.mpr
  exact hx.trans ((ENNReal.toReal_mono ENNReal.coe_ne_top (localSlope_le_lipschitz hF x)).trans_eq (ENNReal.coe_toReal L))

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma heat_pairing_Lp_density (h : QuadraticCheegerEnergy m) (t : ℝ) (u : Lp ℝ 2 m)
    {g : X → ℝ} (hg : MemLp g 2 m) :
    (∫ x,cheegerHeat h t u x*g x ∂m) = ∫ x,u x*cheegerHeat h t (hg.toLp g) x ∂m := by
  have he : (∫ x,cheegerHeat h t u x*g x ∂m) = ⟪hg.toLp g,cheegerHeat h t u⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    simp only [RCLike.inner_apply,conj_trivial,hx]
  calc
    _ = ⟪hg.toLp g,cheegerHeat h t u⟫_ℝ := he
    _ = ⟪cheegerHeat h t (hg.toLp g),u⟫_ℝ := ((cheegerHeat_symmetric h t) (hg.toLp g) u).symm
    _ = _ := by rw [L2.inner_def]; simp only [RCLike.inner_apply,conj_trivial]

lemma RCD.cheegerHeat_gradient_pointwise_compact {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) (f F : X →ᵇ ℝ)
    (hf : GloballyLipschitz (f : X → ℝ)) (hfc : HasCompactSupport (f : X → ℝ))
    (hFl : GloballyLipschitz (F : X → ℝ)) (hf2 : MemLp f 2 m) {t : ℝ} (ht : 0 ≤ t)
    (hF : F =ᵐ[m] cheegerHeat h t (hf2.toLp f)) :
    ∀ᵐ x ∂m,(weakGradient m F x)^2 ≤ Real.exp (-2*K*t)*
      cheegerHeat h t ((memLp_localSlope_sq_compact hfin hf.choose_spec hfc).toLp
        (fun x => (localSlope f x).toReal^2)) x := by
  let hg := memLp_localSlope_sq_compact hfin hf.choose_spec hfc
  let V := cheegerHeat h t (hg.toLp (fun x => (localSlope f x).toReal^2))
  have hVi (S : Set X) (hS : m S < ∞) : IntegrableOn (fun x => Real.exp (-2*K*t)*V x) S m := by
    let : IsFiniteMeasure (m.restrict S) := ⟨by simpa only [Measure.restrict_apply_univ] using hS⟩
    exact ((Lp.memLp V).restrict S |>.integrable (by norm_num)).const_mul _
  have H := ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite
    (f := fun x => Real.exp (-2*K*t)*V x-(weakGradient m F x)^2)
    (fun S _hS hs => (hVi S hs).sub (integrableOn_weakGradient_sq hfin hFl.choose_spec hs)) (by
      intro S hS hs
      let hu2 := memLp_indicator_const (μ := m) 2 hS (1:ℝ) (Or.inr hs.ne)
      let u := hu2.toLp (S.indicator (fun _ : X => (1:ℝ)))
      have hue : u =ᵐ[m] S.indicator (fun _ : X => (1:ℝ)) := hu2.coeFn_toLp
      have hui : Integrable u m :=
        ((integrableOn_const (C := (1:ℝ)) hs.ne).integrable_indicator hS).congr hue.symm
      have hun : ∀ᵐ x ∂m,0 ≤ u x := hue.mono fun x hx => hx ▸ indicator_nonneg (fun _ _ => zero_le_one) x
      have hub : ∀ᵐ x ∂m,u x ≤ 1 := by
        filter_upwards [hue] with x hx
        rw [hx]; by_cases hx : x ∈ S <;> simp [hx]
      have HH := hrcd.cheegerHeat_gradient_integral_compact hN hfull hfin h o f F hf hfc hFl hf2 ht hF
        u hui hun zero_le_one hub
      rw [heat_pairing_Lp_density h t u hg] at HH
      have hpair (g : X → ℝ) : (∫ x,u x*g x ∂m) = ∫ x in S,g x ∂m := by
        rw [← integral_indicator hS]
        apply integral_congr_ae
        filter_upwards [hue] with x hx
        rw [hx]; by_cases hx : x ∈ S <;> simp [hx]
      rw [hpair,hpair] at HH
      rw [integral_sub (hVi S hs) (integrableOn_weakGradient_sq hfin hFl.choose_spec hs),integral_const_mul]
      exact sub_nonneg.mpr HH)
  exact H.mono fun x hx => sub_nonneg.mp hx
end WeakHessian

end
end InlinedFile94

end OAI
