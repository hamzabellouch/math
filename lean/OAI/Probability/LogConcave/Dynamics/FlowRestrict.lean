import Mathlib
import OAI.Probability.LogConcave.Sampling.SkewCenteringFieldSmooth

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.LinearGrowthODE
open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma flow_restrict {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b c : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b)
    (hc : c∈Icc a b) (x : E) :
    EqOn (flow hf hK hB hg hab x) (flow hf hK hB hg hc.1 x) (Icc a c) := by
  apply unique hf (flow_continuous hf hK hB hg hab x).continuousOn
    (flow_continuous hf hK hB hg hc.1 x).continuousOn
  · intro t ht
    exact (flow_deriv hf hK hB hg hab x t ⟨ht.1,ht.2.trans hc.2⟩).mono
      (Icc_subset_Icc le_rfl hc.2)
  · exact flow_deriv hf hK hB hg hc.1 x
  · rw [flow_initial,flow_initial]

theorem stationary_at {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b)
    {μ : Measure E} [IsFiniteMeasure μ] (hfi : Integrable (fun x => ‖f x‖) μ)
    (hflux : ∀ψ : E → ℝ,ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫x,(fderiv ℝ ψ x) (f x) ∂μ)=0) {t : ℝ} (ht : t∈Icc a b) :
    μ.map (fun y => flow hf hK hB hg hab y t)=μ := by
  obtain he|hlt := ht.1.eq_or_lt
  · subst t
    simp only [flow_initial]
    exact Measure.map_id
  · have hEq : (fun y => flow hf hK hB hg hab y t)=
        (fun y => flow hf hK hB hg hlt.le y t) := by
      funext y
      exact flow_restrict hf hK hB hg hab ht y ⟨ht.1,le_rfl⟩
    rw [hEq]
    exact stationary_law hf hK hB hg hlt hfi hflux
end LogConcaveSampling.LinearGrowthODE

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Function MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace

theorem exists_skew_centering_flow {d : ℕ} {μ : Measure (Point d)} [IsFiniteMeasure μ]
    {K : Point d → Point d →L[ℝ] Point d} {m : Point d → Point d}
    (hK : ContDiff ℝ 1 K) (hm : ContDiff ℝ 1 m) {C : ℝ} {L : ℝ≥0}
    (hC : 0≤C) (hKb : ∀y,‖K y‖≤C) (hmL : LipschitzWith L m)
    (hμ : Integrable (fun y => ‖y‖) μ)
    (hstein : ∀u : Point d,∀φ : Point d → ℝ,ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫y,inner ℝ u (m y)*φ y ∂μ)=∫y,fderiv ℝ φ y ((K y).adjoint u) ∂μ)
    {s a b : ℝ} (hs : 0<s) (hab : a≤b) :
    ∃Ψ : (Point d × Point d) → ℝ → (Point d × Point d),
      (∀p,Continuous (Ψ p) ∧ Ψ p a=p ∧ ∀t∈Icc a b,
        HasDerivWithinAt (Ψ p) (skewCenteringField K m s (Ψ p t)) (Icc a b) t) ∧
      (∀t∈Icc a b,Continuous (fun p => Ψ p t)) ∧
      (∀t∈Icc a b,(μ.prod (stdGaussian (Point d))).map (fun p => Ψ p t)=μ.prod (stdGaussian (Point d))) := by
  let f := skewCenteringField K m s
  have hf : ContDiff ℝ 1 f := skewCenteringField_smooth hK hm s
  have hk : 0≤ s⁻¹*(C+L) := by positivity
  have hb : 0≤ s⁻¹*‖m 0‖ := by positivity
  have hg : ∀p,‖f p‖≤ s⁻¹*(C+L)*‖p‖+s⁻¹*‖m 0‖ := skewCenteringField_growth hC hKb hmL hs
  let Ψ := LinearGrowthODE.flow hf hk hb hg hab
  refine ⟨Ψ,?_,?_,?_⟩
  · intro p
    exact ⟨LinearGrowthODE.flow_continuous hf hk hb hg hab p,
      LinearGrowthODE.flow_initial hf hk hb hg hab p,
      LinearGrowthODE.flow_deriv hf hk hb hg hab p⟩
  · exact fun t ht => LinearGrowthODE.flow_continuous_initial hf hk hb hg hab t ht
  · have hi : Integrable (fun g : Point d => ‖g‖) (stdGaussian (Point d)) := IsGaussian.integrable_id.norm
    have hprod := integrable_product_norm hμ hi
    have hfi : Integrable (fun p => ‖f p‖) (μ.prod (stdGaussian (Point d))) := by
      apply ((hprod.const_mul (s⁻¹*(C+L))).add (integrable_const (s⁻¹*‖m 0‖))).mono' hf.continuous.norm.aestronglyMeasurable
      filter_upwards [] with p
      rw [norm_norm]
      exact hg p
    exact fun t ht => LinearGrowthODE.stationary_at hf hk hb hg hab hfi
      (fun φ hφ hφc => product_stein_flux hK.continuous hm.continuous hstein s hφ hφc) ht

theorem centering_momentum_identity {d : ℕ} {K : Point d → Point d →L[ℝ] Point d}
    {M : Point d → Point d} (hM : Continuous M) (u : Point d) {s : ℝ} (hs : 0<s)
    {α : ℝ → Point d × Point d} (hα : Continuous α)
    (hd : ∀t∈Icc (0:ℝ) 1,HasDerivWithinAt α
      (skewCenteringField K (fun y => M y-u) s (α t)) (Icc (0:ℝ) 1) t) :
    s • (α 0).2+(∫t in (0:ℝ)..1,M (α t).1)=u+s • (α 1).2 := by
  let β := fun t : ℝ => s • (α t).2+t • u
  have hβ : Continuous β := (hα.snd.const_smul s).add (continuous_id.smul (continuous_const (y:=u)))
  have hdβ (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) : HasDerivAt β (M (α t).1) t := by
    have hh := (hd t ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have hG : HasDerivAt (fun t => (α t).2) (s⁻¹ • (M (α t).1-u)) t := hh.snd
    have he := (hG.const_smul s).add ((hasDerivAt_id t).smul_const u)
    convert he using 1 <;> first | rfl | simp [smul_smul, hs.ne']
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ)≤1)
    hβ.continuousOn hdβ ((hM.comp hα.fst).intervalIntegrable 0 1)
  change (∫t in (0:ℝ)..1,M (α t).1)=β 1-β 0 at hFTC
  rw [hFTC]
  simp only [β,one_smul,zero_smul,add_zero]
  abel
end LogConcaveSampling

end

end

end

end OAI
