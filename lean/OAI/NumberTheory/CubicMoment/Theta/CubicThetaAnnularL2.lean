import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAnnularSeries
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGlobalL2

namespace OAI

/-! The radial annulus transport is a bounded linear map to the actual
global L2 space, with its norm bounded by the mass of a compact core. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaAnnularSeries_core :
    ∃ S : Finset (Matrix.SpecialLinearGroup (Fin 2) Eisenstein),
      ∀ (f : C(CubicThetaForcingBand,ℂ)) (p : CubicThetaPoint),
      cubicThetaQuotientMap p∉cubicThetaQuotientCore S 2 →
        cubicThetaAnnularSeries f p=0 := by
  obtain ⟨S,hS⟩ := cubicThetaCuspTransition_core
  refine ⟨S,fun f p hp => ?_⟩
  suffices hz : ∀ r, cubicThetaAnnularTerm f r p=0 by
    simp only [cubicThetaAnnularSeries,hz,tsum_zero]
  intro r
  by_contra hn
  have hh := cubicThetaAnnularTerm_high hn
  have he : cubicThetaPointHeight (r.completion • p)=r.height p.val := by
    change (cubicThetaBottomRow r.completion).height p.val=_
    rw [r.completion_row]
  have hq := hS 1 (r.completion • p) (by rw [he]; exact hh.1.le) (by rw [he]; exact hh.2.le)
  rw [one_smul,cubicThetaQuotient_covering.map_smul] at hq
  exact hp hq

def cubicThetaAnnularRepresentative (f : C(CubicThetaForcingBand,ℂ))
    (q : CubicThetaQuotient) : ℂ := cubicThetaAnnularSeries f (cubicThetaBorelSection q)

lemma cubicThetaAnnularRepresentative_measurable (f : C(CubicThetaForcingBand,ℂ)) :
    Measurable (cubicThetaAnnularRepresentative f) :=
  (cubicThetaAnnularSeries_measurable f).comp cubicThetaBorelSection_measurable

lemma cubicThetaAnnularRepresentative_memLp (f : C(CubicThetaForcingBand,ℂ)) :
    MemLp (cubicThetaAnnularRepresentative f) 2 cubicThetaQuotientMeasure := by
  obtain ⟨S,hS⟩ := cubicThetaAnnularSeries_core
  have hK := cubicThetaQuotientCore_compact S 2
  have hi : MemLp ((cubicThetaQuotientCore S 2).indicator (fun _ => ‖f‖)) 2
      cubicThetaQuotientMeasure :=
    memLp_indicator_const 2 hK.measurableSet ‖f‖ (Or.inr hK.measure_ne_top)
  apply hi.mono' (cubicThetaAnnularRepresentative_measurable f).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro q
  by_cases hq : q∈cubicThetaQuotientCore S 2
  · rw [indicator_of_mem hq]
    exact cubicThetaAnnularSeries_norm f _
  · rw [indicator_of_notMem hq]
    have hz := hS f (cubicThetaBorelSection q) (by rwa [cubicThetaBorelSection_rightInverse])
    change ‖cubicThetaAnnularSeries f (cubicThetaBorelSection q)‖≤0
    rw [hz,norm_zero]

def cubicThetaAnnularL2Linear : C(CubicThetaForcingBand,ℂ) →ₗ[ℂ] CubicThetaGlobalL2 where
  toFun f := (cubicThetaAnnularRepresentative_memLp f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(cubicThetaAnnularRepresentative_memLp (f+g)).coeFn_toLp,
      (cubicThetaAnnularRepresentative_memLp f).coeFn_toLp,
      (cubicThetaAnnularRepresentative_memLp g).coeFn_toLp,
      Lp.coeFn_add ((cubicThetaAnnularRepresentative_memLp f).toLp _)
        ((cubicThetaAnnularRepresentative_memLp g).toLp _)] with q hfg hf hg ha
    simp only [Pi.add_apply] at ha
    rw [hfg,ha,hf,hg]
    exact cubicThetaAnnularSeries_add f g _
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(cubicThetaAnnularRepresentative_memLp (c • f)).coeFn_toLp,
      (cubicThetaAnnularRepresentative_memLp f).coeFn_toLp,
      Lp.coeFn_smul c ((cubicThetaAnnularRepresentative_memLp f).toLp _)] with q hcf hf hc
    simp only [RingHom.id_apply]
    simp only [Pi.smul_apply] at hc
    rw [hcf,hc,hf]
    exact cubicThetaAnnularSeries_smul c f _

lemma cubicThetaAnnularL2Linear_bound :
    ∃ C : ℝ, ∀ f : C(CubicThetaForcingBand,ℂ), ‖cubicThetaAnnularL2Linear f‖≤C*‖f‖ := by
  obtain ⟨S,hS⟩ := cubicThetaAnnularSeries_core
  have hK := cubicThetaQuotientCore_compact S 2
  let g : Lp ℝ 2 cubicThetaQuotientMeasure :=
    indicatorConstLp 2 hK.measurableSet hK.measure_ne_top 1
  refine ⟨‖g‖,fun f => ?_⟩
  have hb : ∀ᵐ q ∂cubicThetaQuotientMeasure,
      ‖cubicThetaAnnularL2Linear f q‖≤‖f‖*‖g q‖ := by
    filter_upwards [(cubicThetaAnnularRepresentative_memLp f).coeFn_toLp,
      indicatorConstLp_coeFn (p:=2) (hs:=hK.measurableSet) (hμs:=hK.measure_ne_top) (c:=(1:ℝ))]
      with q hf hg
    change (cubicThetaAnnularL2Linear f) q=_ at hf
    change g q=_ at hg
    rw [hf,hg]
    by_cases hq : q∈cubicThetaQuotientCore S 2
    · rw [indicator_of_mem hq,norm_one,mul_one]
      exact cubicThetaAnnularSeries_norm f _
    · rw [indicator_of_notMem hq,norm_zero,mul_zero]
      have hz := hS f (cubicThetaBorelSection q) (by rwa [cubicThetaBorelSection_rightInverse])
      change ‖cubicThetaAnnularSeries f (cubicThetaBorelSection q)‖≤0
      rw [hz,norm_zero]
  simpa only [mul_comm] using Lp.norm_le_mul_norm_of_ae_le_mul hb

def cubicThetaAnnularL2 : C(CubicThetaForcingBand,ℂ) →L[ℂ] CubicThetaGlobalL2 :=
  cubicThetaAnnularL2Linear.mkContinuous
    cubicThetaAnnularL2Linear_bound.choose cubicThetaAnnularL2Linear_bound.choose_spec

end CubicFirstMoment

end

end OAI
