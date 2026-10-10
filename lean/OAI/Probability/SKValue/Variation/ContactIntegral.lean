import Mathlib
import OAI.Probability.SKValue.Variation.ContactVariations
import OAI.Probability.SKValue.Equations.TruncatedStieltjes

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma IsDiffusion.contact_fubini {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) {T : ℝ}
    (hT : T∈Ico (0 : ℝ) 1) :
    Integrable (contactPotential W γ X) (γ.truncatedMass T hT) ∧
    (∫ s,contactPotential W γ X s ∂γ.truncatedMass T hT)=
      ∫ t in (0 : ℝ)..1,min (γ.coeff t) (γ.coeff T)*(gradientMoment W γ X t-t) := by
  let μ := γ.truncatedMass T hT
  let ν : Measure ℝ := volume.restrict (Ioc 0 1)
  let F : ℝ×ℝ → ℝ := {p : ℝ×ℝ | p.1≤p.2}.indicator (fun p ↦ gradientMoment W γ X p.2-p.2)
  have hi : Integrable (fun t ↦ gradientMoment W γ X t-t) ν :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ)≤1)).mp hX.moment_difference_integrable
  have hF : Integrable F (μ.prod ν) := by
    apply Integrable.of_bound (hi.aestronglyMeasurable.comp_snd.indicator
      (measurableSet_le measurable_fst measurable_snd)) 1
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (μ := volume) measurableSet_Ioc)] with p hp
    by_cases hs : p.1≤p.2
    · rw [indicator_of_mem (show p∈{a : ℝ×ℝ | a.1≤a.2} from hs),Real.norm_eq_abs]
      apply abs_le.mpr
      have h0 := gradientMoment_nonneg W γ X p.2
      have h1 := (abs_le.mp (gradientMoment_bound W γ X ⟨hp.1.le,hp.2⟩)).2
      constructor <;> linarith [hp.1,hp.2]
    · rw [indicator_of_notMem (show p∉{a : ℝ×ℝ | a.1≤a.2} from hs),norm_zero]; norm_num
  have hleft : (fun s ↦ ∫ t,F (s,t) ∂ν)=ᵐ[μ] contactPotential W γ X := by
    filter_upwards [γ.truncatedMass_ae_mem hT] with s hs
    have hs' : s∈Icc (0 : ℝ) 1 := ⟨hs.1,hs.2.trans hT.2.le⟩
    change (∫ t in Ioc (0 : ℝ) 1,F (s,t))=contactPotential W γ X s
    rw [←intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1)]
    calc
      (∫ t in (0 : ℝ)..1,F (s,t))=
          ∫ t in (0 : ℝ)..1,(OrderParameter.atom s).coeff t*(gradientMoment W γ X t-t) := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp [F,OrderParameter.atom,indicator]
        split_ifs <;> simp
      _=contactPotential W γ X s := integral_atom_mul s hs' _
  have hright : (fun t ↦ ∫ s,F (s,t) ∂μ)=ᵐ[ν]
      (fun t ↦ min (γ.coeff t) (γ.coeff T)*(gradientMoment W γ X t-t)) := by
    have hν : ∀ᵐ t ∂ν,t∈Ico (0 : ℝ) 1 := by
      dsimp [ν]
      rw [←restrict_Ico_eq_restrict_Ioc]
      exact ae_restrict_mem measurableSet_Ico
    filter_upwards [hν] with t ht
    have he : (fun s ↦ F (s,t))=(Iic t).indicator (fun _ ↦ gradientMoment W γ X t-t) := rfl
    rw [he,integral_indicator measurableSet_Iic,integral_const]
    simp only [Measure.real,Measure.restrict_apply_univ,μ,γ.truncatedMass_cdf hT ht,
      ENNReal.toReal_ofReal (le_min (γ.nonneg t ht) (γ.nonneg T hT)),smul_eq_mul]
  refine ⟨hF.integral_prod_left.congr hleft,?_⟩
  rw [←integral_congr_ae hleft]
  have hswap := integral_integral_swap (f := fun s t ↦ F (s,t)) hF
  rw [hswap,integral_congr_ae hright]
  exact (intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1)).symm

lemma IsMinimizer.contactPotential_ae_zero {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hγ : IsMinimizer W γ) (hX : IsDiffusion W γ X)
    {T : ℝ} (hT : T∈Ico (0 : ℝ) 1) :
    ∀ᵐ s ∂γ.truncatedMass T hT,contactPotential W γ X s=0 := by
  have hh := hγ.variation_inequality hX (γ.removeBelow (γ.coeff T))
  simp_rw [γ.removeBelow_sub,neg_mul] at hh
  rw [intervalIntegral.integral_neg] at hh
  obtain ⟨hi,he⟩ := hX.contact_fubini hT
  have hnn : 0≤ᵐ[γ.truncatedMass T hT] contactPotential W γ X := by
    filter_upwards [γ.truncatedMass_ae_mem hT] with s hs
    exact hγ.contactPotential_nonneg hX ⟨hs.1,hs.2.trans hT.2.le⟩
  apply (integral_eq_zero_iff_of_nonneg_ae hnn hi).mp
  have hpos := integral_nonneg_of_ae hnn
  rw [he] at hpos ⊢
  linarith

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma OrderParameter.truncatedMass_Ioc (γ : OrderParameter) {a b : ℝ}
    (ha : 0≤a) (hab : a≤b) (hb : b<1) :
    γ.truncatedMass b ⟨ha.trans hab,hb⟩ (Ioc a b)=ENNReal.ofReal (γ.coeff b-γ.coeff a) := by
  have he : Ioc a b∩Ioc (0 : ℝ) b=Ioc a b := inter_eq_left.mpr (Ioc_subset_Ioc ha le_rfl)
  have hst : γ.truncatedStieltjes b ⟨ha.trans hab,hb⟩ a=γ.coeff a := by
    simp [OrderParameter.truncatedStieltjes,max_eq_right ha,min_eq_right hab]
  simp only [OrderParameter.truncatedMass,Measure.add_apply,
    Measure.restrict_apply measurableSet_Ioc,he,StieltjesFunction.measure_Ioc,
    hst,Measure.smul_apply,
    Measure.dirac_apply' _ measurableSet_Ioc]
  rw [indicator_of_notMem (show (0 : ℝ)∉Ioc a b from fun h ↦ not_lt_of_ge ha h.1)]
  simp
  simp [OrderParameter.truncatedStieltjes,max_eq_right (ha.trans hab)]

lemma IsMinimizer.coeff_eq_of_contactPositive {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hγ : IsMinimizer W γ) (hX : IsDiffusion W γ X)
    {a b : ℝ} (ha : 0≤a) (hab : a≤b) (hb : b<1)
    (hG : ∀ s∈Ioc a b,0<contactPotential W γ X s) : γ.coeff a=γ.coeff b := by
  have hz := hγ.contactPotential_ae_zero hX (T := b) ⟨ha.trans hab,hb⟩
  rw [ae_iff] at hz
  have hI : γ.truncatedMass b ⟨ha.trans hab,hb⟩ (Ioc a b)=0 :=
    measure_mono_null (fun s hs ↦ ne_of_gt (hG s hs)) hz
  rw [γ.truncatedMass_Ioc ha hab hb,ENNReal.ofReal_eq_zero] at hI
  exact le_antisymm (γ.monotone ⟨ha,hab.trans_lt hb⟩ ⟨ha.trans hab,hb⟩ hab) (by linarith)

lemma IsMinimizer.coeff_constant_of_contactPositive {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hγ : IsMinimizer W γ) (hX : IsDiffusion W γ X)
    {a b : ℝ} (ha : 0≤a) (hb : b≤1)
    (hG : ∀ s∈Ioo a b,0<contactPotential W γ X s) :
    ∀ s∈Ioo a b,∀ t∈Ioo a b,γ.coeff s=γ.coeff t := by
  intro s hs t ht
  wlog hst : s≤t generalizing s t
  · exact (this t ht s hs (le_of_not_ge hst)).symm
  exact hγ.coeff_eq_of_contactPositive hX (ha.trans hs.1.le) hst (ht.2.trans_le hb)
    (fun u hu ↦ hG u ⟨hs.1.trans hu.1,hu.2.trans_lt ht.2⟩)

end SKValue

end

end OAI
