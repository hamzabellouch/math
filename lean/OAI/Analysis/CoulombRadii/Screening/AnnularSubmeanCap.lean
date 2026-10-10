import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.PoissonInterior
import OAI.Analysis.CoulombRadii.FieldAnalysis.NewtonSubmean

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma cap_ball_geometry {r L : ℝ} (hr : 0<r) (hL : 1≤L) {y z : Position}
    (hy0 : 3*r/4≤‖y‖) (hy1 : ‖y‖≤6*L*r)
    (hz : z∈Metric.closedBall y (r/8)) :
    r/2≤‖z‖ ∧ ‖z‖≤8*L*r ∧ ‖y‖≤2*‖z‖ := by
  have hd : ‖z-y‖≤r/8 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
  have h1 : ‖y‖≤‖z‖+‖z-y‖ := by
    simpa only [add_sub_cancel, norm_sub_rev] using norm_add_le z (y-z)
  have h2 : ‖z‖≤‖y‖+‖z-y‖ := by
    simpa only [add_sub_cancel] using norm_add_le y (z-y)
  have hLr : r≤L*r := by nlinarith
  constructor
  · linarith
  constructor <;> linarith

lemma annular_submean_cap {F : Position → ℝ} {r L T : ℝ}
    (hr : 0<r) (hL : 1≤L) (hT : 0≤T)
    (hE : IntegrableOn (fun z => max (‖z‖^4*F z-T) 0)
      {z | r/2≤‖z‖ ∧ ‖z‖≤8*L*r}) {y : Position}
    (hy0 : 3*r/4≤‖y‖) (hy1 : ‖y‖≤6*L*r)
    (hF : IntegrableOn F (Metric.closedBall y (r/8)))
    (hmean : F y≤(4*Real.pi/3*(r/8)^3)⁻¹*(∫ z in Metric.closedBall y (r/8),F z)) :
    ‖y‖^4*F y≤16*T+16*(4*Real.pi/3*(r/8)^3)⁻¹*
      ∫ z in {z | r/2≤‖z‖ ∧ ‖z‖≤8*L*r},max (‖z‖^4*F z-T) 0 := by
  let A : Set Position := {z | r/2≤‖z‖ ∧ ‖z‖≤8*L*r}
  let B := Metric.closedBall y (r/8)
  let V := 4*Real.pi/3*(r/8)^3
  let E := fun z : Position => max (‖z‖^4*F z-T) 0
  have hV : 0<V := by dsimp [V]; positivity
  have hsub : B⊆A := fun z hz => (cap_ball_geometry hr hL hy0 hy1 hz).1 |> fun h0 =>
    ⟨h0,(cap_ball_geometry hr hL hy0 hy1 hz).2.1⟩
  have hEB : IntegrableOn E B := hE.mono_set hsub
  have hloc (z : Position) (hz : z∈B) : ‖y‖^4*F z≤16*T+16*E z := by
    have H := cap_ball_geometry hr hL hy0 hy1 hz
    have he : ‖z‖^4*F z≤T+E z := by dsimp [E]; linarith [le_max_left (‖z‖^4*F z-T) 0]
    by_cases hf : 0≤F z
    · have hn : ‖y‖^4≤16*‖z‖^4 := by
        have hh := pow_le_pow_left₀ (norm_nonneg y) H.2.2 4
        norm_num [mul_pow] at hh ⊢
        exact hh
      have hh := mul_le_mul_of_nonneg_right hn hf
      nlinarith
    · have hf' : F z≤0 := le_of_not_ge hf
      have hh := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (norm_nonneg y) 4) hf'
      have he0 : 0≤E z := le_max_right _ _
      linarith
  have hcI : IntegrableOn (fun _ : Position => (16*T:ℝ)) B :=
    integrableOn_const (isCompact_closedBall y (r/8)).measure_ne_top
  have hIB : (∫ z in B,‖y‖^4*F z)≤∫ z in B,16*T+16*E z := by
    apply setIntegral_mono_on (hF.const_mul _) (hcI.add (hEB.const_mul _))
      measurableSet_closedBall
    exact hloc
  have hIE : (∫ z in B,E z)≤∫ z in A,E z := by
    apply setIntegral_mono_set hE
    · exact Eventually.of_forall (fun z => le_max_right _ _)
    · exact Eventually.of_forall (fun _ hz => hsub hz)
  have hconst : (∫ z in B,(16*T:ℝ))=V*(16*T) := by
    rw [integral_const,smul_eq_mul,measureReal_restrict_apply_univ]
    rw [show volume.real B=V from Coulomb.volume_closedBall_three _ (by positivity)]
  rw [integral_const_mul,integral_add hcI (hEB.const_mul _),
    hconst,integral_const_mul] at hIB
  have hm := mul_le_mul_of_nonneg_left hmean (pow_nonneg (norm_nonneg y) 4)
  have hIB' := mul_le_mul_of_nonneg_left hIB (inv_nonneg.mpr hV.le)
  have hIV : V⁻¹*V=1 := inv_mul_cancel₀ hV.ne'
  change ‖y‖^4*F y≤16*T+16*V⁻¹*∫ z in A,E z
  calc
    _ ≤ V⁻¹*(‖y‖^4*(∫ z in B,F z)) := by simpa only [V,B,mul_left_comm] using hm
    _ ≤ V⁻¹*(V*(16*T)+16*(∫ z in B,E z)) := hIB'
    _ = 16*T+16*V⁻¹*(∫ z in B,E z) := by rw [mul_add,←mul_assoc,hIV]; ring
    _ ≤ _ := by linarith [mul_le_mul_of_nonneg_left hIE (show 0≤16*V⁻¹ by positivity)]
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma spatial_moment_markov {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {A : Set Position}
    (hA : MeasurableSet A) (hAfin : volume A<∞)
    {Q : Ω × Position → ℝ} (hQ : Measurable Q) (hQ0 : ∀ z,0≤Q z)
    {B M : ℝ} (hB : ∀ ω y,y∈A → Q (ω,y)≤B)
    (hM : ∀ y,y∈A → (∫ ω,Q (ω,y) ∂P)≤M) {t : ℝ} (ht : 0<t) :
    Measurable (fun ω => ∫ y in A,Q (ω,y)) ∧
    (∀ ω,IntegrableOn (fun y => Q (ω,y)) A) ∧
    P.real {ω | t<(∫ y in A,Q (ω,y))}≤volume.real A*M/t := by
  have : IsFiniteMeasure (volume.restrict A) := ⟨by simpa only [Measure.restrict_apply_univ] using hAfin⟩
  have hI (ω : Ω) : IntegrableOn (fun y => Q (ω,y)) A := by
    apply Integrable.of_bound ((hQ.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable) B
    filter_upwards [ae_restrict_mem hA] with y hy
    change ‖Q (ω,y)‖≤B
    rw [Real.norm_of_nonneg (hQ0 _)]
    exact hB ω y hy
  have hprod : Integrable Q (P.prod (volume.restrict A)) := by
    apply Integrable.of_bound hQ.aestronglyMeasurable B
    rw [Measure.ae_prod_iff_ae_ae (measurableSet_le hQ.norm measurable_const)]
    filter_upwards [] with ω
    filter_upwards [ae_restrict_mem hA] with y hy
    rw [Real.norm_of_nonneg (hQ0 _)]
    exact hB ω y hy
  have hIm : Measurable (fun ω => ∫ y in A,Q (ω,y)) :=
    hQ.stronglyMeasurable.integral_prod_right'.measurable
  refine ⟨hIm,hI,?_⟩
  have hswap : (∫ ω,(∫ y in A,Q (ω,y)) ∂P)=(∫ y in A,∫ ω,Q (ω,y) ∂P) :=
    integral_integral_swap hprod
  have hmean : (∫ ω,(∫ y in A,Q (ω,y)) ∂P)≤volume.real A*M := by
    rw [hswap]
    calc
      _ ≤ ∫ y in A,M := integral_mono_ae hprod.integral_prod_right (integrable_const M)
        (by filter_upwards [ae_restrict_mem hA] with y hy; exact hM y hy)
      _ = _ := by simp only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul]
  have hMark := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun ω => integral_nonneg (fun y => hQ0 (ω,y))))
    hprod.integral_prod_left t
  have hprob : P.real {ω | t<(∫ y in A,Q (ω,y))}≤P.real {ω | t≤(∫ y in A,Q (ω,y))} :=
    measureReal_mono (by
      intro ω hω
      exact (show t<(∫ y in A,Q (ω,y)) from hω).le)
  apply (le_div_iff₀ ht).2
  have hh := mul_le_mul_of_nonneg_left hprob ht.le
  linarith
end NeutralAtom
end

end

end OAI
