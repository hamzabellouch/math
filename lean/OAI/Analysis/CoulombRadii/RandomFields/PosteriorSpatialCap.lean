import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.PhysicalPosteriorInverse
import OAI.Analysis.CoulombRadii.Screening.AnnularSubmeanCap
import OAI.Analysis.CoulombRadii.Screening.PhysicalCapMoment

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

def physicalSpatialCap : ℝ := 32*physicalFieldCapBase+1
lemma physicalSpatialCap_pos : 0<physicalSpatialCap := by
  unfold physicalSpatialCap
  linarith [physicalFieldCapBase_ge_one]

lemma posterior_scaled_excess_bounded {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → B)
    (g : Position → ℝ) {c r₀ s : ℝ} (hc : 0<c) (hr₀ : 0<r₀) (hs : 0<s)
    (datum : B) {Z r L T : ℝ} (hZ : 0≤Z) (hr : 0<r) (hL : 1≤L) (hT : 0≤T)
    {y : Position} (hy0 : r/2≤‖y‖) (hy1 : ‖y‖≤8*L*r) :
    max (‖y‖^4*(Z*coulombKernel y-potentialOf
      (conditionalPacketDensity P raw obs g c r₀ s datum) y)-T) 0 ≤ Z*(8*L*r)^3 := by
  have hp := potentialOf_nonneg (conditionalPacketDensity_nonneg P raw obs g hc hr₀ hs datum) y
  have hn : 0<‖y‖ := by linarith
  have he : ‖y‖^4*coulombKernel y=‖y‖^3 := by unfold coulombKernel; field_simp
  have hab : ‖y‖^4*(Z*coulombKernel y-potentialOf
      (conditionalPacketDensity P raw obs g c r₀ s datum) y)≤Z*‖y‖^3 := by
    have H := mul_le_mul_of_nonneg_left (sub_le_self (Z*coulombKernel y) hp) (pow_nonneg hn.le 4)
    calc
      _ ≤ ‖y‖^4*(Z*coulombKernel y) := H
      _ = Z*‖y‖^3 := by rw [mul_left_comm,he]
  have hcub := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn.le hy1 3) hZ
  apply max_le
  · linarith
  · positivity

lemma posterior_spatial_cap_of_moment {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (raw : Ω → Configuration n)
    (obs : Ω → B) (hobs : Measurable obs)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hm : (∫ z,g z^2)=1) {c r₀ s : ℝ}
    (hc : 0<c) (hr₀ : 0<r₀) (hs : 0<s)
    {Z r L M : ℝ} (hZ : 0≤Z) (hr : 0<r) (hL : 1≤L) (hM0 : 0≤M)
    (hM : ∀ y : Position,r/2≤‖y‖ → ‖y‖≤8*L*r →
      (∫ ω,max (‖y‖^4*(Z*coulombKernel y-potentialOf
        (conditionalPacketDensity P raw obs g c r₀ s (obs ω)) y)-2*physicalFieldCapBase) 0 ∂P)≤M) :
    ∃ G : Set Ω,(MeasurableSet G ∧ MeasurableSet[MeasurableSpace.comap obs ‹MeasurableSpace B›] G) ∧ P.real Gᶜ≤16*(64*L)^3*M ∧
      ∀ ω∈G,∀ y : Position,3*r/4≤‖y‖ → ‖y‖≤6*L*r →
        ‖y‖^4*(Z*coulombKernel y-potentialOf
          (conditionalPacketDensity P raw obs g c r₀ s (obs ω)) y)≤physicalSpatialCap := by
  let F := fun ω y => Z*coulombKernel y-potentialOf
    (conditionalPacketDensity P raw obs g c r₀ s (obs ω)) y
  let T := 2*physicalFieldCapBase
  let A := {y : Position | r/2≤‖y‖ ∧ ‖y‖≤8*L*r}
  let Q := fun wy : Ω × Position => max (‖wy.2‖^4*F wy.1 wy.2-T) 0
  let V := 4*Real.pi/3*(r/8)^3
  have hV : 0<V := by dsimp [V]; positivity
  have hT : 0≤T := by dsimp [T]; linarith [physicalFieldCapBase_ge_one]
  have hA : IsCompact A := cap_annulus_compact r L
  have hFmeas : Measurable (fun wy : Ω × Position => F wy.1 wy.2) := by
    have hp := measurable_conditionalPacketPotential_joint P raw obs hg hgs hm hc hr₀ hs
    have hcmeas : Measurable (fun wy : Ω × Position =>
        potentialOf (conditionalPacketDensity P raw obs g c r₀ s (obs wy.1)) wy.2) := by
      change Measurable ((fun dy : B × Position =>
        potentialOf (conditionalPacketDensity P raw obs g c r₀ s dy.1) dy.2) ∘
          (fun wy : Ω × Position => (obs wy.1,wy.2)))
      exact hp.comp ((hobs.comp measurable_fst).prodMk measurable_snd)
    exact ((measurable_coulombKernel.comp measurable_snd).const_mul Z).sub hcmeas
  have hQmeas : Measurable Q :=
    (((measurable_snd.norm.pow_const 4).mul hFmeas).sub_const T).max measurable_const
  have hQ0 : ∀ wy,0≤Q wy := fun _ => le_max_right _ _
  have HB : ∀ ω y,y∈A → Q (ω,y)≤Z*(8*L*r)^3 := by
    intro ω y hy
    exact posterior_scaled_excess_bounded P raw obs g hc hr₀ hs (obs ω) hZ hr hL hT hy.1 hy.2
  obtain ⟨hI,hi,hprob⟩ := spatial_moment_markov P hA.measurableSet hA.measure_lt_top
    hQmeas hQ0 HB (fun y hy => hM y hy.1 hy.2) (div_pos hV (by norm_num : (0:ℝ)<16))
  let G := {ω | (∫ y in A,Q (ω,y))≤V/16}
  have hIdata : Measurable (fun datum : B => ∫ y in A,
      max (‖y‖^4*(Z*coulombKernel y-potentialOf
        (conditionalPacketDensity P raw obs g c r₀ s datum) y)-T) 0) := by
    have hp := measurable_conditionalPacketPotential_joint P raw obs hg hgs hm hc hr₀ hs
    have hq : Measurable (fun dy : B × Position => max (‖dy.2‖^4*(Z*coulombKernel dy.2-potentialOf
      (conditionalPacketDensity P raw obs g c r₀ s dy.1) dy.2)-T) 0) :=
      (((measurable_snd.norm.pow_const 4).mul
      (((measurable_coulombKernel.comp measurable_snd).const_mul Z).sub hp)).sub_const T).max measurable_const
    exact hq.stronglyMeasurable.integral_prod_right'.measurable
  have hGtail : MeasurableSet[MeasurableSpace.comap obs ‹MeasurableSpace B›] G := by
    exact ⟨{datum : B | (∫ y in A,max (‖y‖^4*(Z*coulombKernel y-potentialOf
      (conditionalPacketDensity P raw obs g c r₀ s datum) y)-T) 0)≤V/16},
      measurableSet_le hIdata measurable_const,rfl⟩
  refine ⟨G,⟨measurableSet_le hI measurable_const,hGtail⟩,?_,?_⟩
  · have hGe : Gᶜ={ω | V/16<(∫ y in A,Q (ω,y))} := by ext ω; simp only [G,mem_compl_iff,mem_ofPred_eq,not_le]
    rw [hGe]
    apply hprob.trans
    have hv := cap_annulus_volume_ratio hr hL
    have he : volume.real A*M/(V/16)=16*(volume.real A/V)*M := by ring
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right hv hM0]
  · intro ω hω y hy0 hy1
    have hFn : ContinuousOn (F ω) (Metric.closedBall y (r/8)) := by
      apply (continuousOn_const.mul (continuous_norm.continuousOn.inv₀ ?_)).sub
        (conditionalPacketPotential_continuous P raw obs hg hgs hm hc hr₀ hs (obs ω)).continuousOn
      intro z hz
      have hn := (cap_ball_geometry hr hL hy0 hy1 hz).1
      have hz0 : 0<‖z‖ := by linarith
      exact ne_of_gt hz0
    have hmean := conditionalPacketField_submean P raw obs hg hgs hm hc hr₀ hs
      (obs ω) Z (div_pos hr (by norm_num : (0:ℝ)<8)) y (by linarith : r/8≤‖y‖)
    have H := annular_submean_cap hr hL hT (hi ω) hy0 hy1
      (hFn.integrableOn_compact (isCompact_closedBall _ _)) hmean
    have hω' : (∫ z in A,Q (ω,z))≤V/16 := hω
    have hsmall : 16*V⁻¹*(∫ z in A,Q (ω,z))≤1 := by
      have hh := mul_le_mul_of_nonneg_left hω' (by positivity : 0≤16*V⁻¹)
      have he : 16*V⁻¹*(V/16)=1 := by field_simp
      exact hh.trans_eq he
    change ‖y‖^4*F ω y≤physicalSpatialCap
    change ‖y‖^4*F ω y≤16*T+16*V⁻¹*(∫ z in A,Q (ω,z)) at H
    dsimp [physicalSpatialCap,T] at *
    linarith
end NeutralAtom
end

end

end OAI
