import OAI.Geometry.TranslativeCovering.CylinderAngle

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CylinderProbability
open Set MeasureTheory Metric CylinderAngle ConeStretch
open scoped ENNReal

noncomputable def uniform {n : ℕ} (G : Set (Space n)) : Measure (Space n) :=
  (volume G)⁻¹ • volume.restrict G

lemma uniform_probability {n : ℕ} {G : Set (Space n)} (hG : volume G ≠ 0)
    (hGf : volume G ≠ ∞) : IsProbabilityMeasure (uniform G) := by
  constructor
  simp only [uniform,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
  exact ENNReal.inv_mul_cancel hG hGf

lemma uniform_le {n : ℕ} {G S : Set (Space n)} (hG : MeasurableSet G) :
    uniform G S ≤ (volume G)⁻¹*volume (S ∩ G) := by
  rw [uniform,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply' hG]

lemma uniform_section {n : ℕ} [NeZero n] {G : Set (Space n)} (hG : MeasurableSet G)
    {D L ξ : ℝ} (hD : 0 < D) (hL : 0 < L) (hξ : 0 < ξ)
    (hGsub : G ⊆ closedBall (0 : Space n) D)
    (hGlarge : volume (closedBall (0 : Space n) D) ≤ 4*volume G)
    (u q : Space n) (hu : ‖u‖ = 1) :
    uniform G {x | x-q ≠ 0 ∧ ‖x-q‖ ≤ L ∧ ProjectiveCaps.angle u (x-q) ≤ ξ} ≤
      ENNReal.ofReal (12*((n:ℝ)+1)*(L*ξ/D)^(n-1)) := by
  have hGf : volume G ≠ ∞ := ne_top_of_le_ne_top (isCompact_closedBall (0 : Space n) D).measure_ne_top
    (measure_mono hGsub)
  have hG0 : volume G ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hGlarge
    exact (ne_of_gt (measure_closedBall_pos volume (0 : Space n) hD)) (le_zero_iff.mp hGlarge)
  let c : ℝ := 3*((n:ℝ)+1)*(L*ξ/D)^(n-1)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hsub : {x : Space n | x-q ≠ 0 ∧ ‖x-q‖ ≤ L ∧ ProjectiveCaps.angle u (x-q) ≤ ξ} ∩ G ⊆
      {x : Space n | ‖x‖ ≤ D ∧ x-q ≠ 0 ∧ ‖x-q‖ ≤ L ∧ ProjectiveCaps.angle u (x-q) ≤ ξ} := by
    intro x hx
    exact ⟨mem_closedBall_zero_iff.mp (hGsub hx.2),hx.1⟩
  calc
    _ ≤ (volume G)⁻¹*(ENNReal.ofReal c*volume (closedBall (0 : Space n) D)) :=
      (uniform_le hG).trans (mul_le_mul_right ((measure_mono hsub).trans
        (angular_section_volume u hu q hD hL hξ)) _)
    _ ≤ (volume G)⁻¹*(ENNReal.ofReal c*(4*volume G)) := by gcongr
    _ = 4*ENNReal.ofReal c := by
      rw [show (volume G)⁻¹*(ENNReal.ofReal c*(4*volume G)) =
        (4*ENNReal.ofReal c)*((volume G)⁻¹*volume G) by ring,
        ENNReal.inv_mul_cancel hG0 hGf,mul_one]
    _ = _ := by
      rw [show (4:ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
      congr 1
      dsimp [c]
      ring

def pairEvent {n : ℕ} (p q : Space n) (L ξ : ℝ) : Set (Space n × Space n) :=
  {z | z.1-p ≠ 0 ∧ ‖z.1-p‖ ≤ L ∧ z.2-q ≠ 0 ∧ ‖z.2-q‖ ≤ L ∧
     ProjectiveCaps.angle (z.1-p) (z.2-q) ≤ ξ}

lemma pairEvent_measurable {n : ℕ} (p q : Space n) (L ξ : ℝ) :
    MeasurableSet (pairEvent p q L ξ) := by
  apply MeasurableSet.inter
  · exact (isClosed_eq (continuous_fst.sub continuous_const) continuous_const).measurableSet.compl
  · apply MeasurableSet.inter
    · exact measurableSet_le (continuous_fst.sub continuous_const).norm.measurable measurable_const
    · apply MeasurableSet.inter
      · exact (isClosed_eq (continuous_snd.sub continuous_const) continuous_const).measurableSet.compl
      · exact (measurableSet_le (continuous_snd.sub continuous_const).norm.measurable measurable_const).inter
          (measurableSet_le (measurable_angle.comp ((measurable_fst.sub measurable_const).prodMk
            (measurable_snd.sub measurable_const))) measurable_const)

lemma pair_probability {n : ℕ} [NeZero n] {G : Set (Space n)} (hG : MeasurableSet G)
    {D L ξ : ℝ} (hD : 0 < D) (hL : 0 < L) (hξ : 0 < ξ)
    (hGsub : G ⊆ closedBall (0 : Space n) D)
    (hGlarge : volume (closedBall (0 : Space n) D) ≤ 4*volume G)
    (p q : Space n) :
    ((uniform G).prod (uniform G)) (pairEvent p q L ξ) ≤
      ENNReal.ofReal (12*((n:ℝ)+1)*(L*ξ/D)^(n-1)) := by
  have hGf : volume G ≠ ∞ := ne_top_of_le_ne_top (isCompact_closedBall (0 : Space n) D).measure_ne_top
    (measure_mono hGsub)
  have hG0 : volume G ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hGlarge
    exact (ne_of_gt (measure_closedBall_pos volume (0 : Space n) hD)) (le_zero_iff.mp hGlarge)
  have := uniform_probability hG0 hGf
  rw [Measure.prod_apply (pairEvent_measurable p q L ξ)]
  calc
    _ ≤ ∫⁻ _y : Space n,ENNReal.ofReal (12*((n:ℝ)+1)*(L*ξ/D)^(n-1)) ∂uniform G := by
      apply lintegral_mono
      intro y
      dsimp only
      by_cases hy : y-p = 0
      · have he : Prod.mk y ⁻¹' pairEvent p q L ξ = ∅ := by ext x; simp [pairEvent,hy]
        rw [he,measure_empty]; exact bot_le
      · let u := ‖y-p‖⁻¹ • (y-p)
        have hyn : 0 < ‖y-p‖ := norm_pos_iff.mpr hy
        have hu : ‖u‖ = 1 := by simp [u,norm_smul,hyn.ne']
        have he (x : Space n) : ProjectiveCaps.angle u x = ProjectiveCaps.angle (y-p) x := by
          simp only [u,ProjectiveCaps.angle,InnerProductGeometry.angle_smul_left_of_pos _ _ (inv_pos.mpr hyn)]
        have hsub : Prod.mk y ⁻¹' pairEvent p q L ξ ⊆
            {x | x-q ≠ 0 ∧ ‖x-q‖ ≤ L ∧ ProjectiveCaps.angle u (x-q) ≤ ξ} := by
          intro x hx
          exact ⟨hx.2.2.1,hx.2.2.2.1,by rw [he]; exact hx.2.2.2.2⟩
        exact (measure_mono hsub).trans (uniform_section hG hD hL hξ hGsub hGlarge u q hu)
    _ = _ := by simp

end CylinderProbability

end OAI
