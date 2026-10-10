import Mathlib
import OAI.Analysis.HardSphere.Cutoffs.CubicMoment

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

lemma free_diameterRatio_tail {c : ℝ} {M : ℝ≥0∞}
    (htail : ∀ R : ℝ, 0≤R → wiener {w | R≤‖w‖} ≤ M*ENNReal.ofReal (Real.exp (-c*R^2)))
    {L : Length} {r τ R : ℝ} (hr : 0<r) (hτr : τ ≤ r^2) (hR : 0≤R)
    (X : Configuration 1 L) :
    coordinateWiener 1 {w | R<diameterRatio r (freeTrajectory 1 L τ w X)} ≤
      3*M*ENNReal.ofReal (Real.exp (-c*(R/36)^2)) := by
  have hX : X=oneConfiguration (X 0) := by ext i j; have hi : i=0 := Subsingleton.elim _ _; subst i; rfl
  have hsub : {w | R<diameterRatio r (freeTrajectory 1 L τ w X)} ⊆
      ⋃j : Fin 3,{w | R/36≤‖w (0,j)‖} := by
    intro w hw
    by_contra hn
    have hnorm : ∀j : Fin 3, ‖w (0,j)‖<R/36 := by
      simpa only [Set.mem_iUnion,Set.mem_ofPred_eq,not_exists,not_le] using hn
    have hsum : noiseSize w ≤ R/12 := by
      unfold noiseSize
      calc
        _ ≤ ∑j : Fin 3, R/36 := Finset.sum_le_sum (fun j _ ↦ (hnorm j).le)
        _ = R/12 := by simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul]; ring
    have hd := free_diameter_noise L hr hτr w (X 0)
    rw [←hX] at hd
    change R < intervalDiameter 0 1 (freeTrajectory 1 L τ w X)/r at hw
    linarith
  have he (j : Fin 3) : coordinateWiener 1 {w | R/36≤‖w (0,j)‖} = wiener {w | R/36≤‖w‖} :=
    (measurePreserving_eval (fun _ : Direction 1 ↦ wiener) (0,j)).measure_preimage
      (measurableSet_le measurable_const measurable_norm).nullMeasurableSet
  calc
    _ ≤ coordinateWiener 1 (⋃j : Fin 3,{w | R/36≤‖w (0,j)‖}) := measure_mono hsub
    _ ≤ ∑'j : Fin 3,coordinateWiener 1 {w | R/36≤‖w (0,j)‖} := measure_iUnion_le _
    _ = 3*wiener {w | R/36≤‖w‖} := by simp [he,tsum_fintype]
    _ ≤ 3*(M*ENNReal.ofReal (Real.exp (-c*(R/36)^2))) := mul_le_mul_right (htail _ (by positivity)) _
    _ = _ := by ring

end HardSphere.PathCutoff

end
end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

def MeshRegular {L : Length} (m : ℕ) (r R C : ℝ) (ω : ConfigurationPath 1 L) : Prop :=
  (∀ j : Fin m, diameterRatio r (meshSegment j ω) ≤ R) ∧
  (∑j : Fin m,cubicCost r (meshSegment j ω)) ≤ C*(m:ℝ)

lemma meshRegular_measurable {L : Length} (m : ℕ) (r R C : ℝ) :
    MeasurableSet {ω : ConfigurationPath 1 L | MeshRegular m r R C ω} := by
  change MeasurableSet ({ω : ConfigurationPath 1 L | ∀j : Fin m, diameterRatio r (meshSegment j ω) ≤ R} ∩
    {ω | (∑j : Fin m,cubicCost r (meshSegment j ω)) ≤ C*(m:ℝ)})
  apply MeasurableSet.inter
  · have he (j : Fin m) : MeasurableSet {ω : ConfigurationPath 1 L | diameterRatio r (meshSegment j ω) ≤ R} :=
      measurableSet_le ((diameterRatio_continuous L r).comp (meshSegment_continuous L j)).measurable measurable_const
    simpa only [← Set.ofPred_forall] using MeasurableSet.iInter he
  · exact measurableSet_le (Finset.measurable_fun_sum _ (fun j _ ↦
      ((cubicCost_continuous L r).comp (meshSegment_continuous L j)).measurable)) measurable_const

lemma capSum_eq_of_max {L : Length} (m : ℕ) {r R : ℝ} (hr : 0 ≤ r)
    (ω : ConfigurationPath 1 L) (hmax : ∀j : Fin m, diameterRatio r (meshSegment j ω) ≤ R) :
    capSum m r ((1+R)^3) ω=∑j : Fin m,cubicCost r (meshSegment j ω) := by
  unfold capSum
  apply Finset.sum_congr rfl
  intro j _
  apply min_eq_left
  unfold cubicCost
  exact pow_le_pow_left₀ (by linarith [diameterRatio_nonneg hr (meshSegment j ω)]) (by linarith [hmax j]) 3

lemma mesh_irregular_sub {L : Length} {m : ℕ} {r R : ℝ} (hr : 0 ≤ r) :
    {ω : ConfigurationPath 1 L | ¬MeshRegular m r R (meanCost+1) ω} ⊆
      meshEvent m {ω | R < diameterRatio r ω} ∪
      {ω | (meanCost+1)*(m:ℝ) ≤ capSum m r ((1+R)^3) ω} := by
  intro ω hω
  by_cases hmax : ∀j : Fin m, diameterRatio r (meshSegment j ω) ≤ R
  · right
    change (meanCost+1)*(m:ℝ) ≤ capSum m r ((1+R)^3) ω
    rw [capSum_eq_of_max m hr ω hmax]
    have hn : (meanCost+1)*(m:ℝ) < ∑j : Fin m,cubicCost r (meshSegment j ω) := by
      exact lt_of_not_ge (fun h ↦ hω ⟨hmax,h⟩)
    exact hn.le
  · left
    simpa only [meshEvent,Set.mem_ofPred_eq,not_forall,not_le] using hmax

lemma free_mesh_regular_tail {c : ℝ} {M : ℝ≥0∞}
    (htail : ∀ R : ℝ, 0 ≤ R → wiener {w | R ≤ ‖w‖} ≤ M*ENNReal.ofReal (Real.exp (-c*R^2)))
    {L : Length} {r τ R : ℝ} (hr : 0 < r) (hτ : 0 < τ) (hτr : τ ≤ r^2) (hR : 0 ≤ R)
    (m : ℕ) (hm : 0 < m) (X : Configuration 1 L) :
    coordinateWiener 1 {w | ¬MeshRegular m r R (meanCost+1) (freeTrajectory 1 L ((m:ℝ)*τ) w X)} ≤
      (m:ℝ≥0∞)*(3*M*ENNReal.ofReal (Real.exp (-c*(R/36)^2)))+
      ENNReal.ofReal (Real.exp (-(m:ℝ)/((1+R)^3))) := by
  have hB : 0 < (1+R)^3 := by positivity
  have hp := meshEvent_free_bound (L:=L) m hm
    (measurableSet_lt measurable_const (diameterRatio_continuous L r).measurable) hτ
    (3*M*ENNReal.ofReal (Real.exp (-c*(R/36)^2)))
    (fun Y ↦ free_diameterRatio_tail htail hr hτr hR Y) X
  calc
    _ ≤ coordinateWiener 1 ({w | freeTrajectory 1 L ((m:ℝ)*τ) w X ∈ meshEvent m {ω | R < diameterRatio r ω}} ∪
      {w | (meanCost+1)*(m:ℝ) ≤ capSum m r ((1+R)^3) (freeTrajectory 1 L ((m:ℝ)*τ) w X)}) :=
      measure_mono (fun w hw ↦ mesh_irregular_sub hr.le hw)
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add hp (mesh_cap_tail hr hτ hτr hB m hm X))

end HardSphere.PathCutoff

end
end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

lemma free_split_lintegral {L : Length} {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (F : ConfigurationPath 1 L × ConfigurationPath 1 L → ℝ≥0∞) (hF : Measurable F)
    (X : Configuration 1 L) :
    ∫⁻w,F (configurationPrefix 1 L (splitTime s t hs ht) (freeTrajectory 1 L (s+t) w X),
      configurationSuffix 1 L (splitTime s t hs ht) (freeTrajectory 1 L (s+t) w X)) ∂coordinateWiener 1 =
    ∫⁻w₁,∫⁻w₂,F (freeTrajectory 1 L s w₁ X,
      freeTrajectory 1 L t w₂ (freeTrajectory 1 L s w₁ X 1)) ∂coordinateWiener 1 ∂coordinateWiener 1 := by
  let G : CoordinatePaths 1 × CoordinatePaths 1 → ℝ≥0∞ := fun p ↦
    F (freeTrajectory 1 L s p.1 X,freeTrajectory 1 L t p.2 (freeTrajectory 1 L s p.1 X 1))
  have hG : Measurable G := hF.comp (split_fixedTrajectory_measurable 1 L s t X)
  calc
    _ = ∫⁻w,G (fun p ↦ normalizedPrefix (splitTime s t hs ht) (w p),
        fun p ↦ normalizedSuffix (splitTime s t hs ht) (w p)) ∂coordinateWiener 1 :=
      lintegral_congr (fun w ↦ by rw [split_fixedTrajectory])
    _ = ∫⁻p,G p ∂(coordinateWiener 1).prod (coordinateWiener 1) :=
      (coordinateSplit_preserving 1 (splitTime s t hs ht) (splitTime_pos _ _ _ _)
        (splitTime_lt_one _ _ _ _)).lintegral_comp hG
    _ = _ := lintegral_prod _ hG.aemeasurable

lemma free_prefix_bound {L : Length} {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (F : ConfigurationPath 1 L → ℝ≥0∞) (hF : Measurable F) (p : ℝ≥0∞)
    (hp : ∀ X : Configuration 1 L, ∫⁻w,F (freeTrajectory 1 L s w X) ∂coordinateWiener 1 ≤ p)
    (X : Configuration 1 L) :
    ∫⁻w,F (configurationPrefix 1 L (splitTime s t hs ht) (freeTrajectory 1 L (s+t) w X)) ∂coordinateWiener 1 ≤ p := by
  have h := free_split_lintegral hs ht (fun p ↦ F p.1) (hF.comp measurable_fst) X
  dsimp only at h
  simp only [lintegral_const,measure_univ,mul_one] at h
  rw [h]
  exact hp X

lemma free_suffix_bound {L : Length} {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (F : ConfigurationPath 1 L → ℝ≥0∞) (hF : Measurable F) (p : ℝ≥0∞)
    (hp : ∀ X : Configuration 1 L, ∫⁻w,F (freeTrajectory 1 L t w X) ∂coordinateWiener 1 ≤ p)
    (X : Configuration 1 L) :
    ∫⁻w,F (configurationSuffix 1 L (splitTime s t hs ht) (freeTrajectory 1 L (s+t) w X)) ∂coordinateWiener 1 ≤ p := by
  have h := free_split_lintegral hs ht (fun p ↦ F p.2) (hF.comp measurable_snd) X
  dsimp only at h
  rw [h]
  calc
    _ ≤ ∫⁻w₁,p ∂coordinateWiener 1 := lintegral_mono (fun w ↦ hp _)
    _ = p := by simp

lemma free_prefix_event {L : Length} {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    {E : Set (ConfigurationPath 1 L)} (hE : MeasurableSet E) (p : ℝ≥0∞)
    (hp : ∀ X : Configuration 1 L,coordinateWiener 1 {w | freeTrajectory 1 L s w X ∈ E} ≤ p)
    (X : Configuration 1 L) :
    coordinateWiener 1 {w | configurationPrefix 1 L (splitTime s t hs ht) (freeTrajectory 1 L (s+t) w X) ∈ E} ≤ p := by
  apply (le_of_eq ?_).trans (free_prefix_bound hs ht (E.indicator (fun _ ↦ 1))
    (measurable_const.indicator hE) p (fun Y ↦ ?_) X)
  · have he : MeasurableSet {w | configurationPrefix 1 L (splitTime s t hs ht) (freeTrajectory 1 L (s+t) w X) ∈ E} :=
      hE.preimage (((configurationPrefix_continuous 1 L _).comp
        ((freeTrajectory_continuous 1 L (s+t)).comp (continuous_id.prodMk continuous_const))).measurable)
    change coordinateWiener 1 _=∫⁻w,({w | configurationPrefix 1 L (splitTime s t hs ht) (freeTrajectory 1 L (s+t) w X) ∈ E}.indicator (fun _ ↦ (1:ℝ≥0∞))) w ∂coordinateWiener 1
    rw [lintegral_indicator_const he,one_mul]
  · have he : MeasurableSet {w | freeTrajectory 1 L s w Y ∈ E} := hE.preimage
      ((freeTrajectory_continuous 1 L s).comp (continuous_id.prodMk continuous_const)).measurable
    change ∫⁻w,({w | freeTrajectory 1 L s w Y ∈ E}.indicator (fun _ ↦ (1:ℝ≥0∞))) w ∂coordinateWiener 1 ≤ p
    simpa only [lintegral_indicator_const he,one_mul] using hp Y

lemma free_suffix_event {L : Length} {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    {E : Set (ConfigurationPath 1 L)} (hE : MeasurableSet E) (p : ℝ≥0∞)
    (hp : ∀ X : Configuration 1 L,coordinateWiener 1 {w | freeTrajectory 1 L t w X ∈ E} ≤ p)
    (X : Configuration 1 L) :
    coordinateWiener 1 {w | configurationSuffix 1 L (splitTime s t hs ht) (freeTrajectory 1 L (s+t) w X) ∈ E} ≤ p := by
  apply (le_of_eq ?_).trans (free_suffix_bound hs ht (E.indicator (fun _ ↦ 1))
    (measurable_const.indicator hE) p (fun Y ↦ ?_) X)
  · have he : MeasurableSet {w | configurationSuffix 1 L (splitTime s t hs ht) (freeTrajectory 1 L (s+t) w X) ∈ E} :=
      hE.preimage (((configurationSuffix_continuous 1 L _).comp
        ((freeTrajectory_continuous 1 L (s+t)).comp (continuous_id.prodMk continuous_const))).measurable)
    change coordinateWiener 1 _=∫⁻w,({w | configurationSuffix 1 L (splitTime s t hs ht) (freeTrajectory 1 L (s+t) w X) ∈ E}.indicator (fun _ ↦ (1:ℝ≥0∞))) w ∂coordinateWiener 1
    rw [lintegral_indicator_const he,one_mul]
  · have he : MeasurableSet {w | freeTrajectory 1 L t w Y ∈ E} := hE.preimage
      ((freeTrajectory_continuous 1 L t).comp (continuous_id.prodMk continuous_const)).measurable
    change ∫⁻w,({w | freeTrajectory 1 L t w Y ∈ E}.indicator (fun _ ↦ (1:ℝ≥0∞))) w ∂coordinateWiener 1 ≤ p
    simpa only [lintegral_indicator_const he,one_mul] using hp Y

end HardSphere.PathCutoff

end
end

end

end OAI
