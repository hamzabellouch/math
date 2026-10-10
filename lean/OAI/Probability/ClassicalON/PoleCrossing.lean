import OAI.Probability.ClassicalON.AnnulusPartition

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def crossingIndicator (left right : E → V) (I O : Set V) (η : E → Bool) : ℝ :=
  if bondCrossing left right I O η then 1 else 0

omit [Fintype V] [Fintype E] in
theorem crossingIndicator_nonneg (left right : E → V) (I O : Set V) (η : E → Bool) :
    0≤crossingIndicator left right I O η := by unfold crossingIndicator; split_ifs <;> positivity

omit [Fintype V] [Fintype E] in
theorem crossingIndicator_monotone (left right : E → V) (I O : Set V) :
    Monotone (crossingIndicator left right I O) := by
  intro η ξ hη
  have h : bondCrossing left right I O η → bondCrossing left right I O ξ := by
    rintro ⟨x,hx,y,hy,hxy⟩
    exact ⟨x,hx,y,hy,bondConnected_mono left right x y hη hxy⟩
  unfold crossingIndicator
  split_ifs <;> simp_all

theorem pinnedBondNumerator_sub (μ : Measure Amplitude) [IsFiniteMeasure μ]
    (left right : E → V) (b : E → ℝ) (B : Set V) (f g : (E → Bool) → ℝ) :
    pinnedBondNumerator μ left right b B (fun η => f η-g η)=
      pinnedBondNumerator μ left right b B f-pinnedBondNumerator μ left right b B g := by
  unfold pinnedBondNumerator
  simp only [mul_sub,Finset.sum_sub_distrib]
  apply integral_sub
  all_goals exact compact_integrable ((continuous_pinWeightedSum _ _ _ _ _).comp
    ((continuous_glueAmplitude B).comp (continuous_const.prodMk continuous_id)))

theorem pole_crossing_ratio (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    (I O : Set V) (hIO : Disjoint I O) :
    poleBondMean left right b (I∪O) (fun _ => true) (crossingIndicator left right I O)=
      1-(poleSystem left right b (I∪O) (fun v => layerSigns I v)).Z (fun _ => 1)/
        (poleSystem left right b (I∪O) (fun _ => true)).Z (fun _ => 1) := by
  rw [poleBondMean_eq_pinnedBondMean,layer_Z _ _ _ _ _ hIO,positive_Z,
    mul_div_mul_left _ _ (ne_of_gt (pinNormalization_pos (I∪O)))]
  have he : (fun η : E → Bool => if bondCrossing left right I O η then (0:ℝ) else 1)=
      (fun η => 1-crossingIndicator left right I O η) := by
    funext η
    unfold crossingIndicator
    split_ifs <;> norm_num
  rw [he,pinnedBondNumerator_sub,sub_div,div_self
    (ne_of_gt (pinnedBondNumerator_one_pos sphericalAmplitudeLaw _ _ _ hb _))]
  unfold pinnedBondMean
  ring

theorem freeBondMean_le_poleBondMean (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    (B : Set V) (f : (E → Bool) → ℝ) (hf : ∀ η,0≤f η) (hm : Monotone f) :
    freeBondMean left right b f≤poleBondMean left right b B (fun _ => true) f := by
  rw [freeBondMean_eq_jointBondMean _ _ _ hb,poleBondMean_eq_pinnedBondMean]
  exact jointBond_le_pinnedBond _ _ _ _ hb _ _ hf hm

omit [Fintype V] [Fintype E] in
theorem rotate_pole (a : V → ℝ) (x : V) (h : a x=1) :
    spinRotation (SpinSystem.potentialRotation a Real.pi x) (poleSpin true)=poleSpin false := by
  apply Subtype.ext
  change NormedSpace.exp ((Real.pi*a x) • axisC) (poleSpin true).val=(poleSpin false).val
  rw [h,mul_one,exp_axisC_pi_apply]
  ext i
  fin_cases i <;> simp [poleSpin,cylindricalSpin,transverseAmplitude,signValue]

omit [Fintype V] [Fintype E] in
theorem rotation_zero_potential (a : V → ℝ) (t : ℝ) (x : V) (h : a x=0) (s : Spin 3) :
    spinRotation (SpinSystem.potentialRotation a t x) s=s := by
  apply Subtype.ext
  change NormedSpace.exp ((t*a x) • axisC) s.val=s.val
  simp [h,zero_smul ℝ axisC]

end ClassicalON

end

end OAI
