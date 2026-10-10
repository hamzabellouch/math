import OAI.Probability.LatticePassage.MeanTimeConstant
import OAI.Probability.LatticePassage.NaturalMoment

namespace OAI

namespace CompanionFPP
open MeasureTheory Real Finset Filter Topology

noncomputable def targetCocycle (z : Vertex) (ω : Environment) (x y : Vertex) : ℝ :=
  passageTime ω x z - passageTime ω y z

@[fun_prop] theorem measurable_targetCocycle (z x y : Vertex) :
    Measurable (fun ω : Environment => targetCocycle z ω x y) :=
  (measurable_passageTime x z).sub (measurable_passageTime y z)

theorem integrable_targetCocycle (z x y : Vertex) :
    Integrable (fun ω : Environment => targetCocycle z ω x y) environmentLaw :=
  (integrable_passageTime x z).sub (integrable_passageTime y z)

theorem targetCocycle_add (z : Vertex) (ω : Environment) (x y w : Vertex) :
    targetCocycle z ω x w = targetCocycle z ω x y + targetCocycle z ω y w := by
  unfold targetCocycle
  ring

theorem targetCocycle_dominated : ∀ᵐ ω ∂environmentLaw, ∀ z x y : Vertex,
    |targetCocycle z ω x y| ≤ passageTime ω x y := by
  filter_upwards [passageTime_properties] with ω hω
  intro z x y
  apply abs_le.mpr
  have h₁ := hω.2.2.2 x y z
  have h₂ := hω.2.2.2 y x z
  rw [hω.2.2.1 y x] at h₂
  unfold targetCocycle
  constructor <;> linarith

theorem targetCocycle_translation (a z x y : Vertex) (ω : Environment) :
    targetCocycle (a+z) ω (a+x) (a+y) =
      targetCocycle z (environmentTranslation a ω) x y := by
  simp only [targetCocycle, passageTime_translation]

noncomputable def averagedTargetCocycle (d : Vertex) (N : ℕ)
    (ω : Environment) (x y : Vertex) : ℝ :=
  (∑ k ∈ range N, targetCocycle (scaleVertex (k+1) d) ω x y) / N

theorem averagedTargetCocycle_add (d : Vertex) (N : ℕ) (ω : Environment) (x y z : Vertex) :
    averagedTargetCocycle d N ω x z =
      averagedTargetCocycle d N ω x y + averagedTargetCocycle d N ω y z := by
  simp only [averagedTargetCocycle, targetCocycle, sum_sub_distrib]
  ring

theorem integrable_averagedTargetCocycle (d x y : Vertex) (N : ℕ) :
    Integrable (fun ω : Environment => averagedTargetCocycle d N ω x y) environmentLaw := by
  exact (integrable_finsetSum _ (fun k _ => integrable_targetCocycle _ _ _)).div_const _

theorem averagedTargetCocycle_dominated (d : Vertex) (N : ℕ) (hN : 1 ≤ N) :
    ∀ᵐ ω ∂environmentLaw, ∀ x y : Vertex,
      |averagedTargetCocycle d N ω x y| ≤ passageTime ω x y := by
  filter_upwards [targetCocycle_dominated] with ω hω
  intro x y
  unfold averagedTargetCocycle
  rw [abs_div, show |(N : ℝ)| = (N : ℝ) from abs_of_nonneg (Nat.cast_nonneg N)]
  apply (div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg N)).trans
  have hs : (∑ k ∈ range N, |targetCocycle (scaleVertex (k+1) d) ω x y|) ≤
      (N : ℝ)*passageTime ω x y := by
    simpa using sum_le_sum (s := range N) (fun k _ => hω (scaleVertex (k+1) d) x y)
  apply (div_le_div_of_nonneg_right hs (Nat.cast_nonneg N)).trans
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  exact le_of_eq (mul_div_cancel_left₀ _ hn)

lemma integral_targetCocycle_step (d : Vertex) (k : ℕ) :
    (∫ ω : Environment, targetCocycle (scaleVertex (k+1) d) ω 0 d ∂environmentLaw) =
      meanPassageSequence d (k+1) - meanPassageSequence d k := by
  rw [show (fun ω : Environment => targetCocycle (scaleVertex (k+1) d) ω 0 d) =
    (fun ω => passageTime ω 0 (scaleVertex (k+1) d) -
      passageTime ω d (scaleVertex (k+1) d)) from rfl,
    integral_sub (integrable_passageTime _ _) (integrable_passageTime _ _)]
  have ht := mean_passageTime_translation d 0 (scaleVertex k d)
  have he : scaleVertex (k+1) d = d + scaleVertex k d := by
    rw [scaleVertex_add]
    simp [scaleVertex, add_comm]
  simp only [add_zero] at ht
  rw [he, ht]
  simp only [meanPassageSequence, he]

theorem integral_averagedTargetCocycle (d : Vertex) (N : ℕ) :
    (∫ ω : Environment, averagedTargetCocycle d N ω 0 d ∂environmentLaw) =
      meanPassageSequence d N / N := by
  unfold averagedTargetCocycle
  rw [integral_div, integral_finsetSum _ (fun k _ => integrable_targetCocycle _ _ _)]
  simp_rw [integral_targetCocycle_step]
  rw [sum_range_sub]
  have hz : meanPassageSequence d 0 = 0 := by
    unfold meanPassageSequence
    apply integral_eq_zero_of_ae
    filter_upwards [passageTime_properties] with ω hω
    have hs : scaleVertex 0 d = (0 : Vertex) := by ext <;> simp [scaleVertex]
    rw [hs]
    exact hω.2.1 0
  rw [hz, sub_zero]

theorem mean_averagedTargetCocycle_tendsto (d : Vertex) :
    Tendsto (fun N : ℕ => ∫ ω : Environment, averagedTargetCocycle d N ω 0 d ∂environmentLaw)
      atTop (𝓝 (directionalMeanConstant d)) := by
  simp_rw [integral_averagedTargetCocycle]
  exact meanPassageSequence_tendsto d

end CompanionFPP

end OAI
