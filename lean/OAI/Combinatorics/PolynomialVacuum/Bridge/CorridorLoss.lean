import OAI.Combinatorics.PolynomialVacuum.Bridge.BridgeTail
import OAI.Combinatorics.PolynomialVacuum.Bridge.LogCorridorDecay
import OAI.Combinatorics.PolynomialVacuum.Bridge.CorridorLossTarget

namespace OAI

namespace PolynomialVacuumBridge.Corridor

theorem restricted_tsum_loss {α : Type*} (f : α → ℝ) (P Q : α → Prop) [DecidablePred Q]
    (hf : Summable f) (hpos : ∀ x, 0 ≤ f x) (hpq : ∀ x, ¬P x → Q x) :
    0 ≤ (∑' x, f x) - (∑' x : {x // P x}, f x.val) ∧
    (∑' x, f x) - (∑' x : {x // P x}, f x.val) ≤
      ∑' x, (if Q x then f x else 0) := by
  classical
  have he := hf.tsum_subtype_add_tsum_subtype_compl {x | P x}
  change (∑' x : {x // P x}, f x.val) + (∑' x : {x // ¬P x}, f x.val) = (∑' x, f x) at he
  have hloss : (∑' x, f x) - (∑' x : {x // P x}, f x.val) =
      ∑' x : {x // ¬P x}, f x.val := by linarith
  rw [hloss]
  change 0 ≤ (∑' x : ↥({x | ¬P x} : Set α), f x.val) ∧
    (∑' x : ↥({x | ¬P x} : Set α), f x.val) ≤ _
  rw [tsum_subtype]
  constructor
  · apply tsum_nonneg
    intro x
    by_cases h : P x <;> simp [Set.indicator,h,hpos]
  · have hi : (∑' x, ({x | ¬P x} : Set α).indicator f x) ≤
        ∑' x, ({x | Q x} : Set α).indicator f x := by
      apply Summable.tsum_le_tsum _ (hf.indicator _) (hf.indicator _)
      intro x
      by_cases h : P x
      · simp [Set.indicator,h]
        split_ifs <;> simp [hpos]
      · simp [Set.indicator,h,hpq x h]
    refine hi.trans_eq (tsum_congr fun value => ?_)
    by_cases hQ : Q value <;> simp [Set.indicator,hQ]

theorem not_confined_reaches (h : ℕ) (p : BridgePath h) (hp : ¬InLogCorridor p) :
    BridgeReaches p ((h : ℝ)*(Real.log (h : ℝ))^2) := by
  classical
  unfold InLogCorridor at hp
  push Not at hp
  obtain ⟨v,hv,hlt⟩ := hp
  exact ⟨v,hv,hlt.le⟩

theorem corridor_mass_loss_bound (h : ℕ) (hh : 1 ≤ h) :
    0 ≤ bridgeMass h - confinedMass h ∧
    bridgeMass h - confinedMass h ≤
      tailConstant*((h : ℝ)+1)^2*
        Real.exp (-tailRate*((h : ℝ)*(Real.log (h : ℝ))^2)/(h+1)) := by
  classical
  have hu := restricted_tsum_loss (weight (h := h)) InLogCorridor
    (fun p => BridgeReaches p ((h : ℝ)*(Real.log (h : ℝ))^2))
    (bridge_weight_summable h hh) (fun p => pow_nonneg criticalActivity_pos.le _)
    (not_confined_reaches h)
  refine ⟨hu.1,hu.2.trans ?_⟩
  apply (bridgeTailMass_bound h hh ((h : ℝ)*(Real.log (h : ℝ))^2) (by positivity)).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply le_mul_of_one_le_right tailConstant_pos.le
  nlinarith [Nat.cast_nonneg (α := ℝ) h]

theorem corridor_length_loss_bound (h : ℕ) (hh : 1 ≤ h) :
    0 ≤ bridgeLengthMass h - confinedLengthMass h ∧
    bridgeLengthMass h - confinedLengthMass h ≤
      tailConstant*spatialConstant*((h : ℝ)+1)^2*
        Real.exp (-(tailRate/2)*((h : ℝ)*(Real.log (h : ℝ))^2)/(h+1)) := by
  classical
  have hu := restricted_tsum_loss (firstLengthWeight (h := h)) InLogCorridor
    (fun p => BridgeReaches p ((h : ℝ)*(Real.log (h : ℝ))^2))
    (bridge_length_summable h hh)
    (fun p => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg criticalActivity_pos.le _))
    (not_confined_reaches h)
  exact ⟨hu.1,hu.2.trans (bridgeTailLengthMass_bound h hh ((h : ℝ)*(Real.log (h : ℝ))^2) (by positivity))⟩

theorem corridor_loss_superpolynomial : CorridorLossSuperpolynomial := by
  intro A
  have hm := log_square_exponential_beats_power tailConstant tailRate
    tailConstant_pos tailRate_pos A
  have hl := log_square_exponential_beats_power (tailConstant*spatialConstant) (tailRate/2)
    (mul_pos tailConstant_pos spatialConstant_pos) (div_pos tailRate_pos (by norm_num)) A
  filter_upwards [Filter.eventually_ge_atTop 1,hm,hl] with h hh hm hl
  exact ⟨(corridor_mass_loss_bound h hh).1,(corridor_mass_loss_bound h hh).2.trans hm,
    (corridor_length_loss_bound h hh).1,(corridor_length_loss_bound h hh).2.trans hl⟩

end PolynomialVacuumBridge.Corridor

end OAI
