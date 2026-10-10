import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCharacterRows

namespace OAI

/-! The model polynomial of a bounded stopped row has the expected
b^(5/6) size, directly from its literal norm support. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma bounded_annular_model_norm (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    {b M : ℝ} (hb : 0 < b) (hM : 0 ≤ M)
    (hS : ∀ a ∈ S, primary a ∧ b/2 ≤ norm a ∧ norm a ≤ b)
    (hβ : ∀ a ∈ S, ‖β a‖ ≤ M) (u : ℝ) :
    ‖dispersionModel S β u‖ ≤ (18*(2:ℝ)^(1/6:ℝ)*M)*b^(5/6:ℝ) := by
  have hrow (a : Eisenstein) (ha : a ∈ S) :
      ‖β a*normTwist u a*((norm a^(-1/6:ℝ):ℝ):ℂ)‖ ≤ M*(b/2)^(-1/6:ℝ) := by
    rw [norm_mul,norm_mul,norm_normTwist,mul_one,Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg a) _)]
    exact mul_le_mul (hβ a ha)
      (Real.rpow_le_rpow_of_nonpos (by positivity) (hS a ha).2.1 (by norm_num))
      (Real.rpow_nonneg (norm_nonneg a) _) hM
  have hpow : b*(b/2)^(-1/6:ℝ) = (2:ℝ)^(1/6:ℝ)*b^(5/6:ℝ) := by
    rw [Real.div_rpow hb.le (by norm_num),div_eq_mul_inv,
      ←Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    norm_num only [neg_div,neg_neg]
    calc
      _ = (2:ℝ)^(1/6:ℝ)*(b^(1:ℝ)*b^(-1/6:ℝ)) := by rw [Real.rpow_one]; ring_nf
      _ = _ := by rw [←Real.rpow_add hb]; norm_num
  apply (norm_sum_le S (fun a => β a*normTwist u a*((norm a^(-1/6:ℝ):ℝ):ℂ))).trans
  calc
    _ ≤ ∑ _a ∈ S, M*(b/2)^(-1/6:ℝ) := Finset.sum_le_sum hrow
    _ = (S.card:ℝ)*(M*(b/2)^(-1/6:ℝ)) := by simp
    _ ≤ (18*b)*(M*(b/2)^(-1/6:ℝ)) := mul_le_mul_of_nonneg_right
      (primary_support_card_le S hb.le (fun a ha => ⟨(hS a ha).1,(hS a ha).2.2⟩))
      (by positivity)
    _ = (18*M)*(b*(b/2)^(-1/6:ℝ)) := by ring
    _ = _ := by rw [hpow]; ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_model_norm {ξ : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (W : ι → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) →
      ∀ (selected : Eisenstein → Eisenstein → Prop) (e : Eisenstein) (b u v : ℝ),
      0 < b → b ≤ X →
      ‖dispersionModel (stoppedIntervalSupport ι X (b/2) b e)
        (stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W selected) v‖ ≤ K*b^(5/6:ℝ) := by
  obtain ⟨M,hM,hbound⟩ := stopped_interval_energy (ι := ι) hξ hξz
  refine ⟨18*(2:ℝ)^(1/6:ℝ)*M,by positivity,?_⟩
  filter_upwards [hbound] with X hbound
  intro W hW selected e b u v hb hbX
  apply bounded_annular_model_norm _ _ hb hM.le
  · intro a ha
    have hs := stoppedIntervalSupport_spec X (b/2) b e ha
    exact ⟨hs.1,(Finset.mem_filter.mp ha).2.2.2.1.le,hs.2.2⟩
  · exact (hbound W hW selected u (b/2) b e hb.le hbX).1

end CubicFirstMoment

end

end OAI
