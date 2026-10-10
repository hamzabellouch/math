import Mathlib

namespace OAI

/-!
# Scalar steps of the refinement update

These are the min/max and first-crossing calculations in Sections 5 and 7
of *An Almost-Linear Approximation Scheme for Edit Distance* (2026).
They are internal lemmas, not the main algorithmic theorem.
-/

namespace EditApproximation

/-- The nonzero branch of the refinement update, for a nonempty online list.
An empty list returns the cone minimum directly. -/
noncomputable def refinementUpdate (δ cone online : ℝ) : ℝ :=
  min cone (max (cone / (1 + δ)) online)

theorem refinementUpdate_sandwich {δ cone online lower : ℝ}
    (hcone : lower ≤ cone) (honline : lower ≤ online) :
    lower ≤ refinementUpdate δ cone online ∧
      refinementUpdate δ cone online ≤ cone :=
  ⟨le_min hcone (honline.trans (le_max_right _ _)), min_le_left _ _⟩

theorem refinementUpdate_div_le {δ cone online : ℝ}
    (hδ : 0 ≤ δ) (hcone : 0 ≤ cone) :
    cone / (1 + δ) ≤ refinementUpdate δ cone online := by
  apply le_min _ (le_max_left _ _)
  apply (div_le_iff₀ (by positivity : 0 < 1 + δ)).2
  nlinarith

/-- The cone sandwich gives the multiplicative spatial regularity,
regardless of the independently sampled online values. -/
theorem refinementUpdate_spatial {δ cone cone' online online' charge : ℝ}
    (hδ : 0 ≤ δ) (hcone' : 0 ≤ cone') (hspatial : cone ≤ cone' + charge) :
    refinementUpdate δ cone online ≤
      (1 + δ) * refinementUpdate δ cone' online' + charge := by
  have hdiv := refinementUpdate_div_le (online := online') hδ hcone'
  have hmul := (div_le_iff₀ (by positivity : 0 < 1 + δ)).1 hdiv
  have hup : refinementUpdate δ cone online ≤ cone := min_le_left _ _
  nlinarith

/-- Prefix step of Proposition `prop:node-regret`: if the group estimate
succeeds, any excess over the sampled action is paid by its decrement. -/
theorem refinementUpdate_prefix {δ κ cone online action oldAction b c error : ℝ}
    (hδ : 0 < δ) (hκ : 0 ≤ κ) (hc0 : 0 ≤ c) (hb : b ≤ c)
    (hc : c ≤ action) (hmonotone : action ≤ oldAction)
    (honline : online ≤ action) (hbellman : cone ≤ oldAction)
    (hgroup : cone ≤ (1 + δ) * action + error * b)
    (herror : error * b ≤ κ * δ * b) :
    max c (refinementUpdate δ cone online) ≤
      action + κ * (oldAction - action) := by
  apply max_le (by nlinarith) _
  by_cases hu : refinementUpdate δ cone online ≤ action
  · nlinarith
  · have hact : action < refinementUpdate δ cone online := lt_of_not_ge hu
    have hdiv : action < cone / (1 + δ) := by
      have hmax : action < max (cone / (1 + δ)) online :=
        hact.trans_le (min_le_right _ _)
      exact (lt_max_iff.mp hmax).resolve_right (not_lt_of_ge honline)
    have hcone : (1 + δ) * action < cone := by
      have := (lt_div_iff₀ (by positivity : 0 < 1 + δ)).1 hdiv
      nlinarith
    have hdecrement : δ * b < oldAction - action := by
      nlinarith
    have hcone0 : 0 ≤ cone :=
      (mul_nonneg (by positivity : 0 ≤ 1 + δ) (hc0.trans hc)).trans hcone.le
    have hdivle : cone / (1 + δ) ≤ cone := by
      apply (div_le_iff₀ (by positivity : 0 < 1 + δ)).2
      nlinarith
    have heq : refinementUpdate δ cone online = cone / (1 + δ) := by
      rw [refinementUpdate, max_eq_left (honline.trans hdiv.le)]
      exact min_eq_right hdivle
    rw [heq]
    apply (div_le_iff₀ (by positivity : 0 < 1 + δ)).2
    have hpay : κ * δ * b ≤ κ * (oldAction - action) :=
      by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hdecrement.le hκ
    have hslack : 0 ≤ δ * (κ * (oldAction - action)) :=
      mul_nonneg hδ.le (mul_nonneg hκ (sub_nonneg.mpr hmonotone))
    nlinarith

/-- The crossing iteration is paid once; later Bellman bounds use the
same action and make the clipped regret nonpositive. -/
theorem refinementUpdate_crossing {δ cone online action c : ℝ}
    (hδ : 0 ≤ δ) (hc : 0 ≤ c) (haction : action < c)
    (hgroup : cone ≤ (1 + δ) * action + δ * c) :
    max c (refinementUpdate δ cone online) ≤ c + 2 * δ * c := by
  have hup : refinementUpdate δ cone online ≤ cone := min_le_left _ _
  have hmul := mul_le_mul_of_nonneg_left haction.le (by positivity : 0 ≤ 1 + δ)
  apply max_le <;> nlinarith

theorem clipped_regret_nonpos {parent cost childClipped charge : ℝ}
    (hparent : parent ≤ cost) (hconnection : cost ≤ charge + childClipped) :
    max cost parent - charge - childClipped ≤ 0 := by
  rw [max_eq_left hparent]
  linarith

end EditApproximation

end OAI
