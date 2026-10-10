import Mathlib

namespace OAI

noncomputable section
open Set Polynomial
open scoped BigOperators
namespace Ostmann.Characters

theorem continuous_sign_on {S : Set ℝ} (hS : IsPreconnected S)
    {f : ℝ → ℝ} (hf : ContinuousOn f S) (hne : ∀ x ∈ S, f x ≠ 0) :
    (∀ x ∈ S, 0 < f x) ∨ (∀ x ∈ S, f x < 0) := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact Or.inl (by simp)
  rcases lt_or_gt_of_ne (hne a ha) with hneg | hpos
  · right
    intro b hb
    by_contra h
    have hbpos : 0 ≤ f b := le_of_not_gt h
    obtain ⟨x, hx, hfx⟩ := hS.intermediate_value ha hb hf ⟨hneg.le, hbpos⟩
    exact hne x hx hfx
  · left
    intro b hb
    by_contra h
    have hbneg : f b ≤ 0 := le_of_not_gt h
    obtain ⟨x, hx, hfx⟩ := hS.intermediate_value hb ha hf ⟨hbneg, hpos.le⟩
    exact hne x hx hfx

theorem polynomial_sign_on (p : ℝ[X]) {S : Set ℝ} (hS : IsPreconnected S)
    (havoid : ∀ x ∈ S, x ∉ p.roots.toFinset) :
    (∀ x ∈ S, p.eval x = 0) ∨
      (∀ x ∈ S, 0 < p.eval x) ∨ (∀ x ∈ S, p.eval x < 0) := by
  by_cases hp : p = 0
  · exact Or.inl (by simp [hp])
  right
  apply continuous_sign_on hS p.continuous.continuousOn
  intro x hx heq
  exact havoid x hx (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr heq))

theorem polynomial_relations_constant_on (p : ℝ[X]) {S : Set ℝ}
    (hS : IsPreconnected S) (havoid : ∀ x ∈ S, x ∉ p.roots.toFinset)
    {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) :
    (p.eval x ≤ 0 ↔ p.eval y ≤ 0) ∧
    (p.eval x < 0 ↔ p.eval y < 0) ∧
    (p.eval x = 0 ↔ p.eval y = 0) := by
  rcases polynomial_sign_on p hS havoid with hzero | hpos | hneg
  · simp [hzero x hx, hzero y hy]
  · have hx' := hpos x hx
    have hy' := hpos y hy
    simp [not_le.mpr hx', not_le.mpr hy', not_lt.mpr hx'.le, not_lt.mpr hy'.le,
      ne_of_gt hx', ne_of_gt hy']
  · have hx' := hneg x hx
    have hy' := hneg y hy
    simp [hx'.le, hy'.le, hx', hy', ne_of_lt hx', ne_of_lt hy']

theorem polynomial_monotone_or_antitone_on (p : ℝ[X]) {S : Set ℝ}
    (hS : Convex ℝ S) (havoid : ∀ x ∈ S, x ∉ p.derivative.roots.toFinset) :
    MonotoneOn p.eval S ∨ AntitoneOn p.eval S := by
  rcases polynomial_sign_on p.derivative hS.isPreconnected havoid with hzero | hpos | hneg
  · left
    apply monotoneOn_of_hasDerivWithinAt_nonneg hS p.continuous.continuousOn
      (fun x _ => (p.hasDerivAt x).hasDerivWithinAt)
    intro x hx
    exact le_of_eq (hzero x (interior_subset hx)).symm
  · left
    apply monotoneOn_of_hasDerivWithinAt_nonneg hS p.continuous.continuousOn
      (fun x _ => (p.hasDerivAt x).hasDerivWithinAt)
    intro x hx
    exact (hpos x (interior_subset hx)).le
  · right
    apply antitoneOn_of_hasDerivWithinAt_nonpos hS p.continuous.continuousOn
      (fun x _ => (p.hasDerivAt x).hasDerivWithinAt)
    intro x hx
    exact (hneg x (interior_subset hx)).le

theorem polynomial_div_const_monotone_or_antitone_on (p : ℝ[X]) (d : ℝ)
    {S : Set ℝ} (hS : Convex ℝ S)
    (havoid : ∀ x ∈ S, x ∉ p.derivative.roots.toFinset) :
    MonotoneOn (fun x => p.eval x / d) S ∨ AntitoneOn (fun x => p.eval x / d) S := by
  rcases polynomial_monotone_or_antitone_on p hS havoid with hmono | hanti
  · by_cases hd : 0 ≤ d
    · exact Or.inl (fun x hx y hy hxy => div_le_div_of_nonneg_right (hmono hx hy hxy) hd)
    · exact Or.inr (fun x hx y hy hxy => div_le_div_of_nonpos_of_le (le_of_not_ge hd) (hmono hx hy hxy))
  · by_cases hd : 0 ≤ d
    · exact Or.inr (fun x hx y hy hxy => div_le_div_of_nonneg_right (hanti hx hy hxy) hd)
    · exact Or.inl (fun x hx y hy hxy => div_le_div_of_nonpos_of_le (le_of_not_ge hd) (hanti hx hy hxy))

end Ostmann.Characters

end

end OAI
