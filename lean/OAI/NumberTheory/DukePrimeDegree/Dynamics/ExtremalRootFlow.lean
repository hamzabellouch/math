import OAI.NumberTheory.DukePrimeDegree.Dynamics.HorosphereIsolatingFlow

namespace OAI

/-!
# A neutral flow for the shortest remaining positive root

For type A roots in a fixed positive chamber, choose a root of shortest
index distance. Moving its two diagonal weights to their midpoint makes
that root neutral and keeps every other remaining root strictly contracting.
This is the root-removal step in EK2003 Proposition 8.3.
-/

noncomputable section
open Finset
open scoped BigOperators

namespace DukePrimeDegree

/-- Equalize the selected two coordinates while keeping all other
coordinates at their original ordered values. -/
def midpointRootRaw {n : ℕ} (a b r : Fin n) : ℝ :=
  if r = a ∨ r = b then ((a.val : ℝ) + (b.val : ℝ)) / 2 else (r.val : ℝ)

lemma midpointRootRaw_equal {n : ℕ} (a b : Fin n) :
    midpointRootRaw a b a = midpointRootRaw a b b := by
  simp [midpointRootRaw]

lemma midpointRootRaw_strict {n : ℕ} {a b r s : Fin n}
    (hab : a < b) (hrs : r < s)
    (hgap : (b.val : ℝ) - a.val ≤ (s.val : ℝ) - r.val)
    (hne : ¬ (r = a ∧ s = b)) :
    midpointRootRaw a b r < midpointRootRaw a b s := by
  have hab' : (a.val : ℝ) < b.val := by exact_mod_cast hab
  have hrs' : (r.val : ℝ) < s.val := by exact_mod_cast hrs
  by_cases hra : r = a
  · subst r
    have hsb : s ≠ b := fun h => hne ⟨rfl, h⟩
    have hsa : s ≠ a := (ne_of_lt hrs).symm
    simp only [midpointRootRaw, true_or, ite_true, hsa, hsb, or_self, ite_false]
    linarith
  by_cases hrb : r = b
  · subst r
    have hsa : s ≠ a := by
      intro h
      subst s
      exact (lt_asymm hab hrs)
    have hsb : s ≠ b := (ne_of_lt hrs).symm
    simp [midpointRootRaw, hsa, hsb]
    linarith
  by_cases hsa : s = a
  · subst s
    simp only [midpointRootRaw, hra, hrb, or_self, ite_false, true_or, ite_true]
    linarith
  by_cases hsb : s = b
  · subst s
    simp only [midpointRootRaw, hra, hrb, hsa, false_or, or_self, ite_false, ite_true]
    linarith
  simp only [midpointRootRaw, hra, hrb, hsa, hsb, or_self, ite_false]
  exact hrs'

/-- A nonempty collection of positive type-A roots has a root which can
be made neutral while every other root remains strictly contracting. -/
theorem exists_extremal_root_flow (d : ℕ)
    (S : Finset (Fin (d + 1) × Fin (d + 1))) (hS : S.Nonempty)
    (hpos : ∀ p ∈ S, p.1 < p.2) :
    ∃ p ∈ S, ∃ ell : Fin (d + 1) → ℝ, (∑ r, ell r) = 0 ∧
      ell p.1 = ell p.2 ∧ ∀ q ∈ S, q ≠ p → ell q.1 < ell q.2 := by
  obtain ⟨p, hp, hmin⟩ := S.exists_min_image (fun q => q.2.val - q.1.val) hS
  refine ⟨p, hp, centerWeights d (midpointRootRaw p.1 p.2),
    centerWeights_sum d _, ?_, ?_⟩
  · unfold centerWeights
    rw [midpointRootRaw_equal]
  · intro q hq hqp
    apply sub_neg.mp
    rw [centerWeights_sub]
    apply sub_neg.mpr
    apply midpointRootRaw_strict (hpos p hp) (hpos q hq)
    · have hle := hmin q hq
      have hpLe : p.1.val ≤ p.2.val := (hpos p hp).le
      have hqLe : q.1.val ≤ q.2.val := (hpos q hq).le
      have hcast : ((p.2.val - p.1.val : ℕ) : ℝ) ≤ ((q.2.val - q.1.val : ℕ) : ℝ) := by
        exact_mod_cast hle
      simpa only [Nat.cast_sub hpLe, Nat.cast_sub hqLe] using hcast
    · intro h
      exact hqp (Prod.ext h.1 h.2)

/-- Removing a shortest positive root leaves a collection closed under
root addition. This is the ideal needed for the product induction. -/
theorem erase_shortest_root_closed (n : ℕ)
    (S : Finset (Fin n × Fin n))
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hcomp : ∀ a b c : Fin n, (a, b) ∈ S → (b, c) ∈ S → (a, c) ∈ S)
    (p : Fin n × Fin n)
    (hmin : ∀ q ∈ S, p.2.val - p.1.val ≤ q.2.val - q.1.val) :
    ∀ a b c : Fin n, (a, b) ∈ S.erase p → (b, c) ∈ S.erase p → (a, c) ∈ S.erase p := by
  intro a b c hab hbc
  have habS := (Finset.mem_erase.mp hab).2
  have hbcS := (Finset.mem_erase.mp hbc).2
  refine Finset.mem_erase.mpr ⟨?_, hcomp a b c habS hbcS⟩
  intro he
  subst p
  have hsmall := hmin (a, b) habS
  have h₁ := hpos (a, b) habS
  have h₂ := hpos (b, c) hbcS
  change a.val < b.val at h₁
  change b.val < c.val at h₂
  change c.val - a.val ≤ b.val - a.val at hsmall
  omega

end DukePrimeDegree

end

end OAI
