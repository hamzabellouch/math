import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProbeImageBridge

namespace OAI

/-! # Combining the two restrictions on the same probe endpoint -/

noncomputable section
namespace PolycyclicRecognition

/-- Change the cell predicate without changing the chosen pair of lifts. -/
theorem map_cell_lift_conditions {N D Z : Type*} {cell : Set Z}
    {S : N → D → Prop} {P Q : N → D → Z → Prop}
    (h : ∃ u d, S u d ∧ ∀ z ∈ cell, P u d z)
    (hmap : ∀ u d z, z ∈ cell → P u d z → Q u d z) :
    ∃ u d, S u d ∧ ∀ z ∈ cell, Q u d z := by
  obtain ⟨u, d, he, hP⟩ := h
  exact ⟨u, d, he, fun z hz => hmap u d z hz (hP z hz)⟩

variable {N D G Q : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]

omit [Group G] [MetricSpace G] [IsIsometricSMul G G] in
/-- Choose factor lifts everywhere while retaining the simultaneous
restrictions wherever the eventual geometric construction applies. -/
theorem choose_eventual_probe_lifts {J : ℕ → Type*}
    (project : N × D → G) (hsurj : Function.Surjective project)
    (endpoint : ∀ n, J n → G → G) (points : ∀ n, J n → Finset G)
    (P : ∀ n, J n → G → N × D → Prop)
    (h : ∀ᶠ n in Filter.atTop, ∀ j, ∀ x ∈ points n j,
      ∃ p, project p = endpoint n j x ∧ P n j x p) :
    ∃ p : ∀ n, J n → G → N × D,
      (∀ n j x, project (p n j x) = endpoint n j x) ∧
      ∀ᶠ n in Filter.atTop, ∀ j, ∀ x ∈ points n j, P n j x (p n j x) := by
  classical
  let good := fun n => ∀ j, ∀ x ∈ points n j,
    ∃ p, project p = endpoint n j x ∧ P n j x p
  have hp (n : ℕ) (j : J n) (x : G) :
      ∃ p, project p = endpoint n j x ∧ (good n → x ∈ points n j → P n j x p) := by
    by_cases hg : good n
    · by_cases hx : x ∈ points n j
      · obtain ⟨p, he, hP⟩ := hg j x hx
        exact ⟨p, he, fun _ _ => hP⟩
      · obtain ⟨p, he⟩ := hsurj (endpoint n j x)
        exact ⟨p, he, fun _ hmem => (hx hmem).elim⟩
    · obtain ⟨p, he⟩ := hsurj (endpoint n j x)
      exact ⟨p, he, fun hg' => (hg hg').elim⟩
  choose p he hP using hp
  refine ⟨p, he, ?_⟩
  filter_upwards [h] with n hn
  intro j x hx
  exact hP n j x hn hx

/-- The first path's quotient condition and the bridged second path's
coordinate conditions hold together for one lift of the first endpoint. -/
theorem exists_two_frame_probe_lift
    (project : N → D → G) (act : G → Q → Q) (oneQ : Q)
    (cell : Set (N × D)) (region : Set Q)
    (base anchor first second : G) (r : ℝ)
    (B : N → D → Prop) (C : D → N × D → Prop)
    (P : N → D → N × D → Prop)
    (hfirst : ∃ u d, project u d = base⁻¹ * first ∧ B u d ∧
      ∀ z ∈ cell, act ((base⁻¹ * first) * project z.1 z.2) oneQ ∈ region ∧ C d z)
    (hsecond : ∀ bridge : G, dist 1 bridge ≤ r →
      ∃ u d, project u d = (anchor⁻¹ * second) * bridge ∧ ∀ z ∈ cell, P u d z)
    (hdist : dist second first ≤ r) :
    ∃ u d, project u d = anchor⁻¹ * first ∧ ∀ z ∈ cell,
      act (base⁻¹ * (first * project z.1 z.2)) oneQ ∈ region ∧ P u d z := by
  obtain ⟨_, _, _, _, hquot⟩ := hfirst
  have hd : dist 1 (second⁻¹ * first) ≤ r := by
    rw [dist_one_inv_mul_eq]
    exact hdist
  obtain ⟨u, d, he, hcoord⟩ := hsecond (second⁻¹ * first) hd
  refine ⟨u, d, ?_, ?_⟩
  · simpa only [mul_assoc, mul_inv_cancel_left] using he
  · intro z hz
    exact ⟨by simpa only [mul_assoc] using (hquot z hz).1, hcoord z hz⟩

end PolycyclicRecognition

end

end OAI
