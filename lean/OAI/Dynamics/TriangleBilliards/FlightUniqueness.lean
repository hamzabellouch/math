import OAI.Dynamics.TriangleBilliards.Geometry

namespace OAI

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
namespace TriangularBilliards

namespace FlightChain

lemma initial_line {Q : Triangle} {z : Phase} (c : FlightChain Q z) (t : ℝ) :
    c.point 0 + (t - c.time 0) • (c.direction 0 : ℂ) = z.1 + t • (z.2 : ℂ) := by
  rw [c.start_point, c.start_direction]
  module

lemma previous_line {Q : Triangle} {z : Phase} (c : FlightChain Q z) (n : ℤ) (t : ℝ) :
    c.point (n - 1) + (t - c.time (n - 1)) • (c.direction (n - 1) : ℂ) =
      c.point n + (t - c.time n) • (c.direction (n - 1) : ℂ) := by
  have h := c.flight (n - 1)
  simp only [sub_add_cancel] at h
  rw [h]
  module

/-- Agreement of the four data fields at a collision; the proof fields
are proposition-valued and need no extra equality assumptions. -/
def Agree {Q : Triangle} {z : Phase} (c d : FlightChain Q z) (n : ℤ) : Prop :=
  c.time n = d.time n ∧ c.point n = d.point n ∧
    c.direction n = d.direction n ∧ c.wall n = d.wall n

lemma agree_zero {Q : Triangle} {z : Phase} (c d : FlightChain Q z) : c.Agree d 0 := by
  have hcinside (t : ℝ) (h₁ : c.time 0 < t) (h₂ : t < 0) :
      z.1 + t • (z.2 : ℂ) ∈ Q.table := by
    rw [← c.initial_line]
    exact c.inside 0 t h₁ (by simpa using h₂.trans c.zero_after)
  have hdinside (t : ℝ) (h₁ : d.time 0 < t) (h₂ : t < 0) :
      z.1 + t • (z.2 : ℂ) ∈ Q.table := by
    rw [← d.initial_line]
    exact d.inside 0 t h₁ (by simpa using h₂.trans d.zero_after)
  have hcentry : ¬ (z.1 + c.time 0 • (z.2 : ℂ) ∈ Q.table) := by
    rw [← c.initial_line]
    simpa only [sub_self, zero_smul, add_zero] using Q.side_not_table (c.on_side 0)
  have hdentry : ¬ (z.1 + d.time 0 • (z.2 : ℂ) ∈ Q.table) := by
    rw [← d.initial_line]
    simpa only [sub_self, zero_smul, add_zero] using Q.side_not_table (d.on_side 0)
  have ht := entry_time_unique (fun t => z.1 + t • (z.2 : ℂ) ∈ Q.table)
    c.zero_before d.zero_before hcinside hdinside hcentry hdentry
  have hp : c.point 0 = d.point 0 := by
    have hc := c.initial_line (c.time 0)
    have hd := d.initial_line (d.time 0)
    simp only [sub_self, zero_smul, add_zero] at hc hd
    rw [hc, hd, ht]
  refine ⟨ht, hp, c.start_direction.symm.trans d.start_direction, ?_⟩
  exact Q.side_index_unique (hp ▸ c.on_side 0) (d.on_side 0)

lemma agree_succ {Q : Triangle} {z : Phase} (c d : FlightChain Q z) (n : ℤ)
    (h : c.Agree d n) : c.Agree d (n + 1) := by
  obtain ⟨ht, hp, hv, _⟩ := h
  let P : ℝ → Prop := fun t => c.point n + (t - c.time n) • (c.direction n : ℂ) ∈ Q.table
  have hcinside : ∀ t, c.time n < t → t < c.time (n + 1) → P t := c.inside n
  have hdinside : ∀ t, c.time n < t → t < d.time (n + 1) → P t := by
    simpa only [P, ht, hp, hv] using d.inside n
  have hcexit : ¬ P (c.time (n + 1)) := by
    change ¬ c.point n + _ • (c.direction n : ℂ) ∈ Q.table
    rw [← c.flight n]
    exact Q.side_not_table (c.on_side (n + 1))
  have hdexit : ¬ P (d.time (n + 1)) := by
    change ¬ c.point n + _ • (c.direction n : ℂ) ∈ Q.table
    rw [ht, hp, hv, ← d.flight n]
    exact Q.side_not_table (d.on_side (n + 1))
  have ht' : c.time (n + 1) = d.time (n + 1) :=
    exit_time_unique P (c.increasing (by omega))
      (ht ▸ d.increasing (by omega)) hcinside hdinside hcexit hdexit
  have hp' : c.point (n + 1) = d.point (n + 1) := by
    rw [c.flight n, d.flight n, ht', ht, hp, hv]
  have hw' : c.wall (n + 1) = d.wall (n + 1) :=
    Q.side_index_unique (hp' ▸ c.on_side (n + 1)) (d.on_side (n + 1))
  refine ⟨ht', hp', ?_, hw'⟩
  apply Subtype.ext
  rw [c.specular, d.specular, hw']
  simp only [add_sub_cancel_right, hv]

lemma agree_pred {Q : Triangle} {z : Phase} (c d : FlightChain Q z) (n : ℤ)
    (h : c.Agree d n) : c.Agree d (n - 1) := by
  obtain ⟨ht, hp, hv, hw⟩ := h
  have hv' : c.direction (n - 1) = d.direction (n - 1) := by
    apply Subtype.ext
    calc
      (c.direction (n - 1) : ℂ) = reflect (Q.tangent (c.wall n)) (c.direction n : ℂ) := by
        rw [c.specular n]
        exact (reflect_involutive (Q.tangent_ne_zero _) _).symm
      _ = reflect (Q.tangent (d.wall n)) (d.direction n : ℂ) := by rw [hw, hv]
      _ = (d.direction (n - 1) : ℂ) := by
        rw [d.specular n]
        exact reflect_involutive (Q.tangent_ne_zero _) _
  let P : ℝ → Prop := fun t =>
    c.point n + (t - c.time n) • (c.direction (n - 1) : ℂ) ∈ Q.table
  have hcinside : ∀ t, c.time (n - 1) < t → t < c.time n → P t := by
    intro t h₁ h₂
    change c.point n + _ • (c.direction (n - 1) : ℂ) ∈ Q.table
    rw [← c.previous_line n t]
    exact c.inside (n - 1) t h₁ (by simpa only [sub_add_cancel] using h₂)
  have hdinside : ∀ t, d.time (n - 1) < t → t < c.time n → P t := by
    intro t h₁ h₂
    change c.point n + _ • (c.direction (n - 1) : ℂ) ∈ Q.table
    rw [ht, hp, hv', ← d.previous_line n t]
    exact d.inside (n - 1) t h₁ (by simpa only [sub_add_cancel, ← ht] using h₂)
  have hcentry : ¬ P (c.time (n - 1)) := by
    change ¬ c.point n + _ • (c.direction (n - 1) : ℂ) ∈ Q.table
    rw [← c.previous_line]
    simpa only [sub_self, zero_smul, add_zero] using Q.side_not_table (c.on_side (n - 1))
  have hdentry : ¬ P (d.time (n - 1)) := by
    change ¬ c.point n + _ • (c.direction (n - 1) : ℂ) ∈ Q.table
    rw [ht, hp, hv', ← d.previous_line]
    simpa only [sub_self, zero_smul, add_zero] using Q.side_not_table (d.on_side (n - 1))
  have ht' : c.time (n - 1) = d.time (n - 1) :=
    entry_time_unique P (c.increasing (by omega))
      (ht ▸ d.increasing (by omega)) hcinside hdinside hcentry hdentry
  have hp' : c.point (n - 1) = d.point (n - 1) := by
    have hc := c.previous_line n (c.time (n - 1))
    have hd := d.previous_line n (d.time (n - 1))
    simp only [sub_self, zero_smul, add_zero] at hc hd
    rw [hc, hd, ht', ht, hp, hv']
  refine ⟨ht', hp', hv', ?_⟩
  exact Q.side_index_unique (hp' ▸ c.on_side (n - 1)) (d.on_side (n - 1))

/-- Determinism of actual complete nonsingular specular trajectories.
Both forward and backward schemes use the same geometric reflection and
never postulate uniqueness as an assumption. -/
theorem unique {Q : Triangle} {z : Phase} (c d : FlightChain Q z) : c = d := by
  have h : ∀ n, c.Agree d n := by
    intro n
    induction n using Int.induction_on with
    | zero => exact c.agree_zero d
    | succ n hn => exact c.agree_succ d n hn
    | pred n hn => exact c.agree_pred d (-n) hn
  have ht : c.time = d.time := funext fun n => (h n).1
  have hp : c.point = d.point := funext fun n => (h n).2.1
  have hv : c.direction = d.direction := funext fun n => (h n).2.2.1
  have hw : c.wall = d.wall := funext fun n => (h n).2.2.2
  cases c
  cases d
  cases ht
  cases hp
  cases hv
  cases hw
  rfl

/-- Rebase a complete chain at a time strictly between its collisions.
The integer relabeling is forced by the designated initial flight. -/
def rebase {Q : Triangle} {z : Phase} (c : FlightChain Q z)
    (t : ℝ) (n : ℤ) (hn : c.time n < t ∧ t < c.time (n + 1)) :
    FlightChain Q (c.at t) where
  time k := c.time (k + n) - t
  point k := c.point (k + n)
  direction k := c.direction (k + n)
  wall k := c.wall (k + n)
  increasing := by
    intro a b hab
    exact sub_lt_sub_right (c.increasing (by omega)) t
  unbounded_below u := by
    obtain ⟨k, hk⟩ := c.unbounded_below (u + t)
    refine ⟨k - n, ?_⟩
    simp only [sub_add_cancel]
    linarith
  unbounded_above u := by
    obtain ⟨k, hk⟩ := c.unbounded_above (u + t)
    refine ⟨k - n, ?_⟩
    simp only [sub_add_cancel]
    linarith
  zero_before := by simpa only [zero_add, sub_lt_zero] using hn.1
  zero_after := by simpa only [add_comm 1 n, sub_pos] using hn.2
  on_side k := c.on_side (k + n)
  flight k := by
    have hi : k + 1 + n = k + n + 1 := by omega
    change c.point (k + 1 + n) = c.point (k + n) +
      ((c.time (k + 1 + n) - t) - (c.time (k + n) - t)) • (c.direction (k + n) : ℂ)
    rw [hi, sub_sub_sub_cancel_right]
    exact c.flight (k + n)
  inside k u h₁ h₂ := by
    have hk : k + 1 + n = k + n + 1 := by ring
    have h := c.inside (k + n) (u + t) (by linarith) (by rw [← hk]; linarith)
    have he : u - (c.time (k + n) - t) = u + t - c.time (k + n) := by ring
    simpa only [he] using h
  start_point := by
    rw [c.at_of_flight ⟨hn.1.le, hn.2⟩]
    simp only [zero_add, neg_sub]
  start_direction := by
    rw [c.at_of_flight ⟨hn.1.le, hn.2⟩]
    simp only [zero_add]
  specular k := by
    rw [show k - 1 + n = k + n - 1 by omega]
    exact c.specular (k + n)

lemma rebase_at {Q : Triangle} {z : Phase} (c : FlightChain Q z)
    (t : ℝ) (n : ℤ) (hn : c.time n < t ∧ t < c.time (n + 1)) (s : ℝ) :
    (c.rebase t n hn).at s = c.at (s + t) := by
  obtain ⟨k, hk⟩ := c.exists_flight (s + t)
  have hleft : (c.rebase t n hn).time (k - n) ≤ s ∧
      s < (c.rebase t n hn).time (k - n + 1) := by
    change c.time (k - n + n) - t ≤ s ∧ s < c.time (k - n + 1 + n) - t
    have hi : k - n + 1 + n = k + 1 := by ring
    rw [sub_add_cancel, hi]
    constructor <;> linarith [hk.1, hk.2]
  rw [at_of_flight _ hleft, c.at_of_flight hk]
  simp only [rebase, sub_add_cancel]
  rw [show s - (c.time k - t) = s + t - c.time k by ring]

end FlightChain

lemma billiardFlow_eq_chain {Q : Triangle} {z : Phase} (c : FlightChain Q z) (t : ℝ) :
    billiardFlow Q t z = c.at t := by
  classical
  have h : Nonempty (FlightChain Q z) := ⟨c⟩
  simp only [billiardFlow, dite_eq_left h]
  rw [FlightChain.unique (Classical.choice h) c]

/-- The exact cocycle identity on every rebased nonsingular trajectory.
Only rebasing at a collision is excluded, since Phase itself uses interior
initial states; the main theorem still needs the fixed-time exceptional
sets to be proved null. -/
lemma billiardFlow_add_of_noncollision {Q : Triangle} {z : Phase}
    (c : FlightChain Q z) (s t : ℝ) (ht : t ∉ range c.time) :
    billiardFlow Q (s + t) z = billiardFlow Q s (billiardFlow Q t z) := by
  obtain ⟨n, hn⟩ := c.exists_flight t
  have hne : c.time n ≠ t := fun h => ht ⟨n, h⟩
  let d := c.rebase t n ⟨lt_of_le_of_ne hn.1 hne, hn.2⟩
  rw [billiardFlow_eq_chain c, billiardFlow_eq_chain c,
    billiardFlow_eq_chain d, FlightChain.rebase_at]

end TriangularBilliards
end

end OAI
