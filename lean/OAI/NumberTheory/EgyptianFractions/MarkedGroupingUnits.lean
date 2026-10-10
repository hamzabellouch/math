import OAI.NumberTheory.EgyptianFractions.MarkedGrouping

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- A rational with numerator dividing `K`, after scaling, is a unit fraction. -/
theorem rational_divisor_unit (q K d e t : ℕ) (hq : 0 < q) (hK : 0 < K)
    (hd : 0 < d) (hdq : d ∣ q) (he : 0 < e) (heK : e ∣ K) (ht : 0 < t) :
    0 < (q / d) * (K / e) * t ∧
    (1 : ℚ) / (((q / d) * (K / e) * t : ℕ) : ℚ) =
      ((d : ℚ) / ((q : ℚ) * (K : ℚ))) * ((e : ℚ) / (t : ℚ)) := by
  have hqd : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hdq) hd
  have hKe : 0 < K / e := Nat.div_pos (Nat.le_of_dvd hK heK) he
  constructor
  · positivity
  have hqeq : (q : ℚ) = (d : ℚ) * (q / d : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' hdq).symm
  have hKeq : (K : ℚ) = (e : ℚ) * (K / e : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' heK).symm
  have hdR : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have heR : (e : ℚ) ≠ 0 := by exact_mod_cast he.ne'
  rw [hqeq, hKeq]
  push_cast
  field_simp

/-- A supply expresses every small integer as a short sum of rational divisors. -/
def HasRationalDivisorSupply (m K B : ℕ) : Prop :=
  ∀ s : ℕ, 1 ≤ s → s ≤ m ^ 4 →
    ∃ terms : List (ℕ × ℕ), terms.length ≤ B ∧
      (∀ et ∈ terms, 0 < et.1 ∧ et.1 ∣ K ∧ 0 < et.2) ∧
      (terms.map (fun et => (et.1 : ℚ) / (et.2 : ℚ))).sum = (s : ℚ)

/-- Convert a single supplied group to positive unit fractions. -/
theorem supplied_group_units (m q K B d s : ℕ) (hq : 0 < q) (hK : 0 < K)
    (hd : 0 < d) (hdq : d ∣ q) (hs : 1 ≤ s) (hsm : s ≤ m ^ 4)
    (hsupply : HasRationalDivisorSupply m K B) :
    ∃ denoms : List ℕ, denoms.length ≤ B ∧ (∀ n ∈ denoms, 0 < n) ∧
      (denoms.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum =
        ((d : ℚ) * (s : ℚ)) / ((q : ℚ) * (K : ℚ)) := by
  obtain ⟨terms, hlen, hterms, hsum⟩ := hsupply s hs hsm
  let f : ℕ × ℕ → ℕ := fun et => (q / d) * (K / et.1) * et.2
  refine ⟨terms.map f, by simpa using hlen, ?_, ?_⟩
  · intro n hn
    obtain ⟨et, het, rfl⟩ := List.mem_map.mp hn
    obtain ⟨he, heK, ht⟩ := hterms et het
    exact (rational_divisor_unit q K d et.1 et.2 hq hK hd hdq he heK ht).1
  · rw [List.map_map]
    have hmap : terms.map ((fun n : ℕ => (1 : ℚ) / (n : ℚ)) ∘ f) =
        terms.map (fun et => ((d : ℚ) / ((q : ℚ) * (K : ℚ))) *
          ((et.1 : ℚ) / (et.2 : ℚ))) := by
      apply List.map_congr_left
      intro et het
      obtain ⟨he, heK, ht⟩ := hterms et het
      exact (rational_divisor_unit q K d et.1 et.2 hq hK hd hdq he heK ht).2
    rw [hmap, List.sum_map_mul_left, hsum]
    ring

/-- Concatenate supplied groups, retaining a linear length budget. -/
theorem supplied_groups_units (m q K B : ℕ) (hq : 0 < q) (hK : 0 < K)
    (hsupply : HasRationalDivisorSupply m K B) (groups : List (ℕ × ℕ))
    (hgroups : ∀ g ∈ groups, 0 < g.1 ∧ g.1 ∣ q ∧ 1 ≤ g.2 ∧ g.2 ≤ m ^ 4) :
    ∃ denoms : List ℕ, denoms.length ≤ B * groups.length ∧
      (∀ n ∈ denoms, 0 < n) ∧
      (denoms.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum =
        (((groups.map (fun g => g.1 * g.2)).sum : ℕ) : ℚ) / ((q : ℚ) * (K : ℚ)) := by
  induction groups with
  | nil => exact ⟨[], by simp⟩
  | cons g groups ih =>
      obtain ⟨hd, hdq, hs, hsm⟩ := hgroups g (by simp)
      obtain ⟨front, hflen, hfpos, hfsum⟩ :=
        supplied_group_units m q K B g.1 g.2 hq hK hd hdq hs hsm hsupply
      obtain ⟨tail, htlen, htpos, htsum⟩ := ih (by
        intro g hg
        exact hgroups g (by simp [hg]))
      refine ⟨front ++ tail, ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_cons]
        nlinarith
      · intro n hn
        rcases List.mem_append.mp hn with hn | hn
        · exact hfpos n hn
        · exact htpos n hn
      · simp only [List.map_append, List.sum_append, hfsum, htsum,
          List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_mul]
        ring

/-- Grouping a numerator using a rational-divisor supply yields a short unit-fraction list.
No distinctness is asserted here; later cleanup is applied only to the tail. -/
theorem marked_grouping_units_from_list_supply (m q K B X : ℕ) (hm : 2 ≤ m)
    (hq : 0 < q) (hK : 0 < K) (hXq : X ≤ q)
    (hdensity : HasMarkedDivisorDensity m q)
    (hsupply : HasRationalDivisorSupply m K B) :
    ∃ denoms : List ℕ,
      (denoms.length : ℝ) ≤ (B : ℝ) *
        (Real.log (X : ℝ) / (2 * Real.log (m : ℝ)) + 1) ∧
      (∀ n ∈ denoms, 0 < n) ∧
      (denoms.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum =
        (X : ℚ) / ((q : ℚ) * (K : ℚ)) := by
  obtain ⟨groups, hlen, hgroups, hsum⟩ := marked_grouping m q X hm hdensity hXq
  obtain ⟨denoms, hdlen, hdpos, hdsum⟩ :=
    supplied_groups_units m q K B hq hK hsupply groups hgroups
  refine ⟨denoms, ?_, hdpos, ?_⟩
  · have hdlenR : (denoms.length : ℝ) ≤ (B : ℝ) * (groups.length : ℝ) := by
      exact_mod_cast hdlen
    exact hdlenR.trans (mul_le_mul_of_nonneg_left hlen (by positivity))
  · simpa [hsum] using hdsum

end Problem337

end

end OAI
