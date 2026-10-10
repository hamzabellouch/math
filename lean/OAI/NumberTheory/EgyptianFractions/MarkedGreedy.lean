import Mathlib

namespace OAI
noncomputable section
namespace Problem337

/-- The integer ceiling of `q/R`, presented without rational rounding. -/
theorem marked_ceiling_spec (R q : ℕ) (hR : 0 < R) (hRq : R < q) :
    ∃ a : ℕ, 2 ≤ a ∧ a ≤ q ∧ (a - 1) * R < q ∧ q ≤ a * R := by
  let a := (q - 1) / R + 1
  have hq : 0 < q := by omega
  have hlow : ((q - 1) / R) * R ≤ q - 1 := Nat.div_mul_le_self _ _
  have hhigh : q - 1 < ((q - 1) / R + 1) * R := by
    have hr := Nat.mod_lt (q - 1) hR
    have he := Nat.mod_add_div (q - 1) R
    nlinarith
  have ha2 : 2 ≤ a := by
    have hdiv : 1 ≤ (q - 1) / R := (Nat.one_le_div_iff hR).2 (by omega)
    dsimp [a]
    omega
  refine ⟨a, ha2, ?_, ?_, ?_⟩
  · have hmul : (a - 1) ≤ (a - 1) * R := by nlinarith
    have : (a - 1) * R ≤ q - 1 := by simpa [a] using hlow
    omega
  · simpa [a] using (lt_of_le_of_lt hlow (by omega : q - 1 < q))
  · dsimp [a]
    omega

/-- One marked greedy step avoids the prescribed denominator, with an unreduced numerator. -/
theorem marked_greedy_step_data (m R q : ℕ)
    (hm : 4 ≤ m) (hR : 0 < R) (hRq : R < q) :
    ∃ n c : ℕ, 2 ≤ n ∧ n ≠ m ∧ n ≤ q + 1 ∧
      q ≤ n * R ∧ n * R = q + c ∧ c < q ∧ c < 2 * R ∧
      (n ≠ m + 1 → c < R) ∧
      (R : ℚ) / q = 1 / (n : ℚ) + (c : ℚ) / (n * q : ℕ) ∧
      (c : ℚ) / (n * q : ℕ) < 1 / (n : ℚ) := by
  obtain ⟨a, ha2, haq, halow, hahigh⟩ := marked_ceiling_spec R q hR hRq
  let n := if a = m then m + 1 else a
  have hn2 : 2 ≤ n := by dsimp [n]; split <;> omega
  have hnm : n ≠ m := by dsimp [n]; split <;> omega
  have hnq : n ≤ q + 1 := by dsimp [n]; split <;> omega
  have han : a ≤ n := by dsimp [n]; split <;> omega
  have hhigh : q ≤ n * R := le_trans hahigh (Nat.mul_le_mul_right R han)
  let c := n * R - q
  have heq : n * R = q + c := by dsimp [c]; omega
  have hc2 : c < 2 * R := by
    by_cases ham : a = m
    · have hn : n = m + 1 := by simp [n, ham]
      have hlow : (m - 1) * R < q := by simpa [ham] using halow
      have hm1 : m - 1 + 1 = m := by omega
      rw [hn] at heq
      nlinarith
    · have hn : n = a := by simp [n, ham]
      rw [hn] at heq
      have ha1 : a - 1 + 1 = a := by omega
      nlinarith
  have hcord : n ≠ m + 1 → c < R := by
    intro hne
    have ham : a ≠ m := by intro he; simp [n, he] at hne
    have hn : n = a := by simp [n, ham]
    rw [hn] at heq
    have ha1 : a - 1 + 1 = a := by omega
    nlinarith
  have hcq : c < q := by
    by_cases ham : a = m
    · have hlow : (m - 1) * R < q := by simpa [ham] using halow
      have hm1 : 3 ≤ m - 1 := by omega
      nlinarith
    · have hn : n = a := by simp [n, ham]
      rw [hn] at heq
      have ha1 : a - 1 + 1 = a := by omega
      have : c < R := by nlinarith
      omega
  have hnQ : (0 : ℚ) < n := by exact_mod_cast (by omega : 0 < n)
  have hqQ : (0 : ℚ) < q := by exact_mod_cast (by omega : 0 < q)
  have heqQ : (n : ℚ) * R = q + c := by exact_mod_cast heq
  refine ⟨n, c, hn2, hnm, hnq, hhigh, heq, hcq, hc2, hcord, ?_, ?_⟩
  · push_cast
    field_simp
    nlinarith
  · push_cast
    apply (div_lt_div_iff₀ (mul_pos hnQ hqQ) hnQ).2
    have hcqQ : (c : ℚ) < q := by exact_mod_cast hcq
    nlinarith

/-- The ordinary steps square the size of the remainder. -/
theorem marked_greedy_square (R q n c : ℕ) (hR : 0 < R) (hq : 0 < q)
    (hn : 0 < n) (heq : n * R = q + c) (hc : c < R) :
    (c : ℚ) / (n * q : ℕ) < ((R : ℚ) / q) ^ 2 := by
  have hR' : (0 : ℚ) < R := by exact_mod_cast hR
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have heq' : (n : ℚ) * R = q + c := by exact_mod_cast heq
  have hc' : (c : ℚ) < R := by exact_mod_cast hc
  have hc0 : (0 : ℚ) ≤ c := by positivity
  have hprod : (c : ℚ) * q < (n : ℚ) * R ^ 2 := by
    calc
      (c : ℚ) * q < R * q := mul_lt_mul_of_pos_right hc' hq'
      _ ≤ (n : ℚ) * R ^ 2 := by nlinarith
  push_cast
  apply (div_lt_iff₀ (mul_pos hn' hq')).2
  field_simp
  nlinarith


/-- A finite trace of unreduced marked greedy steps. -/
inductive MarkedGreedySteps (m : ℕ) : ℕ → ℕ → List ℕ → ℕ → ℕ → Prop
  | nil (R q : ℕ) : MarkedGreedySteps m R q [] R q
  | cons (R q n c : ℕ) (L : List ℕ) (Rf qf : ℕ)
      (hn : 2 ≤ n) (hnm : n ≠ m) (hnq : n ≤ q + 1)
      (heq : n * R = q + c) (hcq : c < q) (hcR : c < 2 * R)
      (hord : n ≠ m + 1 → c < R)
      (tail : MarkedGreedySteps m c (n * q) L Rf qf) :
      MarkedGreedySteps m R q (n :: L) Rf qf

/-- The process stops by the threshold, since each active step increases the denominator. -/
theorem exists_marked_greedy_steps (m T R q : ℕ) (hm : 4 ≤ m)
    (hq : 0 < q) (hRq : R < q) (hbound : q < T ^ 2) :
    ∃ L : List ℕ, ∃ Rf qf : ℕ, MarkedGreedySteps m R q L Rf qf ∧
      (Rf = 0 ∨ T ≤ qf) ∧ qf < T ^ 2 := by
  by_cases hstop : R = 0 ∨ T ≤ q
  · exact ⟨[], R, q, .nil R q, hstop, hbound⟩
  · have hR : 0 < R := by omega
    have hqT : q < T := by omega
    obtain ⟨n, c, hn, hnm, hnq, hhigh, heq, hcq, hcR, hord, hfrac, hrem⟩ :=
      marked_greedy_step_data m R q hm hR hRq
    have hqq : q < n * q := by nlinarith
    have hnext : n * q < T ^ 2 := by nlinarith
    obtain ⟨L, Rf, qf, htrace, hstop', hbound'⟩ :=
      exists_marked_greedy_steps m T c (n * q) hm
        (Nat.mul_pos (by omega) hq) (by omega) hnext
    exact ⟨n :: L, Rf, qf, .cons R q n c L Rf qf hn hnm hnq heq hcq hcR hord htrace,
      hstop', hbound'⟩
termination_by T - q

/-- Every chosen denominator is above the preceding threshold; the numerator remains small. -/
theorem MarkedGreedySteps.invariants {m R q Rf qf : ℕ} {L : List ℕ}
    (h : MarkedGreedySteps m R q L Rf qf) (t : ℕ)
    (ht : 1 ≤ t) (hq : 0 < q) (hgap : t * R < q)
    (hsmall : R < 2 * m) (hphase : R < m ∨ m < t) :
    qf > 0 ∧ t * Rf < qf ∧ Rf < 2 * m ∧
      (∀ n ∈ L, t < n ∧ n ≠ m) ∧ L.Pairwise (· < ·) ∧
      (∀ n ∈ L, n * Rf < qf) := by
  induction h generalizing t with
  | nil R q => exact ⟨hq, hgap, hsmall, by simp, by simp, by simp⟩
  | cons R q n c L Rf qf hn hnm hnq heq hcq hcR hord tail ih =>
    have htn : t < n := by
      by_contra h
      have hnt : n ≤ t := by omega
      have := Nat.mul_le_mul_right R hnt
      omega
    have hcsmall : c < 2 * m := by
      by_cases hne : n ≠ m + 1
      · exact lt_trans (hord hne) hsmall
      · have hnm1 : n = m + 1 := by omega
        have hRm : R < m := by rcases hphase with h | h <;> omega
        omega
    have hcphase : c < m ∨ m < n := by
      by_cases hmn : m < n
      · exact Or.inr hmn
      · have hne : n ≠ m + 1 := by omega
        have hRm : R < m := by rcases hphase with h | h <;> omega
        exact Or.inl (lt_trans (hord hne) hRm)
    have hnextq : 0 < n * q := by positivity
    have hnextgap : n * c < n * q := Nat.mul_lt_mul_of_pos_left hcq (by omega)
    obtain ⟨hqf, hgapf, hsmallf, hlist, hpair, hfinal⟩ :=
      ih n (by omega) hnextq hnextgap hcsmall hcphase
    refine ⟨hqf, ?_, hsmallf, ?_, ?_, ?_⟩
    · exact lt_of_le_of_lt (Nat.mul_le_mul_right Rf (by omega : t ≤ n)) hgapf
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨htn, hnm⟩
      · exact ⟨lt_trans htn (hlist a ha).1, (hlist a ha).2⟩
    · exact List.pairwise_cons.mpr ⟨fun a ha => (hlist a ha).1, hpair⟩
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hgapf
      · exact hfinal a ha

/-- The unreduced denominator is exactly the initial one times the chosen denominators. -/
theorem MarkedGreedySteps.denominator {m R q Rf qf : ℕ} {L : List ℕ}
    (h : MarkedGreedySteps m R q L Rf qf) : qf = q * L.prod := by
  induction h with
  | nil => simp
  | cons R q n c L Rf qf hn hnm hnq heq hcq hcR hord tail ih =>
    simpa [List.prod_cons, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using ih

/-- Telescoping the successive unreduced fraction identities. -/
theorem MarkedGreedySteps.sum {m R q Rf qf : ℕ} {L : List ℕ}
    (h : MarkedGreedySteps m R q L Rf qf) (hq : 0 < q) :
    (R : ℚ) / q = (L.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum + (Rf : ℚ) / qf := by
  induction h with
  | nil R q => simp
  | cons R q n c L Rf qf hn hnm hnq heq hcq hcR hord tail ih =>
    have hnQ : (0 : ℚ) < n := by exact_mod_cast (by omega : 0 < n)
    have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
    have heqQ : (n : ℚ) * R = q + c := by exact_mod_cast heq
    have hstep : (R : ℚ) / q = 1 / (n : ℚ) + (c : ℚ) / (n * q : ℕ) := by
      push_cast
      field_simp
      nlinarith
    have htail := ih (by positivity : 0 < n * q)
    rw [hstep, htail]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- The marked greedy prefix, with all arithmetic conclusions except its length estimate. -/
theorem exists_marked_greedy_prefix (m T : ℕ) (hm : 4 ≤ m) (hT : 2 * m ^ 2 ≤ T) :
    ∃ L : List ℕ, ∃ R q : ℕ,
      MarkedGreedySteps m (m - 1) m L R q ∧
      L.Pairwise (· < ·) ∧ (∀ n ∈ L, 2 ≤ n ∧ n ≠ m) ∧
      q = m * L.prod ∧ 0 < q ∧ R < 2 * m ∧
      (1 : ℚ) = 1 / (m : ℚ) + (L.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum + (R : ℚ) / q ∧
      q < T ^ 2 ∧ (R = 0 ∨ T ≤ q) ∧
      m * R < q ∧ (∀ n ∈ L, n * R < q) := by
  have hm0 : 0 < m := by omega
  have hmT0 : m < T := by nlinarith
  have hTT : T ≤ T ^ 2 := by nlinarith
  have hmT : m < T ^ 2 := lt_of_lt_of_le hmT0 hTT
  obtain ⟨L, R, q, htrace, hstop, hbound⟩ :=
    exists_marked_greedy_steps m T (m - 1) m hm hm0 (by omega) hmT
  obtain ⟨hq, hgap, hsmall, hlist, hpair, hfinal⟩ :=
    htrace.invariants 1 (by omega) hm0 (by omega) (by omega) (Or.inl (by omega))
  have hsum := htrace.sum hm0
  have hmarker : m * R < q := by
    rcases hstop with hzero | hlarge
    · simp [hzero, hq]
    · nlinarith
  refine ⟨L, R, q, htrace, hpair, ?_, htrace.denominator, hq, hsmall, ?_,
    hbound, hstop, hmarker, hfinal⟩
  · intro n hn
    exact ⟨by have := (hlist n hn).1; omega, (hlist n hn).2⟩
  · have hmQ : (0 : ℚ) < m := by exact_mod_cast hm0
    have hm1 : ((m - 1 : ℕ) : ℚ) = (m : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ m)]
      norm_num
    have htotal : (1 : ℚ) = 1 / (m : ℚ) + ((m - 1 : ℕ) : ℚ) / m := by
      rw [hm1]
      field_simp
      ring
    rw [hsum] at htotal
    linarith

/-- Stopping also records that the denominator before the last step is below the threshold. -/
theorem exists_marked_greedy_steps_bounded (m T R q : ℕ) (hm : 4 ≤ m)
    (hq : 0 < q) (hRq : R < q) (hbound : q < T ^ 2) :
    ∃ L : List ℕ, ∃ Rf qf : ℕ, MarkedGreedySteps m R q L Rf qf ∧
      (Rf = 0 ∨ T ≤ qf) ∧ qf < T ^ 2 ∧
      (L ≠ [] → q * L.dropLast.prod < T) := by
  by_cases hstop : R = 0 ∨ T ≤ q
  · exact ⟨[], R, q, .nil R q, hstop, hbound, by simp⟩
  · have hR : 0 < R := by omega
    have hqT : q < T := by omega
    obtain ⟨n, c, hn, hnm, hnq, hhigh, heq, hcq, hcR, hord, hfrac, hrem⟩ :=
      marked_greedy_step_data m R q hm hR hRq
    have hqq : q < n * q := by nlinarith
    have hnext : n * q < T ^ 2 := by nlinarith
    obtain ⟨L, Rf, qf, htrace, hstop', hbound', hactive⟩ :=
      exists_marked_greedy_steps_bounded m T c (n * q) hm
        (Nat.mul_pos (by omega) hq) (by omega) hnext
    refine ⟨n :: L, Rf, qf, .cons R q n c L Rf qf hn hnm hnq heq hcq hcR hord htrace,
      hstop', hbound', ?_⟩
    intro _
    cases L with
    | nil => simpa using hqT
    | cons a L =>
      have ha := hactive (by simp)
      simpa [List.dropLast_cons_cons, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using ha
termination_by T - q


/-- Every nonempty marked trace starts by removing one half. -/
theorem MarkedGreedySteps.first {m n Rf qf : ℕ} {L : List ℕ}
    (h : MarkedGreedySteps m (m - 1) m (n :: L) Rf qf) (hm : 4 ≤ m) :
    n = 2 ∧ MarkedGreedySteps m (m - 2) (2 * m) L Rf qf := by
  cases h with
  | cons R q n c L Rf qf hn hnm hnq heq hcq hcR hord tail =>
    have hm1 : m - 1 + 1 = m := by omega
    have hne : n ≠ m + 1 := by
      intro he
      rw [he] at heq
      nlinarith
    have hc : c < m - 1 := hord hne
    have hn2 : n = 2 := by nlinarith
    have hm2 : m - 2 + 2 = m := by omega
    have hc2 : c = m - 2 := by nlinarith
    refine ⟨hn2, ?_⟩
    simpa [hn2, hc2] using tail


/-- A trace can be cut at any chosen prefix. -/
theorem MarkedGreedySteps.split {m R q Rf qf : ℕ} {A B : List ℕ}
    (h : MarkedGreedySteps m R q (A ++ B) Rf qf) :
    ∃ Ri qi : ℕ, MarkedGreedySteps m R q A Ri qi ∧
      MarkedGreedySteps m Ri qi B Rf qf := by
  induction A generalizing R q with
  | nil => exact ⟨R, q, .nil R q, h⟩
  | cons a A ih =>
    cases h with
    | cons R q n c L Rf qf hn hnm hnq heq hcq hcR hord tail =>
      obtain ⟨Ri, qi, hleft, hright⟩ := ih tail
      exact ⟨Ri, qi, .cons R q a c A Ri qi hn hnm hnq heq hcq hcR hord hleft, hright⟩

/-- The state before the final step has a positive numerator. -/
theorem MarkedGreedySteps.penultimate {m R q Rf qf : ℕ} {L : List ℕ}
    (h : MarkedGreedySteps m R q L Rf qf) (hL : L ≠ []) :
    ∃ Ri qi : ℕ, MarkedGreedySteps m R q L.dropLast Ri qi ∧
      0 < Ri ∧ 0 < qi ∧ qi = q * L.dropLast.prod := by
  have hsplit : MarkedGreedySteps m R q (L.dropLast ++ [L.getLast hL]) Rf qf := by
    simpa only [List.dropLast_append_getLast hL] using h
  obtain ⟨Ri, qi, hleft, hright⟩ := hsplit.split
  refine ⟨Ri, qi, hleft, ?_, ?_, hleft.denominator⟩
  · cases hright with
    | cons R q n c L Rf qf hn hnm hnq heq hcq hcR hord tail => omega
  · cases hright with
    | cons R q n c L Rf qf hn hnm hnq heq hcq hcR hord tail => omega

/-- The full arithmetic prefix contract also recording the final active state. -/
theorem exists_marked_greedy_prefix_bounded (m T : ℕ) (hm : 4 ≤ m) (hT : 2 * m ^ 2 ≤ T) :
    ∃ L : List ℕ, ∃ R q : ℕ,
      MarkedGreedySteps m (m - 1) m L R q ∧
      L.Pairwise (· < ·) ∧ (∀ n ∈ L, 2 ≤ n ∧ n ≠ m) ∧
      q = m * L.prod ∧ 0 < q ∧ R < 2 * m ∧
      (1 : ℚ) = 1 / (m : ℚ) + (L.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum + (R : ℚ) / q ∧
      q < T ^ 2 ∧ (R = 0 ∨ T ≤ q) ∧
      m * R < q ∧ (∀ n ∈ L, n * R < q) ∧
      (L ≠ [] → m * L.dropLast.prod < T) := by
  have hm0 : 0 < m := by omega
  have hmT0 : m < T := by nlinarith
  have hTT : T ≤ T ^ 2 := by nlinarith
  have hmT : m < T ^ 2 := lt_of_lt_of_le hmT0 hTT
  obtain ⟨L, R, q, htrace, hstop, hbound, hactive⟩ :=
    exists_marked_greedy_steps_bounded m T (m - 1) m hm hm0 (by omega) hmT
  obtain ⟨hq, hgap, hsmall, hlist, hpair, hfinal⟩ :=
    htrace.invariants 1 (by omega) hm0 (by omega) (by omega) (Or.inl (by omega))
  have hsum := htrace.sum hm0
  have hmarker : m * R < q := by
    rcases hstop with hzero | hlarge
    · simp [hzero, hq]
    · nlinarith
  refine ⟨L, R, q, htrace, hpair, ?_, htrace.denominator, hq, hsmall, ?_,
    hbound, hstop, hmarker, hfinal, hactive⟩
  · intro n hn
    exact ⟨by have := (hlist n hn).1; omega, (hlist n hn).2⟩
  · have hmQ : (0 : ℚ) < m := by exact_mod_cast hm0
    have hm1 : ((m - 1 : ℕ) : ℚ) = (m : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ m)]
      norm_num
    have htotal : (1 : ℚ) = 1 / (m : ℚ) + ((m - 1 : ℕ) : ℚ) / m := by
      rw [hm1]
      field_simp
      ring
    rw [hsum] at htotal
    linarith

end Problem337

end

end OAI
