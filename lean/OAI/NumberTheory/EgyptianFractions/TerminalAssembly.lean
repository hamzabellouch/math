import OAI.NumberTheory.EgyptianFractions.TerminalRecursion
import OAI.NumberTheory.EgyptianFractions.TerminalDepth
import OAI.NumberTheory.EgyptianFractions.ResidueStep
import OAI.NumberTheory.EgyptianFractions.BinaryExpansion

namespace OAI
noncomputable section

namespace Problem337.TerminalAssembly

/-- The constructive terminal stage of the dense-family argument, with an
explicit logarithmic length bound. The only remaining number-theoretic input
is the asserted supply of divisor residues. -/
theorem terminal_expansion_of_residue_supply
    (M U : ℕ) (D α S : ℝ) (hUM : U < M)
    (hD : 1 ≤ D) (hα : 0 < α) (hα1 : α < 1)
    (hS : 1 ≤ S) (hlogS : 1 ≤ Real.log S)
    (hU : (U : ℝ) ≤ Real.exp S)
    (hdiv : 2 ^ TerminalDepth.binaryExponent D S ∣ M)
    (hstep : ∀ u : ℕ, u ≤ U → S ^ D < (u : ℝ) →
      ∃ t z h : ℕ, 0 < t ∧ 0 < z ∧ t ∣ M ∧
        (h : ℝ) ≤ (u : ℝ) ^ α ∧ t + h = u * z) :
    ∀ u : ℕ, u ≤ U → ∃ l : List ℕ,
      (∀ n ∈ l, 2 ≤ n) ∧
      (l.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum = (u : ℚ) / M ∧
      (l.length : ℝ) ≤
        (D / Real.log 2 + 1 / (-Real.log α) + 3) * Real.log S := by
  let a := TerminalDepth.binaryExponent D S
  let T := 2 ^ a
  have hT : 0 < T := by dsimp [T]; positivity
  have hM : 0 < M := by omega
  have hbase : ∀ u : ℕ, u ≤ U → u ≤ T →
      ∃ l : List ℕ, TerminalDescent.UnitList ((u : ℚ) / M) l ∧ l.length ≤ a + 1 := by
    intro u hu huT
    have hpow : u < 2 ^ (a + 1) := by
      have : 0 < 2 ^ a := by positivity
      dsimp [T] at huT
      rw [pow_succ]
      omega
    obtain ⟨l, hl2, hlen, hsum⟩ := binary_unit_fraction_list u M a (hu.trans_lt hUM) hpow hdiv
    exact ⟨l, ⟨fun n hn => by have := hl2 n hn; omega, hsum⟩, hlen⟩
  have hstep' : ∀ u : ℕ, u ≤ U → T < u →
      ∃ d z h : ℕ, 0 < d ∧ 0 < z ∧ h ≤ U ∧ (h : ℝ) ≤ (u : ℝ) ^ α ∧
      (u : ℚ) / M = (1 : ℚ) / d + ((h : ℚ) / M) / z := by
    intro u hu huT
    have hSu : S ^ D < (u : ℝ) := by
      have hb := TerminalDepth.rpow_le_binary (D := D) (by linarith : 0 < S)
      have hTuR : (T : ℝ) < u := by exact_mod_cast huT
      have hb' : S ^ D ≤ (T : ℝ) := by
        simpa only [T, a, Nat.cast_pow, Nat.cast_ofNat] using hb
      exact hb'.trans_lt hTuR
    obtain ⟨t, z, h, ht, hz, htM, hsmall, heq⟩ := hstep u hu hSu
    have hupos : 1 ≤ u := by omega
    have hhu : h ≤ u := by
      have hpow : (u : ℝ) ^ α ≤ u := by
        simpa using Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast hupos : (1 : ℝ) ≤ u) hα1.le
      exact_mod_cast hsmall.trans hpow
    have hhU := hhu.trans hu
    refine ⟨(M / t) * z, z, h,
      Nat.mul_pos (Nat.div_pos (Nat.le_of_dvd hM htM) ht) hz, hz, hhU, hsmall, ?_⟩
    have hid := residue_step_identity M 1 u t z h hM (by omega) ht hz htM (by simpa using heq)
    simpa only [mul_one, Nat.cast_mul, Nat.cast_one, one_mul, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc] using hid
  intro u hu
  have hlogT : 1 ≤ Real.log (T : ℝ) := by
    simpa only [T, Nat.cast_pow, Nat.cast_ofNat] using TerminalDepth.binary_log_lower hD hlogS
  have hpotential : α ^ TerminalDepth.depth α S * Real.log (u : ℝ) ≤ Real.log (T : ℝ) :=
    (TerminalDepth.potential_bound hα hα1 hS u
      ((by exact_mod_cast hu : (u : ℝ) ≤ U).trans hU)).trans hlogT
  obtain ⟨l, hl, hlen⟩ := TerminalDescent.short_unit_list_of_descent
    M T U (a + 1) hT α hα.le hbase hstep' (TerminalDepth.depth α S) u hu hpotential
  refine ⟨l, ?_, hl.2, ?_⟩
  · intro n hn
    have hn0 := hl.1 n hn
    by_contra hn2
    have hn1 : n = 1 := by omega
    subst n
    have hle : (1 : ℚ) ≤ (l.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum := by
      apply List.single_le_sum
      · intro x hx
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
        positivity
      · exact List.mem_map.2 ⟨1, hn, by norm_num⟩
    rw [hl.2] at hle
    have hlt : (u : ℚ) / M < 1 := by
      apply (div_lt_one (by exact_mod_cast hM : (0 : ℚ) < M)).2
      exact_mod_cast hu.trans_lt hUM
    linarith
  · have hlenR : (l.length : ℝ) ≤ ((a + 1 + TerminalDepth.depth α S : ℕ) : ℝ) := by
      exact_mod_cast hlen
    exact hlenR.trans (TerminalDepth.terminal_length_budget hD hα hα1 hlogS)

end Problem337.TerminalAssembly

end

end OAI
