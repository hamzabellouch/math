import OAI.InformationTheory.QuantumCircuit.Main

namespace OAI

/-! Measured-output parity bounds deduced from operator-norm localization. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Polynomial Filter Asymptotics

namespace QAC

theorem parity_lower_bound_of_localization (hlocal : LocalizationStatement) :
    ParityStatement := by
  intro d c ε hc hε _
  have hcpos : 0<c := lt_of_lt_of_le zero_lt_one hc
  let t : ℝ := 1/(2*c)
  let s : ℝ := t/2
  have ht : 0<t := by dsimp [t]; positivity
  have hs : 0<s := by dsimp [s]; positivity
  have hst : s<t := by dsimp [s]; linarith only [ht]
  have hct : c*t≤1 := by
    have hceq : c*t=1/2 := by dsimp [t]; field_simp
    rw [hceq]
    norm_num
  obtain ⟨N₀,hN₀⟩ := hlocal d s t hs.le hst
  obtain ⟨N₁,hN₁⟩ := Filter.eventually_atTop.mp (eventually_exp_neg_power_lt hs hε)
  refine ⟨max 1 (max N₀ N₁),?_⟩
  intro n hn N hnN hsize layers hdepth out hsuccess
  have hn1 : 1≤n := (le_max_left 1 (max N₀ N₁)).trans hn
  have hn0 : 0<n := lt_of_lt_of_le Nat.zero_lt_one hn1
  have hNN₀ : N₀≤N := (le_trans (le_max_left N₀ N₁) (le_max_right 1 (max N₀ N₁))).trans (hn.trans hnN)
  have hNN₁ : N₁≤N := (le_trans (le_max_right N₀ N₁) (le_max_right 1 (max N₀ N₁))).trans (hn.trans hnN)
  let W := physicalCircuitMatrix layers
  let H := localMatrix (inputHadamard n N)
  have hW : IsCircuit d W := (physicalCircuit_isCircuit layers).mono hdepth
  have hU : IsCircuit d (H*star W) := hW.star_mem.local_mul (inputHadamard n N)
  have hthreshold : (N:ℝ)^t≤(n:ℝ) := polynomial_qubit_threshold hn1 ht.le hct hsize
  have hentry (x : Word n) :
      ‖(H*(star W*(outputZeroCount out).zero*W)*H)
        (flipWord (inputSet n N) (inputWord x)) (inputWord x)‖ ≤ Real.exp (-(N:ℝ)^s) := by
    exact (hadamard_high_entry_bound hnN W out x hthreshold).trans
      (hN₀ N hNN₀ (H*star W) hU (computationalCount (inputWord x)) (outputZeroCount out))
  have hadv := parity_advantage_from_entries hn0 hnN W hW.mem_unitary out hsuccess hentry
  exact (not_le_of_gt (hN₁ N hNN₁)) hadv

theorem parity_lower_bound_polynomial_size_of_localization
    (hlocal : LocalizationStatement) (d k C : ℕ)
    (_hd : 0 < d) (_hk : 0 < k) (_hC : 0 < C) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ N : ℕ, n ≤ N → N ≤ C * (n + 1) ^ k →
      ∀ layers : List (PhysicalLayer N), layers.length ≤ d →
        ∀ out : Fin N, ∃ x : Word n,
          successProbability (physicalCircuitMatrix layers) out x < (2 : ℝ) / 3 := by
  classical
  obtain ⟨n₀, h₀⟩ := parity_lower_bound_of_localization hlocal d ((k + 1 : ℕ) : ℝ) (1 / 6)
    (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)) (by norm_num) (by norm_num)
  refine ⟨max n₀ (max 1 (C * 2 ^ k)), ?_⟩
  intro n hn N hnN hN layers hdepth out
  rcases max_le_iff.mp hn with ⟨hn₀, hnrest⟩
  rcases max_le_iff.mp hnrest with ⟨hn1, hCn⟩
  have hpoly : N ≤ n ^ (k + 1) := by
    calc
      N ≤ C * (n + 1) ^ k := hN
      _ ≤ C * (2 * n) ^ k :=
        Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) k)
      _ = (C * 2 ^ k) * n ^ k := by rw [mul_pow, Nat.mul_assoc]
      _ ≤ n * n ^ k := Nat.mul_le_mul_right (n ^ k) hCn
      _ = n ^ (k + 1) := by rw [pow_succ, Nat.mul_comm]
  have hsize : (N : ℝ) ≤ (n : ℝ) ^ ((k + 1 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hpoly
  have hnot := h₀ n hn₀ N hnN hsize layers hdepth out
  push Not at hnot
  norm_num at hnot
  exact hnot

end QAC

end

end OAI
