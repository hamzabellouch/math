import OAI.InformationTheory.QuantumCircuit.Localization
import OAI.InformationTheory.QuantumCircuit.Physical
import OAI.InformationTheory.QuantumCircuit.Measurement

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Polynomial Filter Asymptotics

namespace QAC

lemma eventually_exp_neg_power_lt {s ε : ℝ} (hs : 0<s) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, Real.exp (-(N:ℝ)^s)<ε := by
  filter_upwards [eventually_power_le hs (-Real.log ε+1)] with N hN
  rw [Real.rpow_zero,mul_one] at hN
  rw [← Real.exp_log hε]
  exact Real.exp_lt_exp.mpr (by linarith only [hN])

lemma polynomial_qubit_threshold {n N : ℕ} {c t : ℝ} (hn : 1≤n)
    (ht : 0≤t) (hct : c*t≤1) (hN : (N:ℝ)≤(n:ℝ)^c) : (N:ℝ)^t≤(n:ℝ) := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  calc
    (N:ℝ)^t ≤ ((n:ℝ)^c)^t := Real.rpow_le_rpow (Nat.cast_nonneg N) hN ht
    _ = (n:ℝ)^(c*t) := (Real.rpow_mul (Nat.cast_nonneg n) c t).symm
    _ ≤ (n:ℝ)^1 := Real.rpow_le_rpow_of_exponent_le hn1 hct
    _ = (n:ℝ) := Real.rpow_one _

lemma hadamard_high_entry_bound {n N : ℕ} (hnN : n≤N) (W : Operator N)
    (out : Fin N) (x : Word n) {r : ℝ} (hr : r≤(n:ℝ)) :
    ‖(localMatrix (inputHadamard n N)*(star W*(outputZeroCount out).zero*W)*
      localMatrix (inputHadamard n N))
      (flipWord (inputSet n N) (inputWord x)) (inputWord x)‖ ≤
    ‖(computationalCount (inputWord x)).high r*(localMatrix (inputHadamard n N)*star W)*
      (outputZeroCount out).zero*star (localMatrix (inputHadamard n N)*star W)*
      (computationalCount (inputWord x)).zero‖ := by
  have hcard : r≤((inputSet n N).card:ℝ) := by simpa only [inputSet_card hnN] using hr
  have hh := high_entry_bound
    (localMatrix (inputHadamard n N)*(star W*(outputZeroCount out).zero*W)*
      localMatrix (inputHadamard n N)) (inputWord x) (inputSet n N) hcard
  simpa only [star_mul,star_star,inputHadamard_star,mul_assoc] using hh

/-- The measured-output parity lower bound, allowing arbitrary final garbage and
all polynomially many initially zero ancillas. No cleanliness assumption is used. -/
theorem parity_lower_bound : ParityStatement := by
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
  obtain ⟨N₀,hN₀⟩ := localization d s t hs.le hst
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

end QAC

end

end OAI
