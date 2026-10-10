import OAI.NumberTheory.JointDickman.Arithmetic.PrimePairSieveScale

namespace OAI

/-! # Uniform upper bound for pairs of primes at a prescribed difference -/
namespace JointDickman
open Filter Finset
open scoped Topology

/-- The upper-sieve bound is uniform in the positive difference, including
all prime divisors of that difference through the exact totient factor. -/
theorem primePair_count_log_bound : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ Q : ℕ in atTop, ∀ h : ℕ, 0 < h →
      (primePairCount Q h:ℝ) ≤ C*((h:ℝ)/h.totient)*(Q:ℝ)/(Real.log Q)^2 := by
  obtain ⟨C,hC,hbound⟩ := primePair_count_sieve_log_bound
  refine ⟨128*C+1,by positivity,?_⟩
  have hscale := tendsto_natCast_atTop_atTop.eventually primePair_sieve_scale
  filter_upwards [hscale,eventually_ge_atTop 2] with Q hscale hQ
  intro h hh
  obtain ⟨Z,hZ,hlogZ,herr⟩ := hscale
  have hQR : (2:ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0:ℝ) < Q := by linarith
  have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
  have hlogZ0 : 0 < Real.log Z := Real.log_pos (by exact_mod_cast (show 1 < Z by omega))
  have hφ : (0:ℝ) < h.totient := by exact_mod_cast (Nat.totient_pos.mpr hh)
  have hw : 1 ≤ (h:ℝ)/h.totient := (one_le_div hφ).mpr (by exact_mod_cast Nat.totient_le h)
  have hrecip : 1/(Real.log Z)^2 ≤ 64/(Real.log Q)^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hlogZ0) (sq_pos_of_pos hlogQ)).mpr
    nlinarith
  have hmain : C*(Q+1:ℝ)*((h:ℝ)/h.totient)/(Real.log Z)^2 ≤
      128*C*((h:ℝ)/h.totient)*(Q:ℝ)/(Real.log Q)^2 := by
    calc
      _ = C*(Q+1:ℝ)*((h:ℝ)/h.totient)*(1/(Real.log Z)^2) := by ring
      _ ≤ C*(2*(Q:ℝ))*((h:ℝ)/h.totient)*(64/(Real.log Q)^2) := by
        gcongr
        linarith
      _ = _ := by ring
  have herr' : 2*(Z+1:ℝ)*(Z:ℝ)^2+(Z+1:ℝ) ≤
      ((h:ℝ)/h.totient)*(Q:ℝ)/(Real.log Q)^2 := by
    exact herr.trans (by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      nlinarith)
  have hb := hbound Q Z h hZ hh
  calc
    _ ≤ C*(Q+1:ℝ)*((h:ℝ)/h.totient)/(Real.log Z)^2 +
        (2*(Z+1:ℝ)*(Z:ℝ)^2+(Z+1:ℝ)) := by linarith
    _ ≤ 128*C*((h:ℝ)/h.totient)*(Q:ℝ)/(Real.log Q)^2 +
        ((h:ℝ)/h.totient)*(Q:ℝ)/(Real.log Q)^2 := add_le_add hmain herr'
    _ = _ := by ring

end JointDickman

end OAI
