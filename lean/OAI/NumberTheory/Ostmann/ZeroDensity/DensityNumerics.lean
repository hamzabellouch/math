import OAI.NumberTheory.Ostmann.ZeroDensity.DensityNumericsScales

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.ZeroDensity

theorem exists_density_numerical_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q H : ℕ) (σ : ℝ),
      1 ≤ Q → 1 ≤ H → 0 ≤ σ → σ ≤ 1 →
      4*(detectorBlockCount (detectorLength Q H (Q^2*H)) : ℝ) *
        ∑ j ∈ Finset.range (detectorBlockCount (detectorLength Q H (Q^2*H))),
          (((2^j*(Q^2*H) : ℕ) : ℝ)+(Q : ℝ)^2*H) * (1+Real.log Q) *
            (1+Real.log (2*(2^j*(Q^2*H) : ℕ) : ℝ))^7 *
              (2^j*(Q^2*H) : ℕ) * ((2^j*(Q^2*H) : ℕ) : ℝ)^(-2*σ) ≤
        C*((Q^2*H : ℕ):ℝ)^(10*(1-σ))*(1+Real.log (Q*H : ℕ))^10 := by
  let D : ℝ := 265/Real.log 2+1
  have hD : 0 < D := by
    have : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
    dsimp [D]
    positivity
  refine ⟨8*512^2*2048^7*D^2,by positivity,?_⟩
  intro Q H σ hQ hH hσ hσ1
  let J := detectorBlockCount (detectorLength Q H (Q^2*H))
  let B : ℝ := (Q^2*H : ℕ)
  let L : ℝ := 1+Real.log (Q*H : ℕ)
  let U : ℕ → ℝ := fun j => (2^j*(Q^2*H) : ℕ)
  have hnat := density_nat_scales hQ hH
  have hlogs := density_log_scales hQ hH
  have hB : 1 ≤ B := by dsimp [B]; exact_mod_cast hnat.1
  have hU (j : ℕ) (hj : j ∈ Finset.range J) : B ≤ U j ∧ U j ≤ 512*B^5 := by
    have hh := hnat.2.2.2 j (Finset.mem_range.mp hj)
    constructor
    · dsimp [B,U]; exact_mod_cast hh.1
    · dsimp [B,U]; exact_mod_cast hh.2
  have hb := density_sum_bound U hB hlogs.1 hD.le (density_block_count_bound hQ hH)
    hlogs.2.1 hlogs.2.2.1 hσ hσ1 hU
    (fun j hj => (hlogs.2.2.2.2 (U j) (hU j hj).1 (hU j hj).2).1)
    (fun j hj => (hlogs.2.2.2.2 (U j) (hU j hj).1 (hU j hj).2).2)
  simpa only [U,B,L,J,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hb

end Ostmann.ZeroDensity

end

end OAI
