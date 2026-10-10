import OAI.NumberTheory.JointDickman.Arithmetic.DyadicPrimePartition
import OAI.NumberTheory.JointDickman.Counting.UniformHyperbolaBlock

namespace OAI

/-! # Rational cancellation after removing both small bilinear variables -/
namespace JointDickman
open Finset

noncomputable def truncatedPrimeHyperbola (b c : ℕ → ℂ) (N Z : ℕ) (θ : ℝ) : ℂ :=
  ∑ p ∈ (Nat.primesLE (N/Z)).filter (fun p => Z < p),
    ∑ m ∈ Ioc Z (N/p), b p*c m*additivePhase (θ*p*m)

theorem truncated_prime_hyperbola_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (b c : ℕ → ℂ) (N Z H q a : ℕ),
    0 < N → 0 < Z → 0 < H → 0 < q → a.Coprime q →
    (∀ p, p.Prime → ‖b p‖ ≤ Real.log p) → (∀ m, ‖c m‖ ≤ 1) →
    ‖truncatedPrimeHyperbola b c N Z ((a:ℝ)/q)‖ ≤
      (1+Real.log N/Real.log 2)*(N:ℝ)*
        (Real.log 4*(2/(H:ℝ)+2/(Z:ℝ)) + H*Real.sqrt
          (C*rationalHyperbolaBudget N Z (Real.log (2*(N:ℝ))) q)) := by
  classical
  obtain ⟨C,hC,hblock⟩ := uniform_prime_hyperbola_block_bound
  refine ⟨C,hC,?_⟩
  intro b c N Z H q a hN hZ hH hq ha hb hc
  let P := (Nat.primesLE (N/Z)).filter (fun p => Z < p)
  let J := Nat.log 2 N+1
  let T := (N:ℝ)*(Real.log 4*(2/(H:ℝ)+2/(Z:ℝ)) + H*Real.sqrt
    (C*rationalHyperbolaBudget N Z (Real.log (2*(N:ℝ))) q))
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hZR : (0:ℝ) < Z := by exact_mod_cast hZ
  have hL : 0 ≤ Real.log (2*(N:ℝ)) := Real.log_nonneg (by
    have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
    linarith)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hcover (p : ℕ) (hp : p ∈ P) : Z < p ∧ p ≤ 2^J*Z := by
    obtain ⟨hp0,hpZ⟩ := mem_filter.mp hp
    refine ⟨hpZ,?_⟩
    exact (Nat.mem_primesLE.mp hp0).1.trans
      ((Nat.div_le_self N Z).trans (dyadic_cover_integer N Z hZ))
  have he := sum_dyadic_blocks P
    (fun p => ∑ m ∈ Ioc Z (N/p), b p*c m*additivePhase ((a:ℝ)/q*p*m)) Z J hcover
  unfold truncatedPrimeHyperbola
  change ‖∑ p ∈ P, _‖ ≤ _
  rw [he]
  have hsum : ‖∑ j ∈ range J, ∑ p ∈ P.filter
      (fun p => 2^j*Z < p ∧ p ≤ 2^(j+1)*Z),
      ∑ m ∈ Ioc Z (N/p), b p*c m*additivePhase ((a:ℝ)/q*p*m)‖ ≤ (J:ℝ)*T := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j ∈ range J, T := by
        apply sum_le_sum
        intro j hj
        let W := 2^j*Z
        let S := P.filter (fun p => W < p ∧ p ≤ 2*W)
        have heS : P.filter (fun p => 2^j*Z < p ∧ p ≤ 2^(j+1)*Z) = S := by
          dsimp [S,W]
          congr 2
          funext p
          rw [pow_succ]
          ring_nf
        rw [heS]
        by_cases hS : S=∅
        · simpa [hS] using hT
        obtain ⟨p,hp⟩ := nonempty_iff_ne_empty.mpr hS
        obtain ⟨hpP,hpW,hpQ⟩ := mem_filter.mp hp
        obtain ⟨hpPrime,hpZ⟩ := mem_filter.mp hpP
        have hpNZ := (Nat.mem_primesLE.mp hpPrime).1
        have hW0 : 0 < W := Nat.mul_pos (pow_pos (by norm_num) j) hZ
        have hZW : Z ≤ W := by
          dsimp [W]
          exact Nat.le_mul_of_pos_left Z (pow_pos (by norm_num) j)
        have hWN : W ≤ N := hpW.le.trans (hpNZ.trans (Nat.div_le_self N Z))
        have hQU : ((2*W:ℕ):ℝ)*((N/W:ℕ):ℝ) ≤ 2*(N:ℝ) := by
          have hh : (2*W)*(N/W) ≤ 2*N := by
            simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 (Nat.mul_div_le N W)
          exact_mod_cast hh
        have hU : ((N/W:ℕ):ℝ) ≤ (N:ℝ)/Z := by
          exact (nat_div_cast_le N W hW0).trans
            (div_le_div_of_nonneg_left hNR.le hZR (by exact_mod_cast hZW))
        have hQZ : ((2*W:ℕ):ℝ) ≤ 2*(N:ℝ)/Z := by
          have hwN : (W:ℝ) ≤ ((N/Z:ℕ):ℝ) := by exact_mod_cast hpW.le.trans hpNZ
          have hw := hwN.trans (nat_div_cast_le N Z hZ)
          push_cast
          calc
            2*(W:ℝ) ≤ 2*((N:ℝ)/Z) := mul_le_mul_of_nonneg_left hw (by norm_num)
            _ = _ := by ring
        have hlog : Real.log ((2*W:ℕ):ℝ) ≤ Real.log (2*(N:ℝ)) := by
          apply Real.log_le_log (by positivity)
          exact_mod_cast Nat.mul_le_mul_left 2 hWN
        have hPS (r : ℕ) (hr : r ∈ S) : r.Prime ∧ r ≤ 2*W := by
          obtain ⟨hrP,hrW,hrQ⟩ := mem_filter.mp hr
          exact ⟨(Nat.mem_primesLE.mp (mem_filter.mp hrP).1).2,hrQ⟩
        have hM (r : ℕ) (hr : r ∈ S) : Z ≤ N/r ∧ N/r ≤ N/W := by
          obtain ⟨hrP,hrW,hrQ⟩ := mem_filter.mp hr
          have hrPrime := (Nat.mem_primesLE.mp (mem_filter.mp hrP).1).2
          have hrNZ := (Nat.mem_primesLE.mp (mem_filter.mp hrP).1).1
          constructor
          · apply (Nat.le_div_iff_mul_le hrPrime.pos).mpr
            have hh := (Nat.le_div_iff_mul_le hZ).mp hrNZ
            simpa [mul_comm] using hh
          · apply (Nat.le_div_iff_mul_le hW0).mpr
            exact (Nat.mul_le_mul_left (N/r) hrW.le).trans (Nat.div_mul_le_self N r)
        exact hblock S (fun p => N/p) b c Z (N/W) H (2*W) q a
          N Z (Real.log (2*(N:ℝ))) hH (by omega) hq ha hNR hZR hL hlog hQU hU hQZ
          hPS hM (fun p hp => hb p (hPS p hp).1) hc
      _ = _ := by simp
  apply hsum.trans
  have hj := mul_le_mul_of_nonneg_right (dyadic_block_count_le N) hT
  convert hj using 1
  dsimp [J,T]
  ring

end JointDickman

end OAI
