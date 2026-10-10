import OAI.NumberTheory.Jacobsthal.Estimates.ScalarErrorBudget

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosHyperbolaError

theorem sum_zero_add_nonzero (N : ℕ) [NeZero N] (f : ZMod N → ℂ) :
    (∑ h : ZMod N, f h) = f 0 + ∑ h ∈ nonzeroFrequencies N, f h := by
  have he : nonzeroFrequencies N = (Finset.univ : Finset (ZMod N)).erase 0 := by
    ext h
    simp [nonzeroFrequencies]
  rw [he]
  exact (Finset.add_sum_erase Finset.univ f (Finset.mem_univ 0)).symm

theorem double_sum_decomposition (N : ℕ) [NeZero N] (F : ZMod N → ZMod N → ℂ) :
    (∑ h : ZMod N, ∑ k : ZMod N, F h k) =
      F 0 0 + (∑ h ∈ nonzeroFrequencies N, F h 0) +
        (∑ k ∈ nonzeroFrequencies N, F 0 k) +
        ∑ h ∈ nonzeroFrequencies N, ∑ k ∈ nonzeroFrequencies N, F h k := by
  rw [sum_zero_add_nonzero N (fun h => ∑ k : ZMod N, F h k), sum_zero_add_nonzero N (F 0)]
  simp_rw [sum_zero_add_nonzero N]
  rw [Finset.sum_add_distrib]
  ring

theorem double_remainder_norm_le (N : ℕ) [NeZero N] (F : ZMod N → ZMod N → ℂ) :
    ‖(∑ h : ZMod N, ∑ k : ZMod N, F h k)-F 0 0‖ ≤
      (∑ h ∈ nonzeroFrequencies N, ‖F h 0‖) +
        (∑ k ∈ nonzeroFrequencies N, ‖F 0 k‖) +
        ∑ h ∈ nonzeroFrequencies N, ∑ k ∈ nonzeroFrequencies N, ‖F h k‖ := by
  let X := ∑ h ∈ nonzeroFrequencies N, F h 0
  let Y := ∑ k ∈ nonzeroFrequencies N, F 0 k
  let Z := ∑ h ∈ nonzeroFrequencies N, ∑ k ∈ nonzeroFrequencies N, F h k
  rw [double_sum_decomposition]
  change ‖F 0 0+X+Y+Z-F 0 0‖ ≤ _
  rw [show F 0 0+X+Y+Z-F 0 0 = X+Y+Z by ring]
  have hX : ‖X‖ ≤ ∑ h ∈ nonzeroFrequencies N, ‖F h 0‖ := norm_sum_le _ _
  have hY : ‖Y‖ ≤ ∑ k ∈ nonzeroFrequencies N, ‖F 0 k‖ := norm_sum_le _ _
  have hZ : ‖Z‖ ≤ ∑ h ∈ nonzeroFrequencies N, ∑ k ∈ nonzeroFrequencies N, ‖F h k‖ := by
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun h _ => norm_sum_le _ _))
  calc
    _ ≤ ‖X+Y‖+‖Z‖ := norm_add_le _ _
    _ ≤ ‖X‖+‖Y‖+‖Z‖ := add_le_add (norm_add_le X Y) le_rfl
    _ ≤ _ := add_le_add (add_le_add hX hY) hZ

end ErdosHyperbolaError

end

section

open scoped BigOperators
namespace ErdosHyperbolaError

open ErdosHyperbolaIdentities

noncomputable def spectralTerm (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod (H*T))ˣ) (P Q : ProgressionInterval)
    (h k : ZMod (H*T)) : ℂ :=
  P.weight (H*T) h * Q.weight (H*T) k * restrictedSum (H*T) T (dvd_mul_left T H) a c h k

theorem spectral_remainder_bound (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod (H*T))ˣ) (P Q : ProgressionInterval) :
    ‖(∑ h : ZMod (H*T), ∑ k : ZMod (H*T), spectralTerm H T a c P Q h k)-
      spectralTerm H T a c P Q 0 0‖ ≤
      ‖Q.weight (H*T) 0‖ * completeScale (H*T) * Real.sqrt T * gcdL1Norm (H*T) P +
      ‖P.weight (H*T) 0‖ * completeScale (H*T) * gcdL1Norm (H*T) Q +
      completeScale (H*T) * l1Norm (H*T) P * gcdL1Norm (H*T) Q := by
  have hleft : (∑ h ∈ nonzeroFrequencies (H*T), ‖spectralTerm H T a c P Q h 0‖) ≤
      ‖Q.weight (H*T) 0‖ * completeScale (H*T) * Real.sqrt T * gcdL1Norm (H*T) P := by
    unfold gcdL1Norm
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h _
    rw [spectralTerm, norm_mul, norm_mul]
    calc
      _ ≤ (‖P.weight (H*T) h‖*‖Q.weight (H*T) 0‖) *
          (completeScale (H*T)*Real.sqrt T*Real.sqrt (Nat.gcd h.val (H*T))) :=
        mul_le_mul_of_nonneg_left (restrictedSum_norm_le_first H T a c h 0) (by positivity)
      _ = _ := by ring
  have hright : (∑ k ∈ nonzeroFrequencies (H*T), ‖spectralTerm H T a c P Q 0 k‖) ≤
      ‖P.weight (H*T) 0‖ * completeScale (H*T) * gcdL1Norm (H*T) Q := by
    unfold gcdL1Norm
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    rw [spectralTerm, norm_mul, norm_mul]
    calc
      _ ≤ (‖P.weight (H*T) 0‖*‖Q.weight (H*T) k‖) *
          (completeScale (H*T)*Real.sqrt (Nat.gcd k.val (H*T))) :=
        mul_le_mul_of_nonneg_left (restrictedSum_norm_le_second H T a c 0 k) (by positivity)
      _ = _ := by ring
  have hboth : (∑ h ∈ nonzeroFrequencies (H*T), ∑ k ∈ nonzeroFrequencies (H*T),
      ‖spectralTerm H T a c P Q h k‖) ≤
        completeScale (H*T)*l1Norm (H*T) P*gcdL1Norm (H*T) Q := by
    have hp (h k : ZMod (H*T)) : ‖spectralTerm H T a c P Q h k‖ ≤
        completeScale (H*T)*‖P.weight (H*T) h‖ *
          (‖Q.weight (H*T) k‖*Real.sqrt (Nat.gcd k.val (H*T))) := by
      rw [spectralTerm, norm_mul, norm_mul]
      calc
        _ ≤ (‖P.weight (H*T) h‖*‖Q.weight (H*T) k‖) *
            (completeScale (H*T)*Real.sqrt (Nat.gcd k.val (H*T))) :=
          mul_le_mul_of_nonneg_left (restrictedSum_norm_le_second H T a c h k) (by positivity)
        _ = _ := by ring
    calc
      _ ≤ ∑ h ∈ nonzeroFrequencies (H*T), ∑ k ∈ nonzeroFrequencies (H*T),
          completeScale (H*T)*‖P.weight (H*T) h‖ *
            (‖Q.weight (H*T) k‖*Real.sqrt (Nat.gcd k.val (H*T))) :=
        Finset.sum_le_sum (fun h _ => Finset.sum_le_sum (fun k _ => hp h k))
      _ = _ := by
        unfold l1Norm gcdL1Norm
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
  exact (double_remainder_norm_le (H*T) (spectralTerm H T a c P Q)).trans
    (add_le_add (add_le_add hleft hright) hboth)

end ErdosHyperbolaError

end

section

open scoped BigOperators
namespace ErdosHyperbolaError

open ErdosHyperbolaIdentities

theorem normalized_spectral_error (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod (H*T))ˣ) (P Q : ProgressionInterval)
    (hP : P.left ≤ P.right) (hQ : Q.left ≤ Q.right)
    (hPN : P.step.Coprime (H*T)) (hQN : Q.step.Coprime (H*T)) :
    ‖(∑ h : ZMod (H*T), ∑ k : ZMod (H*T), spectralTerm H T a c P Q h k)-
      spectralTerm H T a c P Q 0 0‖/((H*T : ℕ) : ℝ)^2 ≤
      8*errorBase (H*T) T*(1+intervalLength P/((H*T : ℕ) : ℝ)+intervalLength Q/((H*T : ℕ) : ℝ)) := by
  have hD := completeScale_nonneg (H*T)
  have hs := Real.sqrt_nonneg (T : ℝ)
  have ht : 0 ≤ logFactor (H*T) := le_trans (by norm_num) (logFactor_one_le (H*T))
  have hU := intervalLength_nonneg P hP
  have hV := intervalLength_nonneg Q hQ
  have hA0 := norm_weight_zero_le (H*T) P hP
  have hB0 := norm_weight_zero_le (H*T) Q hQ
  have hA := l1Norm_le_logFactor (H*T) P hPN
  have hAg := gcdL1Norm_le_logFactor (H*T) P hPN
  have hBg := gcdL1Norm_le_logFactor (H*T) Q hQN
  have hAg0 := gcdL1Norm_nonneg (H*T) P
  have hBg0 := gcdL1Norm_nonneg (H*T) Q
  have hApos := l1Norm_nonneg (H*T) P
  have hnum : ‖(∑ h : ZMod (H*T), ∑ k : ZMod (H*T), spectralTerm H T a c P Q h k)-
      spectralTerm H T a c P Q 0 0‖ ≤
      completeScale (H*T)*
        ((2*((H*T : ℕ) : ℝ)*((H*T).divisors.card : ℝ)*logFactor (H*T))*(intervalLength P+1)+
          Real.sqrt T*(2*((H*T : ℕ) : ℝ)*((H*T).divisors.card : ℝ)*logFactor (H*T))*(intervalLength Q+1)+
          (2*((H*T : ℕ) : ℝ)*logFactor (H*T))*
            (2*((H*T : ℕ) : ℝ)*((H*T).divisors.card : ℝ)*logFactor (H*T))) := by
    calc
      _ ≤ _ := spectral_remainder_bound H T a c P Q
      _ ≤ (intervalLength Q+1)*completeScale (H*T)*Real.sqrt T*
          (2*((H*T : ℕ) : ℝ)*((H*T).divisors.card : ℝ)*logFactor (H*T))+
          (intervalLength P+1)*completeScale (H*T)*
            (2*((H*T : ℕ) : ℝ)*((H*T).divisors.card : ℝ)*logFactor (H*T))+
          completeScale (H*T)*(2*((H*T : ℕ) : ℝ)*logFactor (H*T))*
            (2*((H*T : ℕ) : ℝ)*((H*T).divisors.card : ℝ)*logFactor (H*T)) := by
        gcongr
      _ = _ := by ring
  calc
    _ ≤ _ := div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ ≤ _ := axis_quadrant_budget (completeScale (H*T)) ((H*T).divisors.card : ℝ)
      (Real.sqrt T) (logFactor (H*T)) ((H*T : ℕ) : ℝ) (intervalLength P) (intervalLength Q)
      hD (Nat.cast_nonneg _) (sqrt_modulus_one_le T) (logFactor_one_le (H*T))
      (by exact_mod_cast Nat.mul_pos (NeZero.pos H) (NeZero.pos T)) hU hV

end ErdosHyperbolaError

end

end Erdos970

end OAI
