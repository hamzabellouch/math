import OAI.NumberTheory.Jacobsthal.Sieve.ResidueCountDifference

namespace OAI

namespace Erdos970


namespace ErdosModulusRelative
open ErdosInverseHits ErdosInverseCounts NumberTheoryLean

theorem modulus_small_upper (aStar : ℝ) (ha : 0 < aStar) :
    ∃ C w0 : ℝ,0 < C ∧ 2 ≤ w0 ∧ ∀ w : ℝ,w0 ≤ w →
      ∀ (Y d : ℕ) (a : ℕ → ℕ),0 < Y → Squarefree d →
        (∀ p ∈ d.primeFactors,w < (p : ℝ)) →
        aStar ≤ Real.log ((Y : ℝ)/(d : ℝ))/Real.log w →
        (modulusCount Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a d : ℝ) ≤
          C*((Y : ℝ)/(d : ℝ))*SmallSieveFinite.smallEuler ⌊w⌋₊ := by
  obtain ⟨C,hC,w0,hw0,hupper⟩ := SmallSieveUpper.progression_small_upper aStar ha
  refine ⟨C,w0,hC,hw0,?_⟩
  intro w hw Y d a hY hd hlarge hv
  have hw2 : 2 ≤ w := hw0.trans hw
  have hw1 : 1 < w := by linarith
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  have hJ : 0 < (Y : ℝ)/(d : ℝ) := by positivity
  have hJL : w^aStar ≤ (Y : ℝ)/(d : ℝ) := by
    calc
      _ ≤ w^(Real.log ((Y : ℝ)/(d : ℝ))/Real.log w) :=
        Real.rpow_le_rpow_of_exponent_le hw1.le hv
      _ = _ := SmallSieveRelative.rpow_log_ratio w _ hw1 hJ
  have hb := primeHitRepresentative_spec d hd a
  have hN := hitLength_error Y d (primeHitRepresentative d hd a) hd0 hb.1 hb.2.1
  have hh := hupper (hitLength Y d (primeHitRepresentative d hd a)) w ((Y : ℝ)/(d : ℝ))
    (primeHitRepresentative d hd a : ℤ) d a hw hJL hN (large_modulus_coprime_small w d hd hlarge)
  rw [modulus_count_eq_offsets Y _ a d hd,offsets_eq_progression,Int.cast_natCast]
  exact hh

theorem modulus_error_uniform_bound (aStar : ℝ) (ha : 0 < aStar) :
    ∃ B w0 : ℝ,0 < B ∧ 2 ≤ w0 ∧ ∀ w : ℝ,w0 ≤ w →
      ∀ (Y d : ℕ) (a : ℕ → ℕ),0 < Y → Squarefree d →
        (∀ p ∈ d.primeFactors,w < (p : ℝ)) →
        aStar ≤ Real.log ((Y : ℝ)/(d : ℝ))/Real.log w →
        |(modulusCount Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a d : ℝ)/
          (((Y : ℝ)/(d : ℝ))*SmallSieveFinite.smallEuler ⌊w⌋₊)-1| ≤ B := by
  obtain ⟨C,w0,hC,hw0,hupper⟩ := modulus_small_upper aStar ha
  refine ⟨C+1,w0,by linarith,hw0,?_⟩
  intro w hw Y d a hY hd hlarge hv
  have hw2 : 2 ≤ w := hw0.trans hw
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  have hJ : 0 < (Y : ℝ)/(d : ℝ) := by positivity
  have hV : 0 < SmallSieveFinite.smallEuler ⌊w⌋₊ :=
    (inv_pos.mpr (show 0 < w by linarith)).trans_le (SmallSieveFinite.smallEuler_floor_ge_inv w hw2)
  have hDen : 0 < ((Y : ℝ)/(d : ℝ))*SmallSieveFinite.smallEuler ⌊w⌋₊ := mul_pos hJ hV
  have hu := (div_le_iff₀ hDen).mpr (by
    simpa only [mul_assoc] using hupper w hw Y d a hY hd hlarge hv)
  have hnon : 0 ≤ (modulusCount Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a d : ℝ) := by
    exact_mod_cast modulusCount_nonneg Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a d
  have hn := div_nonneg hnon hDen.le
  rw [abs_le]
  constructor <;> linarith

theorem modulus_error_envelope (aStar : ℝ) (ha : 0 < aStar) :
    ∃ C w0 : ℝ,0 < C ∧ 1 < w0 ∧ ∀ w : ℝ,w0 ≤ w →
      ∀ (Y d : ℕ) (a : ℕ → ℕ),0 < Y → 0 < d → Squarefree d →
        (∀ p ∈ d.primeFactors,w < (p : ℝ)) →
        aStar ≤ Real.log ((Y : ℝ)/(d : ℝ))/Real.log w →
        |(modulusCount Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a d : ℝ)/
          (((Y : ℝ)/(d : ℝ))*SmallSieveFinite.smallEuler ⌊w⌋₊)-1| ≤
            C*Real.exp (-(Real.log ((Y : ℝ)/(d : ℝ))/Real.log w)/192) := by
  obtain ⟨B,w0,hB,hw0,hbound⟩ := modulus_error_uniform_bound aStar ha
  let C := max 3 (B*Real.exp ((960048 : ℝ)/192))
  have hC3 : 3 ≤ C := le_max_left _ _
  have hCB : B*Real.exp ((960048 : ℝ)/192) ≤ C := le_max_right _ _
  refine ⟨C,w0,by linarith,by linarith,?_⟩
  intro w hw Y d a hY _hdpos hd hlarge hv
  let v := Real.log ((Y : ℝ)/(d : ℝ))/Real.log w
  by_cases hbig : 960048 ≤ v
  · exact (modulus_small_relative w Y d a (hw0.trans hw) hY hd hlarge hbig).trans
      (mul_le_mul_of_nonneg_right hC3 (Real.exp_pos (-v/192)).le)
  · have hvmax : v ≤ 960048 := le_of_lt (lt_of_not_ge hbig)
    have he : 1 ≤ Real.exp ((960048 : ℝ)/192)*Real.exp (-v/192) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by linarith)
    have hBC : B ≤ C*Real.exp (-v/192) := by
      calc
        _ = B*1 := by ring
        _ ≤ B*(Real.exp ((960048 : ℝ)/192)*Real.exp (-v/192)) :=
          mul_le_mul_of_nonneg_left he hB.le
        _ = (B*Real.exp ((960048 : ℝ)/192))*Real.exp (-v/192) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hCB (Real.exp_pos _).le
    exact (hbound w hw Y d a hY hd hlarge hv).trans hBC

end ErdosModulusRelative


end Erdos970

end OAI
