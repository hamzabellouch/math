import OAI.NumberTheory.Jacobsthal.Estimates.HypotheticalIndividualUpper
import OAI.NumberTheory.Jacobsthal.Primes.ReferenceSourcePrimeSets

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseEuler
open NumberTheoryLean ErdosPrimeInputs.MertensStrong

theorem cutoffPrimes_eq_filtered_Ioc (z : ℕ) :
    LargePrimeDeletion.cutoffPrimes z = (Finset.Ioc 0 z).filter Nat.Prime := by
  ext p
  rw [LargePrimeDeletion.mem_cutoffPrimes]
  simp only [Finset.mem_filter,Finset.mem_Ioc]
  exact ⟨fun h => ⟨⟨h.1.pos,h.2⟩,h.1⟩,fun h => ⟨h.2,h.1.2⟩⟩

theorem smallEuler_eq_primeProduct (w : ℝ) :
    SmallSieveFinite.smallEuler ⌊w⌋₊ = primeProduct w := by
  unfold SmallSieveFinite.smallEuler primeProduct
  rw [cutoffPrimes_eq_filtered_Ioc]
  simp only [one_div]

open _root_.Filter
open scoped Topology

theorem smallEuler_log_bounds : ∀ᶠ w : ℝ in atTop,
    2 ≤ w ∧ 0 < SmallSieveFinite.smallEuler ⌊w⌋₊ ∧
      Real.exp (-Real.eulerMascheroniConstant)/(2*Real.log w) ≤ SmallSieveFinite.smallEuler ⌊w⌋₊ ∧
      (SmallSieveFinite.smallEuler ⌊w⌋₊)⁻¹ ≤ 2*Real.exp Real.eulerMascheroniConstant*Real.log w := by
  have hnorm := (tendsto_order.mp ReferenceMertens.normalization_tendsto_one).2 2 (by norm_num)
  filter_upwards [hnorm,eventually_ge_atTop (2 : ℝ)] with w hn hw
  have hw0 : 0 < w := by linarith
  have hL : 0 < Real.log w := Real.log_pos (by linarith)
  have hV : 0 < SmallSieveFinite.smallEuler ⌊w⌋₊ :=
    (inv_pos.mpr hw0).trans_le (SmallSieveFinite.smallEuler_floor_ge_inv w hw)
  have hn' : Real.exp (-Real.eulerMascheroniConstant)/
      (Real.log w*SmallSieveFinite.smallEuler ⌊w⌋₊) ≤ 2 := by
    simpa only [ReferenceMertens.normalization,← smallEuler_eq_primeProduct] using hn.le
  have hprod := (div_le_iff₀ (mul_pos hL hV)).mp hn'
  have hlo : Real.exp (-Real.eulerMascheroniConstant)/(2*Real.log w) ≤ SmallSieveFinite.smallEuler ⌊w⌋₊ := by
    apply (div_le_iff₀ (by positivity : 0 < 2*Real.log w)).mpr
    nlinarith
  have hlowpos : 0 < Real.exp (-Real.eulerMascheroniConstant)/(2*Real.log w) := by positivity
  have hi := (inv_le_inv₀ hV hlowpos).mpr hlo
  refine ⟨hw,hV,hlo,?_⟩
  calc
    _ ≤ (Real.exp (-Real.eulerMascheroniConstant)/(2*Real.log w))⁻¹ := hi
    _ = 2*Real.exp Real.eulerMascheroniConstant*Real.log w := by
      rw [inv_div,Real.exp_neg,div_inv_eq_mul]
      ring

end ErdosInverseEuler

end

section

namespace ErdosStoppedArithmetic
open NumberTheoryLean ErdosInverseCounts ErdosInverseEuler
  ErdosPrimeInputs.MertensStrong ReferenceProductsBasics
attribute [local instance] Classical.propDecidable

theorem smallEuler_nat_primeProduct (P : ℕ) :
    SmallSieveFinite.smallEuler P=primeProduct (P : ℝ) := by
  simpa only [Nat.floor_natCast] using smallEuler_eq_primeProduct (P : ℝ)

theorem smallEuler_prime_step (P : ℕ) (hP : P.Prime) :
    SmallSieveFinite.smallEuler P=(1-(P : ℝ)⁻¹)*SmallSieveFinite.smallEuler (P-1) := by
  have hset : LargePrimeDeletion.cutoffPrimes P = insert P (LargePrimeDeletion.cutoffPrimes (P-1)) := by
    ext p
    simp only [LargePrimeDeletion.mem_cutoffPrimes,Finset.mem_insert]
    constructor
    · rintro ⟨hp,hpP⟩
      by_cases he : p=P
      · exact Or.inl he
      · exact Or.inr ⟨hp,by omega⟩
    · rintro (rfl | ⟨hp,hpP⟩)
      · exact ⟨hP,le_rfl⟩
      · exact ⟨hp,by omega⟩
  have hnot : P ∉ LargePrimeDeletion.cutoffPrimes (P-1) := by
    rw [LargePrimeDeletion.mem_cutoffPrimes]
    have hp := hP.pos
    omega
  unfold SmallSieveFinite.smallEuler
  rw [hset,Finset.prod_insert hnot]

theorem smallEuler_strict_le_two_closed (P : ℕ) (hP : P.Prime) :
    SmallSieveFinite.smallEuler (P-1) ≤ 2*primeProduct (P : ℝ) := by
  have hV : 0 ≤ SmallSieveFinite.smallEuler (P-1) := by
    rw [smallEuler_nat_primeProduct]
    exact (actual_primeProduct_pos _).le
  have hp : (0 : ℝ) < P := by exact_mod_cast hP.pos
  have h2 : (2 : ℝ) ≤ P := by exact_mod_cast hP.two_le
  have hinv : (P : ℝ)⁻¹ ≤ 1/2 := by rw [← one_div];exact (div_le_iff₀ hp).mpr (by linarith)
  have hfactor := mul_le_mul_of_nonneg_right (show (1/2 : ℝ) ≤ 1-(P : ℝ)⁻¹ by linarith) hV
  rw [← smallEuler_nat_primeProduct P,smallEuler_prime_step P hP]
  nlinarith

theorem original_individual_upper_closed :
    ∃ C : ℝ,0 < C ∧ ∃ P0 : ℕ,2 ≤ P0 ∧ ∀ P : ℕ,P.Prime → P0 ≤ P →
      ∀ (Y d : ℕ) (a : ℕ → ℕ),0 < Y → Squarefree d →
        (∀ t ∈ d.primeFactors,P ≤ t) → (P : ℝ)^2 ≤ (Y : ℝ)/(d : ℝ) →
        (modulusCount Y (LargePrimeDeletion.cutoffPrimes (P-1)) a d : ℝ) ≤
          C*((Y : ℝ)/(d : ℝ))*primeProduct (P : ℝ) := by
  obtain ⟨C,hC,P0,hP0,hUpper⟩ := original_individual_upper
  refine ⟨2*C,by positivity,P0,hP0,?_⟩
  intro P hPrime hP Y d a hY hd hlarge hJ
  have hU := hUpper P hP Y d a hY hd hlarge hJ
  have hE := smallEuler_strict_le_two_closed P hPrime
  have hm := mul_le_mul_of_nonneg_left hE
    (show 0 ≤ C*((Y : ℝ)/(d : ℝ)) by positivity)
  calc
    _ ≤ C*((Y : ℝ)/(d : ℝ))*SmallSieveFinite.smallEuler (P-1) := hU
    _ ≤ C*((Y : ℝ)/(d : ℝ))*(2*primeProduct (P : ℝ)) := hm
    _ = _ := by ring

end ErdosStoppedArithmetic

end

end Erdos970

end OAI
