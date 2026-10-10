import Mathlib.NumberTheory.Harmonic.Bounds
import OAI.NumberTheory.Jacobsthal.Sieve.SourcePairSieve

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceLargeCount
open NumberTheoryLean ErdosHyperbolaError
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem real_level_card_bound (P : Finset ℕ) (v s : ℝ) (hD : 1 ≤ v^s) :
    ((RealFundamentalSieve.levelDivisors P v s).card : ℝ) ≤ 2*(v^s) := by
  have hsub : RealFundamentalSieve.levelDivisors P v s ⊆ Finset.range (⌊v^s⌋₊+1) := by
    intro d hd
    have hb := (Finset.mem_filter.mp hd).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_floor_iff (by linarith)).mpr hb))
  have hc : ((RealFundamentalSieve.levelDivisors P v s).card : ℝ) ≤ ((⌊v^s⌋₊+1 : ℕ) : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range _)
  have hf := Nat.floor_le (show 0 ≤ v^s by linarith)
  push_cast at hc
  linarith

theorem real_level_reciprocal_bound (P : Finset ℕ) (v s : ℝ) (hD : 1 ≤ v^s) :
    (∑ d ∈ RealFundamentalSieve.levelDivisors P v s,1/(d : ℝ)) ≤ 1+Real.log (v^s) := by
  have hsub : RealFundamentalSieve.levelDivisors P v s ⊆ Finset.Icc 1 ⌊v^s⌋₊ := by
    intro d hd
    obtain ⟨hddiv,hdlev⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hddiv,(Nat.le_floor_iff (by linarith)).mpr hdlev⟩
  have hh := harmonic_floor_le_one_add_log (v^s) hD
  have hh' : (∑ d ∈ Finset.Icc 1 ⌊v^s⌋₊,1/(d : ℝ)) ≤ 1+Real.log (v^s) := by
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div] using hh
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans hh'

theorem hyperbolaEnvelope_nonneg (H T0 : ℕ) : 0 ≤ hyperbolaEnvelope H T0 := by
  have hC := completionConstant_pos.le
  dsimp [hyperbolaEnvelope]
  positivity

theorem hyperbola_level_sum_bound (H T0 : ℕ) (P : Finset ℕ) (v s U V : ℝ)
    (hD : 1 ≤ v^s) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    (∑ d ∈ RealFundamentalSieve.levelDivisors P v s,
      hyperbolaEnvelope H T0*(1+U/((d : ℝ)*((H*T0 : ℕ) : ℝ))+V/((H*T0 : ℕ) : ℝ))) ≤
        hyperbolaEnvelope H T0*(2*(v^s)*(1+V/((H*T0 : ℕ) : ℝ))+
          (U/((H*T0 : ℕ) : ℝ))*(1+Real.log (v^s))) := by
  let F := RealFundamentalSieve.levelDivisors P v s
  let N : ℝ := (H*T0 : ℕ)
  have he (d : ℕ) : 1+U/((d : ℝ)*N)+V/N = (1+V/N)+(U/N)*(1/(d : ℝ)) := by ring
  have hsum : (∑ d ∈ F,hyperbolaEnvelope H T0*(1+U/((d : ℝ)*N)+V/N)) =
      hyperbolaEnvelope H T0*((F.card : ℝ)*(1+V/N)+(U/N)*(∑ d ∈ F,1/(d : ℝ))) := by
    rw [← Finset.mul_sum]
    simp_rw [he]
    rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum]
  rw [hsum]
  apply mul_le_mul_of_nonneg_left _ (hyperbolaEnvelope_nonneg H T0)
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (real_level_card_bound P v s hD) (by positivity)
  · exact mul_le_mul_of_nonneg_left (real_level_reciprocal_bound P v s hD) (by positivity)

end ErdosVarianceLargeCount

end

end Erdos970

end OAI
