import OAI.NumberTheory.Jacobsthal.Primes.PrimeProductOmissions
import OAI.NumberTheory.Jacobsthal.Sieve.SourcePairSieve

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
namespace ErdosVarianceLargeCount
open NumberTheoryLean ErdosHyperbolaError ErdosPrimeInputs.PrimeProductOmissions
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

def patternCard (T0 T1 : ℕ) : ℕ := T0*T0.totient*T1*T1.totient

theorem patternCard_pos (T0 T1 : ℕ) (hT0 : 0 < T0) (hT1 : 0 < T1) : 0 < patternCard T0 T1 := by
  unfold patternCard
  exact mul_pos (mul_pos (mul_pos hT0 (Nat.totient_pos.mpr hT0)) hT1) (Nat.totient_pos.mpr hT1)

theorem sourceMain_totient_cancellation (H T0 T1 : ℕ) (hH : 0 < H) (hT0 : 0 < T0) (hT1 : 0 < T1)
    (hT0H : T0 ∣ H) (hcop : H.Coprime T1) (U V : ℝ) :
    sourceMain H T0 T1 U V*((H*T1 : ℕ) : ℝ)/((H*T1).totient : ℝ) =
      U*(V/(H : ℝ))/(patternCard T0 T1 : ℝ) := by
  have hHN : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  have h0N : (T0 : ℝ) ≠ 0 := by exact_mod_cast hT0.ne'
  have h1N : (T1 : ℝ) ≠ 0 := by exact_mod_cast hT1.ne'
  have hph : (H.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hH).ne'
  have hp0 : (T0.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hT0).ne'
  have hp1 : (T1.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hT1).ne'
  unfold sourceMain patternCard
  rw [source_totient_product H T0 hT0H hT0,Nat.totient_mul hcop]
  push_cast
  field_simp

theorem source_main_uniform_upper : ∃ C v0 : ℝ,0 < C ∧ 2 ≤ v0 ∧
    ∀ v : ℝ,v0 ≤ v → ∀ (H T0 T1 : ℕ),0 < H → 0 < T0 → 0 < T1 →
      T0 ∣ H → H.Coprime T1 → ∀ (U V s : ℝ),0 ≤ U → 0 ≤ V → V ≤ 2*(H : ℝ) → 0 ≤ s →
      sourceMain H T0 T1 U V*
        (∏ t ∈ reducedPrimes ⌊v⌋₊ (H*T1),(1-1/(t : ℝ)))*
          (1+Real.exp (-s/96)) ≤ C*U/((patternCard T0 T1 : ℝ)*Real.log v) := by
  obtain ⟨C,v0,hC,hv0,hEuler⟩ := reduced_product_upper
  refine ⟨4*C,v0,by positivity,hv0,?_⟩
  intro v hv H T0 T1 hH hT0 hT1 hT0H hcop U V s hU hV hVH hs
  have hv1 : 1 < v := by linarith
  have hlog : 0 < Real.log v := Real.log_pos hv1
  have hHN : (0 : ℝ) < H := by exact_mod_cast hH
  have hpat : (0 : ℝ) < patternCard T0 T1 := by exact_mod_cast patternCard_pos T0 T1 hT0 hT1
  have hX : 0 ≤ sourceMain H T0 T1 U V := by dsimp [sourceMain];positivity
  have he := hEuler v hv (H*T1) (mul_pos hH hT1)
  have hmul := mul_le_mul_of_nonneg_left he hX
  have heq : sourceMain H T0 T1 U V*(C*(((H*T1 : ℕ) : ℝ)/((H*T1).totient : ℝ))/Real.log v) =
      C*(U*(V/(H : ℝ))/(patternCard T0 T1 : ℝ))/Real.log v := by
    rw [show sourceMain H T0 T1 U V*(C*(((H*T1 : ℕ) : ℝ)/((H*T1).totient : ℝ))/Real.log v) =
      C*(sourceMain H T0 T1 U V*((H*T1 : ℕ) : ℝ)/((H*T1).totient : ℝ))/Real.log v by ring,
      sourceMain_totient_cancellation H T0 T1 hH hT0 hT1 hT0H hcop]
  have hEuler' : sourceMain H T0 T1 U V*
      (∏ t ∈ reducedPrimes ⌊v⌋₊ (H*T1),(1-1/(t : ℝ))) ≤
        C*(U*(V/(H : ℝ))/(patternCard T0 T1 : ℝ))/Real.log v := by
    simpa only [ErdosPrimeInputs.SubsetPrimeSieve.euler,one_div] using hmul.trans_eq heq
  have hVdiv : V/(H : ℝ) ≤ 2 := (div_le_iff₀ hHN).mpr hVH
  have hEexp : 1+Real.exp (-s/96) ≤ 2 := by
    have hh : Real.exp (-s/96) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have hm1 := mul_le_mul_of_nonneg_right hEuler' (show 0 ≤ 1+Real.exp (-s/96) by positivity)
  have hm2 := mul_le_mul_of_nonneg_left hEexp
    (show 0 ≤ C*(U*(V/(H : ℝ))/(patternCard T0 T1 : ℝ))/Real.log v by positivity)
  have hlast : (C*(U*(V/(H : ℝ))/(patternCard T0 T1 : ℝ))/Real.log v)*2 ≤
      (4*C)*U/((patternCard T0 T1 : ℝ)*Real.log v) := by
    calc
      _ = (2*C*U/((patternCard T0 T1 : ℝ)*Real.log v))*(V/(H : ℝ)) := by ring
      _ ≤ (2*C*U/((patternCard T0 T1 : ℝ)*Real.log v))*2 :=
        mul_le_mul_of_nonneg_left hVdiv (by positivity)
      _ = _ := by ring
  exact hm1.trans (hm2.trans hlast)

end ErdosVarianceLargeCount

end

end Erdos970

end OAI
