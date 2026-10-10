import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightLeaf
import OAI.NumberTheory.Ostmann.Construction.InitialEtaRepeatedPhysical
import OAI.NumberTheory.Ostmann.Construction.RepeatedWeightCounting

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators FourierTransform
namespace Ostmann.Construction.InitialEta

lemma sqrt_weight_algebra {A X M Q K : ℝ} (hX : 0≤X) :
    (A/M)*(Real.sqrt X*K*(Real.sqrt M/Q))=A*K*Real.sqrt (X/M)/Q := by
  calc
    _ = A*K*(Real.sqrt X*(Real.sqrt M/M))/Q := by ring
    _ = A*K*(Real.sqrt X/Real.sqrt M)/Q := by rw [Real.sqrt_div_self']; ring
    _ = _ := by rw [Real.sqrt_div hX]

theorem weighted_tuplePhysical_bound (d : Decomposition) (P : Finset ℕ)
    (giant bulk spectator : PrimeSource) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (aux : ι → PrimeSource) (b s : ℕ) (tb td : ℤ) {X A Δ W : ℝ}
    (hX : 0<X) (hA : 0≤A) (x : JointSample giant bulk spectator aux b s)
    (hmass : (jointPrior giant bulk spectator aux b s).mass x≤A/(∏i,(tupleValues x i:ℝ)))
    (hperiod : ((∏q:↥(tupleDistinctPrimes (tupleValues x)),(q:ℕ):ℕ):ℝ)/4<X)
    (hlog : Real.log X+Δ-W≤Real.log (∏i,tupleValues x i:ℕ)) :
    (jointPrior giant bulk spectator aux b s).mass x*
        ‖tuplePhysical d P giant bulk spectator aux b s tb td X x‖≤
      A*‖𝓕 SchwartzCutoff.psi 0‖*Real.exp ((-Δ+W)/2)*
        (1/((∏q:↥(tupleDistinctPrimes (tupleValues x)),(q:ℕ):ℕ):ℝ)) := by
  have hM : 0<(∏i,tupleValues x i:ℕ) := Finset.prod_pos fun i _ => (tupleValues_prime x i).pos
  have hMr : 0<((∏i,tupleValues x i:ℕ):ℝ) := by exact_mod_cast hM
  have hQr : 0≤((∏q:↥(tupleDistinctPrimes (tupleValues x)),(q:ℕ):ℕ):ℝ) := Nat.cast_nonneg _
  have hphys := tuplePhysical_repeated_bound d P giant bulk spectator aux b s tb td hX x hperiod
  have hs := Arithmetic.sqrt_ratio_le_of_log_lower X (∏i,tupleValues x i:ℕ) Δ W hX hMr hlog
  rw [← Nat.cast_prod] at hmass
  calc
    _ ≤ (A/((∏i,tupleValues x i:ℕ):ℝ))*
        (Real.sqrt X*‖𝓕 SchwartzCutoff.psi 0‖*
          (Real.sqrt (∏i,tupleValues x i:ℕ)/(∏q:↥(tupleDistinctPrimes (tupleValues x)),(q:ℕ):ℕ))) :=
      mul_le_mul hmass hphys (norm_nonneg _) (div_nonneg hA hMr.le)
    _ = A*‖𝓕 SchwartzCutoff.psi 0‖*Real.sqrt (X/(∏i,tupleValues x i:ℕ))/
        (∏q:↥(tupleDistinctPrimes (tupleValues x)),(q:ℕ):ℕ) := sqrt_weight_algebra hX.le
    _ ≤ A*‖𝓕 SchwartzCutoff.psi 0‖*Real.exp ((-Δ+W)/2)/
        (∏q:↥(tupleDistinctPrimes (tupleValues x)),(q:ℕ):ℕ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (mul_nonneg hA (norm_nonneg _))) hQr
    _ = _ := by ring

theorem repeatedContribution_bound (d : Decomposition) (P : Finset ℕ)
    (giant bulk spectator : PrimeSource) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (aux : ι → PrimeSource) (b s : ℕ) (tb td : ℤ) {X A Δ W : ℝ}
    (hX : 0<X) (hA : 0≤A)
    (hmass : ∀x,(jointPrior giant bulk spectator aux b s).mass x≤A/(∏i,(tupleValues x i:ℝ)))
    (hperiod : ∀x,(jointPrior giant bulk spectator aux b s).mass x≠0 →
      tupleBins tb td x≠0 → ¬Function.Injective (tupleValues x) →
      ((∏q:↥(tupleDistinctPrimes (tupleValues x)),(q:ℕ):ℕ):ℝ)/4<X)
    (hlog : ∀x,(jointPrior giant bulk spectator aux b s).mass x≠0 →
      tupleBins tb td x≠0 → Real.log X+Δ-W≤Real.log (∏i,tupleValues x i:ℕ)) :
    ‖repeatedContribution d P giant bulk spectator aux b s tb td X‖≤
      A*‖𝓕 SchwartzCutoff.psi 0‖*Real.exp ((-Δ+W)/2)*
        (Fintype.card (Position b s ι):ℝ)^(Fintype.card (Position b s ι))*
        Real.exp (harmonicPrimeMass (candidateValues giant bulk spectator aux b s)) := by
  classical
  let μ := jointPrior giant bulk spectator aux b s
  let K := A*‖𝓕 SchwartzCutoff.psi 0‖*Real.exp ((-Δ+W)/2)
  have hK : 0≤K := by dsimp [K]; positivity
  calc
    _ ≤ ∑x:JointSample giant bulk spectator aux b s,
        ‖(μ.mass x:ℂ)*(if Function.Injective (tupleValues x) then 0
          else tuplePhysical d P giant bulk spectator aux b s tb td X x)‖ := norm_sum_le _ _
    _ ≤ ∑x:JointSample giant bulk spectator aux b s,
        K*(1/((∏q:↥(tupleDistinctPrimes (tupleValues x)),(q:ℕ):ℕ):ℝ)) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (μ.mass_nonneg x)]
      by_cases hi : Function.Injective (tupleValues x)
      · simp only [hi,ite_true,norm_zero,mul_zero]
        positivity
      · rw [ite_eq_right hi]
        by_cases hm : μ.mass x=0
        · rw [hm,zero_mul]; positivity
        · by_cases hb : tupleBins tb td x=0
          · rw [tuplePhysical_eq_zero_of_bins_zero d P giant bulk spectator aux b s tb td X x hb,norm_zero,mul_zero]
            positivity
          · exact weighted_tuplePhysical_bound d P giant bulk spectator aux b s tb td hX hA x
              (hmass x) (hperiod x hm hb hi) (hlog x hm hb)
    _ = K*(∑x:JointSample giant bulk spectator aux b s,
        1/((∏q:↥(tupleDistinctPrimes (tupleValues x)),(q:ℕ):ℕ):ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ K*((Fintype.card (Position b s ι):ℝ)^(Fintype.card (Position b s ι))*
        Real.exp (harmonicPrimeMass (candidateValues giant bulk spectator aux b s))) :=
      mul_le_mul_of_nonneg_left (original_tuple_reciprocal_distinct_sum_le giant bulk spectator aux b s) hK
    _ = _ := by dsimp only [K]; ring

end Ostmann.Construction.InitialEta

end

end OAI
