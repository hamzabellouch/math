import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalDensity
import OAI.NumberTheory.TwoPoint.Halasz.HalaszPhaseTranslation

namespace OAI

/-! Prefix density controls the centered typical amplitude before the
near-frequency square is taken. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma mrt_typical_prefix_count {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (k : ℕ) [NeZero k] :
    (((Icc 1 k).filter (fun n => ¬mrtTypical J P n)).card : ℝ) =
      (k:ℝ)*(uniformFiniteLaw (Fin k)).probability
        (fun n => ¬mrtTypical J P (1+n.val)) := by
  unfold FiniteLaw.probability FiniteLaw.average uniformFiniteLaw
  dsimp only
  rw [← mul_sum, Fintype.card_fin, ← mul_assoc]
  have hk : (k:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne k
  rw [mul_one_div_cancel hk, one_mul]
  calc
    _ = ∑ n ∈ Icc 1 k, if ¬mrtTypical J P n then (1:ℝ) else 0 := by
      rw [← sum_filter]
      simp
    _ = _ := by
      symm
      apply sum_bij (fun n : Fin k => fun _ => 1+n.val)
      · intro n _
        exact mem_Icc.mpr ⟨by omega,by have hn:=n.isLt; omega⟩
      · intro n _ m _ he
        apply Fin.ext
        omega
      · intro n hn
        refine ⟨⟨n-1,?_⟩,mem_univ _,?_⟩
        · have hn := mem_Icc.mp hn
          omega
        · have hn := mem_Icc.mp hn
          change 1+(n-1)=n
          omega
      · intro n _
        simp

lemma mrt_typical_prefix_difference {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F) (t : ℝ) (k : ℕ) :
    ‖halaszPhaseMean (mrtTypicalCoefficient J P F) t k - halaszPhaseMean F t k‖ ≤
      (((Icc 1 k).filter (fun n => ¬mrtTypical J P n)).card : ℝ) := by
  unfold halaszPhaseMean
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Icc 1 k,
        ‖mrtTypicalCoefficient J P F n*halaszPowerPhase t n-F n*halaszPowerPhase t n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 k, if ¬mrtTypical J P n then (1:ℝ) else 0 := by
      apply sum_le_sum
      intro n hn
      by_cases ht : mrtTypical J P n
      · simp [mrtTypicalCoefficient,ht]
      · simpa only [mrtTypicalCoefficient,ht,ite_false,zero_mul,zero_sub,norm_neg,
          norm_mul,halasz_power_phase_norm,mul_one,not_false_eq_true,ite_true]
          using hF n (mem_Icc.mp hn).1
    _ = _ := by rw [← sum_filter]; simp

/-- The phase-centered typical prefix differs from the full prefix by
linear density, uniformly at all dyadic prefixes and all center phases. -/
theorem mrt_typical_centered_prefix_density : ∃ C : ℝ, 0<C ∧
    ∀ᶠ N : ℕ in atTop, ∀ P Q : ℝ, ∀ J : ℕ,
      2≤P → P≤Q → 1≤Real.log Q →
      (∀ j∈Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ F : ℕ → ℂ, OneBounded F → ∀ τ : ℝ, ∀ k∈Icc N (2*N),
      ‖halaszPhaseMean (halaszTwistedFunction (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) τ) 0 k -
        halaszPhaseMean (halaszTwistedFunction F τ) 0 k‖ ≤
        C*(Real.log P/Real.log Q)*k := by
  obtain ⟨C,hC,hdensity⟩ := mrt_typical_density
  refine ⟨C,hC,?_⟩
  have hlog : Tendsto (fun N:ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually hdensity,
    hlog.eventually (eventually_ge_atTop (1:ℝ)),eventually_ge_atTop 2]
    with N hdensity hLN hN2
  intro P Q J hP hPQ hQ hmax F hF τ k hk
  have hNk := (mem_Icc.mp hk).1
  have hN0 : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hNkR : (N:ℝ)≤k := by exact_mod_cast hNk
  have : NeZero k := ⟨by omega⟩
  let V := fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)
  have hs : Real.sqrt (Real.log N) ≤ (Real.log N)^(99/100:ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hLN (by norm_num)
  have hscale : (1/2:ℝ)*Real.exp ((Real.log N)^(199/200:ℝ)) ≤ k := by
    have hp := Real.rpow_le_self_of_one_le hLN (show (199/200:ℝ)≤1 by norm_num)
    have he := Real.exp_le_exp.mpr hp
    rw [Real.exp_log hN0] at he
    nlinarith [Real.exp_pos ((Real.log N)^(199/200:ℝ))]
  have heq (n:ℕ) :
      mrtTypical univ (fun j:{j:ℕ // j∈(Icc 1 J:Finset ℕ)} => V j) n ↔
        mrtTypical (Icc 1 J) V n := by simp [mrtTypical]
  have hp := hdensity P Q J hP hPQ hQ
    (fun j hj => (hmax j hj).trans (Real.exp_le_exp.mpr hs)) 1 k hscale
  change (uniformFiniteLaw (Fin k)).probability
    (fun n => ¬mrtTypical univ
      (fun j:{j:ℕ // j∈(Icc 1 J:Finset ℕ)} => V j) (1+n.val)) ≤ _ at hp
  have hp' : (uniformFiniteLaw (Fin k)).probability
      (fun n => ¬mrtTypical (Icc 1 J) V (1+n.val)) ≤ C*(Real.log P/Real.log Q) := by
    simpa only [heq,mul_div_assoc] using hp
  have hcount : (((Icc 1 k).filter (fun n => ¬mrtTypical (Icc 1 J) V n)).card:ℝ) ≤
      C*(Real.log P/Real.log Q)*k := by
    rw [mrt_typical_prefix_count]
    nlinarith [mul_le_mul_of_nonneg_left hp' (Nat.cast_nonneg k : (0:ℝ)≤k)]
  rw [← halasz_typical_twist]
  exact (mrt_typical_prefix_difference (Icc 1 J) V (halaszTwistedFunction F τ)
    (halasz_twisted_oneBounded F hF τ) 0 k).trans hcount

end TwoPointCorrelations

end OAI
