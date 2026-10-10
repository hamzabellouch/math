import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.LocalSampling
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BinnedRamareError

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinaryCorrelations.SourcePrimeFactor
open Finset OrdinaryDirichletMeanSquare

lemma binnedRamare_error_identity (P : Finset ℕ) (M : ℕ → ℕ) (f : ℕ → ℂ)
    (X E : ℕ) (hrange : ∀p∈P,X-E≤p*M p ∧ p*M p≤X+E) (t : ℝ) :
    polynomial (Ioc 0 (2*(X+E))) (fun n => binnedRamareCoefficient P M f n/(n:ℂ))
      (fun n => Real.log n) t -
    polynomial (Ioc X (2*X)) (fun n => f n/(n:ℂ)) (fun n => Real.log n) t =
    polynomial (Ioc (X-E) (2*(X+E))) (fun n => binnedRamareError P M f X n/(n:ℂ))
      (fun n => Real.log n) t := by
  classical
  have hsub : Finset.Ioc (X-E) (2*(X+E)) ⊆ Finset.Ioc 0 (2*(X+E)) := by
    intro n hn
    have h := Finset.mem_Ioc.mp hn
    apply Finset.mem_Ioc.mpr
    constructor <;> omega
  have hbin : polynomial (Ioc 0 (2*(X+E)))
      (fun n => binnedRamareCoefficient P M f n/(n:ℂ)) (fun n => Real.log n) t =
      polynomial (Ioc (X-E) (2*(X+E)))
      (fun n => binnedRamareCoefficient P M f n/(n:ℂ)) (fun n => Real.log n) t := by
    symm
    apply sum_subset hsub
    intro n hn hnot
    dsimp only
    rw [binnedRamare_support P M f X E n hrange hnot]
    simp
  rw [hbin]
  have hfilter : (Finset.Ioc (X-E) (2*(X+E))).filter (fun n => n∈Finset.Ioc X (2*X))=Finset.Ioc X (2*X) := by
    ext n
    simp only [mem_filter,Finset.mem_Ioc]
    constructor
    · exact fun h => h.2
    · intro h
      constructor
      · constructor <;> omega
      · exact h
  unfold polynomial binnedRamareError
  simp_rw [sub_div,sub_mul,ite_div,ite_mul,zero_div,zero_mul]
  rw [sum_sub_distrib,←sum_filter,hfilter]

lemma binnedRamare_weighted_error_energy (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    (M : ℕ → ℕ) {f : ℕ → ℂ} (hf : OneBounded f) (hm : Multiplicative f)
    (X E : ℕ) (hEX : E<X) (hrange : ∀p∈P,X-E≤p*M p ∧ p*M p≤X+E) :
    (∑n∈Ioc (X-E) (2*(X+E)),‖binnedRamareError P M f X n/(n:ℂ)‖^2) ≤
      4*((ramareArithmeticExceptions P (X-E) (2*(X+E))).card+6*(E:ℝ))/((X-E:ℕ):ℝ)^2 := by
  have hLp : (0:ℝ)<(X-E:ℕ) := by exact_mod_cast (Nat.sub_pos_of_lt hEX)
  calc
    _ ≤ ∑n∈Ioc (X-E) (2*(X+E)),‖binnedRamareError P M f X n‖^2/((X-E:ℕ):ℝ)^2 := by
      apply sum_le_sum
      intro n hn
      simp only [norm_div,Complex.norm_natCast,div_pow]
      apply div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hLp)
      exact pow_le_pow_left₀ hLp.le (by exact_mod_cast (Finset.mem_Ioc.mp hn).1.le) 2
    _ = (∑n∈Ioc (X-E) (2*(X+E)),‖binnedRamareError P M f X n‖^2)/((X-E:ℕ):ℝ)^2 := by rw [sum_div]
    _ ≤ _ := div_le_div_of_nonneg_right (binnedRamareError_energy P hP M hf hm X E hrange) (sq_nonneg _)

theorem binnedRamare_sampled_error (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    (M : ℕ → ℕ) {f : ℕ → ℂ} (hf : OneBounded f) (hm : Multiplicative f)
    (X E : ℕ) (hX : 0<X) (hEX : 2*E≤X)
    (hrange : ∀p∈P,X-E≤p*M p ∧ p*M p≤X+E)
    (R : Finset ℝ) {T : ℝ} (hT : 0≤T)
    (hR : ∀t∈R,t∈Set.Icc (-T) T) (hsep : ∀t∈R,∀u∈R,t≠u → 1≤|t-u|) :
    (∑t∈R,‖polynomial (Ioc (X-E) (2*(X+E)))
      (fun n => binnedRamareError P M f X n/(n:ℂ)) (fun n => Real.log n) t‖^2) ≤
    (4*Real.exp (1+1/4)*gaussianConstant*(T+1+2*((X:ℝ)+E))*(2+(Real.log 6)^2))*
      (4*((ramareArithmeticExceptions P (X-E) (2*(X+E))).card+6*(E:ℝ))/((X-E:ℕ):ℝ)^2) := by
  have hEL : E<X := by omega
  have hLp : (0:ℝ)<(X-E:ℕ) := by exact_mod_cast (Nat.sub_pos_of_lt hEL)
  have hUp : (0:ℝ)<2*((X:ℝ)+E) := by exact_mod_cast (by omega : 0<2*(X+E))
  have hbound : ∀n∈Finset.Ioc (X-E) (2*(X+E)),0<(n:ℝ) ∧ (n:ℝ)≤2*((X:ℝ)+E) := by
    intro n hn
    constructor
    · exact hLp.trans (by exact_mod_cast (Finset.mem_Ioc.mp hn).1)
    · exact_mod_cast (Finset.mem_Ioc.mp hn).2
  have hband : ∀n∈Finset.Ioc (X-E) (2*(X+E)),|Real.log (n:ℝ)-Real.log ((X-E:ℕ):ℝ)|≤Real.log 6 := by
    intro n hn
    have hnlo : ((X-E:ℕ):ℝ)≤n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1.le
    have hnhi : (n:ℝ)≤6*((X-E:ℕ):ℝ) := by
      have hh : n≤6*(X-E) := by have := (Finset.mem_Ioc.mp hn).2; omega
      exact_mod_cast hh
    have hloglo := Real.log_le_log hLp hnlo
    have hloghi := Real.log_le_log (hbound n hn).1 hnhi
    rw [Real.log_mul (by norm_num) hLp.ne'] at hloghi
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hh := OrdinaryMellinSampling.band_spaced_mean_square
    (Ioc (X-E) (2*(X+E))) (fun n => binnedRamareError P M f X n/(n:ℂ)) R
    hUp hT (Real.log_nonneg (by norm_num : (1:ℝ)≤6)) hbound hband hR hsep
  apply hh.trans
  apply mul_le_mul_of_nonneg_left
    (binnedRamare_weighted_error_energy P hP M hf hm X E hEL hrange)
  unfold gaussianConstant
  positivity

end OrdinaryCorrelations.SourcePrimeFactor

end

end OAI
