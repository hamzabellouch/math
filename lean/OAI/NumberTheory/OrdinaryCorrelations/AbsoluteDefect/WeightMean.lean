import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.BetaZ
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Avg
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PrimeSystem
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.VertexWeight
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.KappaPos

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
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff
open Finset Classical
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.FiniteIntegration OrdinaryCorrelations.SignedTrace
open Finset Classical
noncomputable section
variable {S : PrimeSystem}

def weightMean (S : PrimeSystem) : ℝ := ∏ p : S.Index, (1+S.amplitude p/(p:ℝ))

lemma vertex_local_moment (p : S.Index) (b : ℤ) (j : ℕ) :
    avg (fun r:ZMod (p:ℕ) => ((S.beta p)⁻¹^(if r+(b:ZMod (p:ℕ))=0 then (1:ℕ) else 0))^j)=
      1+((S.beta p)⁻¹^j-1)/(p:ℝ) := by
  have he : (fun r:ZMod (p:ℕ) => ((S.beta p)⁻¹^(if r+(b:ZMod (p:ℕ))=0 then (1:ℕ) else 0))^j)=
      fun r => 1+if r=-(b:ZMod (p:ℕ)) then (S.beta p)⁻¹^j-1 else 0 := by
    funext r
    by_cases hr : r+(b:ZMod (p:ℕ))=0
    · simp [add_eq_zero_iff_eq_neg.mp hr]
    · have hn : r≠-(b:ZMod (p:ℕ)) := by simpa only [add_eq_zero_iff_eq_neg] using hr
      simp only [hr,hn,ite_false,pow_zero,one_pow,add_zero]
  rw [he]
  have hp : (p:ℝ)≠0 := by exact_mod_cast (S.prime_mem p p.property).ne_zero
  simp only [OrdinaryCorrelations.FiniteIntegration.avg,sum_add_distrib,sum_const,
    Finset.card_univ,ZMod.card,nsmul_eq_mul,mul_one,sum_ite_eq',Finset.mem_univ,ite_true]
  field_simp

theorem vertexWeight_moment (S : PrimeSystem) (b : ℤ) (j : ℕ) :
    avg (fun r:S.Residues => S.vertexWeight r b^j)=
      ∏ p : S.Index, (1+((S.beta p)⁻¹^j-1)/(p:ℝ)) := by
  simp only [vertexWeight,←Finset.prod_pow]
  trans ∏ p : S.Index, avg (fun r : ZMod (p:ℕ) =>
    ((S.beta p)⁻¹^(if r+(b:ZMod (p:ℕ))=0 then (1:ℕ) else 0))^j)
  · convert avg_product (fun p : S.Index => fun r : ZMod (p:ℕ) =>
      ((S.beta p)⁻¹^(if r+(b:ZMod (p:ℕ))=0 then (1:ℕ) else 0))^j) using 1
    congr 1
    exact Subsingleton.elim _ _
  · apply prod_congr rfl
    intro p hp
    exact vertex_local_moment p b j

theorem vertexWeight_mean (S : PrimeSystem) (b : ℤ) :
    avg (fun r:S.Residues => S.vertexWeight r b)=S.weightMean := by
  have hm := vertexWeight_moment S b 1
  simpa only [pow_one,beta,inv_inv,add_sub_cancel_left,weightMean] using hm

lemma amplitude_nonneg (p : S.Index) : 0≤S.amplitude p := by
  unfold amplitude
  split_ifs
  · exact A_pos.le
  · norm_num

theorem vertexWeight_second_moment_exp (S : PrimeSystem) (b : ℤ) :
    avg (fun r:S.Residues => S.vertexWeight r b^2) ≤
      Real.exp (∑ p : S.Index,(S.amplitude p^2+2*S.amplitude p)/(p:ℝ)) := by
  rw [vertexWeight_moment,Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro prime _hprime
    simp only [beta,inv_inv]
    have ha := amplitude_nonneg prime
    have hprime : 0<(prime:ℝ) := by exact_mod_cast (S.prime_mem prime prime.property).pos
    apply add_nonneg (by norm_num) (div_nonneg _ hprime.le)
    nlinarith
  · intro prime _hprime
    simp only [beta,inv_inv]
    have he : (1+S.amplitude prime)^2-1=S.amplitude prime^2+2*S.amplitude prime := by ring
    rw [he]
    calc
      _ = (S.amplitude prime^2+2*S.amplitude prime)/(prime:ℝ)+1 := add_comm _ _
      _ ≤ _ := Real.add_one_le_exp _

end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
