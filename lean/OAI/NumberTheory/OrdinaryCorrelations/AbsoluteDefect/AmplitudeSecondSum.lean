import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.CardTreeVerticesLe
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.WeightMean

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

lemma amplitude_second_sum (S : PrimeSystem) :
    (∑ p : S.Index,(S.amplitude p^2+2*S.amplitude p)/(p:ℝ))=
      (A^2+2*A)*S.harmonicCore+3*S.harmonicCenter := by
  have hc : (∑ p : S.Index,if S.IsCore p then (p:ℝ)⁻¹ else 0)=S.harmonicCore := by
    have he := sum_subtype (F:=inferInstance) (p:=fun p:S.Index => S.IsCore p)
      (univ.filter (fun p:S.Index => S.IsCore p)) (by simp) (fun p:S.Index => (p:ℝ)⁻¹)
    simpa only [sum_filter,harmonicCore] using he
  have hz : (∑ p : S.Index,if S.IsCore p then 0 else (p:ℝ)⁻¹)=S.harmonicCenter := by
    have he := sum_subtype (F:=inferInstance) (p:=fun p:S.Index => ¬S.IsCore p)
      (univ.filter (fun p:S.Index => ¬S.IsCore p)) (by simp) (fun p:S.Index => (p:ℝ)⁻¹)
    simpa only [sum_filter,harmonicCenter,ite_not] using he
  rw [←hc,←hz,mul_sum,mul_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  unfold amplitude
  split_ifs <;> simp only [div_eq_mul_inv] <;> ring

theorem vertexWeight_second_moment_source (S : PrimeSystem) (b : ℤ) :
    avg (fun r:S.Residues => S.vertexWeight r b^2) ≤
      Real.exp ((A^2+2*A)*S.harmonicCore+3*S.harmonicCenter) := by
  simpa only [amplitude_second_sum] using vertexWeight_second_moment_exp S b

theorem vertexWeight_event_bound (S : PrimeSystem) (b : ℤ) (E : S.Residues → Prop) :
    avg (fun r => if E r then S.vertexWeight r b else 0) ≤
      Real.sqrt (avg (fun r:S.Residues => S.vertexWeight r b^2))*
        Real.sqrt (avg (fun r:S.Residues => if E r then (1:ℝ) else 0)) := by
  rw [←Real.sqrt_mul (avg_nonneg (fun r => sq_nonneg (S.vertexWeight r b)))]
  apply Real.le_sqrt_of_sq_le
  have h := sum_mul_sq_le_sq_mul_sq (R:=ℝ) (univ:Finset S.Residues)
    (fun r => S.vertexWeight r b) (fun r => if E r then 1 else 0)
  have h' := mul_le_mul_of_nonneg_left h (sq_nonneg ((Fintype.card S.Residues:ℝ)⁻¹))
  unfold FiniteIntegration.avg
  simp only [mul_ite,mul_one,mul_zero,ite_pow,one_pow,zero_pow (by norm_num : (2:ℕ)≠0)] at h'
  nlinarith

end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
