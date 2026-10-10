import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SumFinFunSucc
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SourceBlockMatrix

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
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.Localization
open Finset Classical Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {S : PrimeSystem} {B τ C₀ T : ℝ}

theorem sourceBlockMatrix_trace_expansion (D : S.DivisorFamily B τ C₀) (h L : ℕ)
    (cut : S.Cutoffs T) (a : ℕ → ℂ) (D₀ k : ℕ) :
    let M := sourceBlockMatrix D h L cut a D₀ k
    ((M.conjTranspose*M)^⌊B⌋₊).trace=
      ∑ v : Fin (⌊B⌋₊+1) → Fin D₀,if v (Fin.last ⌊B⌋₊)=v 0 then
        ∑ x : Fin ⌊B⌋₊ → Fin D₀,
          ∏ j : Fin ⌊B⌋₊,star (M (x j) (v j.castSucc))*M (x j) (v j.succ)
      else 0 := by
  exact matrix_gram_trace_expansion _ _

lemma sourceBlockMatrix_denominator_cancel (D : S.DivisorFamily B τ C₀) (h L : ℕ)
    (cut : S.Cutoffs T) (a : ℕ → ℂ) (D₀ k : ℕ) (x y : Fin D₀) :
    let r := S.integerResidues ((k:ℤ)*D₀)
    sourceBlockMatrix D h L cut a D₀ k x y*
      (Real.sqrt (S.vertexWeight r (x.val+1)):ℂ)*
      (Real.sqrt (S.vertexWeight r (y.val+1)):ℂ)=
    if VertexAllowed D h L ((k:ℤ)*D₀+x.val+1) ∧
       VertexAllowed D h L ((k:ℤ)*D₀+y.val+1) then
      ∑ d∈D.members,if (y.val:ℤ)+1=(x.val:ℤ)+1+(h:ℤ)*d then
        a d*(S.divisorEdgeWeight cut r d (x.val+1) (y.val+1):ℝ) else 0
      else 0 := by
  dsimp only
  unfold sourceBlockMatrix
  simp only [←add_assoc]
  split_ifs with hy
  · rw [Finset.sum_mul,Finset.sum_mul]
    apply sum_congr rfl
    intro d hd
    split_ifs with he
    · have hx := S.vertexWeight_pos (S.integerResidues ((k:ℤ)*D₀)) (x.val+1)
      have hy := S.vertexWeight_pos (S.integerResidues ((k:ℤ)*D₀)) (y.val+1)
      rw [Real.sqrt_mul hx.le,Complex.ofReal_div,Complex.ofReal_mul]
      have hxs : (Real.sqrt (S.vertexWeight (S.integerResidues ((k:ℤ)*D₀)) (x.val+1)):ℂ)≠0 :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hx))
      have hys : (Real.sqrt (S.vertexWeight (S.integerResidues ((k:ℤ)*D₀)) (y.val+1)):ℂ)≠0 :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hy))
      field_simp
    · simp
  · simp

theorem sourceBlockMatrix_bilinear (D : S.DivisorFamily B τ C₀) (h L : ℕ)
    (cut : S.Cutoffs T) (a : ℕ → ℂ) (D₀ k : ℕ) (F G : Fin D₀ → ℂ)
    (hF : ∀ x,‖F x‖≤1) (hG : ∀ x,‖G x‖≤1) :
    let r := S.integerResidues ((k:ℤ)*D₀)
    ‖∑ x,∑ y,F x*G y*(if VertexAllowed D h L ((k:ℤ)*D₀+x.val+1) ∧
        VertexAllowed D h L ((k:ℤ)*D₀+y.val+1) then
        ∑ d∈D.members,if (y.val:ℤ)+1=(x.val:ℤ)+1+(h:ℤ)*d then
          a d*(S.divisorEdgeWeight cut r d (x.val+1) (y.val+1):ℝ) else 0
        else 0)‖ ≤
      ‖sourceBlockMatrix D h L cut a D₀ k‖*∑ x:Fin D₀,S.vertexWeight r (x.val+1) := by
  dsimp only
  have hb := weighted_matrix_bilinear (sourceBlockMatrix D h L cut a D₀ k)
    (fun x => S.vertexWeight (S.integerResidues ((k:ℤ)*D₀)) (x.val+1))
    (fun x => (S.vertexWeight_pos _ _).le) F G hF hG
  convert hb using 1
  congr 1
  apply sum_congr rfl
  intro x hx
  apply sum_congr rfl
  intro y hy
  rw [←sourceBlockMatrix_denominator_cancel D h L cut a D₀ k x y]
  ring

end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
