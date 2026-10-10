import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.BetaZ
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PrimeSystem
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceSystem
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FreeResidues
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DivisorPrimeFactor
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.WeightedMatrixBilinear
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.NormPowLeGramTrace

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

def sourceBlockMatrix (D : S.DivisorFamily B τ C₀) (h L : ℕ) (cut : S.Cutoffs T)
    (a : ℕ → ℂ) (D₀ k : ℕ) : Matrix (Fin D₀) (Fin D₀) ℂ := fun x y =>
  let n : ℤ := k*D₀
  let b : ℤ := x.val+1
  let c : ℤ := y.val+1
  if VertexAllowed D h L (n+b) ∧ VertexAllowed D h L (n+c) then
    ∑ d∈D.members,if c=b+(h:ℤ)*d then
      a d*((S.divisorEdgeWeight cut (S.integerResidues n) d b c /
        Real.sqrt (S.vertexWeight (S.integerResidues n) b*
          S.vertexWeight (S.integerResidues n) c)):ℝ) else 0
  else 0

lemma sourceBlockMatrix_entry (D : S.DivisorFamily B τ C₀) (h L : ℕ) (hh : 0<h)
    (cut : S.Cutoffs T) (a : ℕ → ℂ) (D₀ k : ℕ) (x y : Fin D₀)
    (d : ℕ) (hd : d∈D.members) (hedge : (y.val:ℤ)+1=(x.val:ℤ)+1+(h:ℤ)*d) :
    sourceBlockMatrix D h L cut a D₀ k x y=
      if VertexAllowed D h L ((k:ℤ)*D₀+x.val+1) ∧
        VertexAllowed D h L ((k:ℤ)*D₀+y.val+1) then
        a d*((S.divisorEdgeWeight cut (S.integerResidues ((k:ℤ)*D₀)) d (x.val+1) (y.val+1) /
          Real.sqrt (S.vertexWeight (S.integerResidues ((k:ℤ)*D₀)) (x.val+1)*
            S.vertexWeight (S.integerResidues ((k:ℤ)*D₀)) (y.val+1))):ℝ)
      else 0 := by
  unfold sourceBlockMatrix
  simp only [←add_assoc]
  split_ifs with hy
  · rw [sum_eq_single d]
    · simp only [hedge,ite_true]
    · intro e he hed
      have hn : ¬((y.val:ℤ)+1=(x.val:ℤ)+1+(h:ℤ)*e) := by
        intro heq
        have hcast : (h:ℤ)≠0 := by exact_mod_cast ne_of_gt hh
        have hm : (h:ℤ)*e=(h:ℤ)*d := by linarith
        have heq' : (e:ℤ)=d := mul_left_cancel₀ hcast hm
        exact hed (by exact_mod_cast heq')
      simp only [hn,ite_false]
    · exact fun h => False.elim (h hd)
  · rfl

lemma sourceBlockMatrix_zero_of_no_edge (D : S.DivisorFamily B τ C₀) (h L : ℕ)
    (cut : S.Cutoffs T) (a : ℕ → ℂ) (D₀ k : ℕ) (x y : Fin D₀)
    (hedge : ∀ d∈D.members,¬((y.val:ℤ)+1=(x.val:ℤ)+1+(h:ℤ)*d)) :
    sourceBlockMatrix D h L cut a D₀ k x y=0 := by
  unfold sourceBlockMatrix
  dsimp only
  split_ifs
  · exact sum_eq_zero (fun d hd => ite_eq_right (hedge d hd))
  · rfl

theorem sourceBlockMatrix_norm_moment (D : S.DivisorFamily B τ C₀) (h L : ℕ)
    (cut : S.Cutoffs T) (a : ℕ → ℂ) (D₀ k : ℕ) (hD : 0<D₀) :
    ‖sourceBlockMatrix D h L cut a D₀ k‖^(sourceLength B) ≤
      (((sourceBlockMatrix D h L cut a D₀ k).conjTranspose*
        sourceBlockMatrix D h L cut a D₀ k)^⌊B⌋₊).trace.re := by
  let : Nonempty (Fin D₀) := ⟨⟨0,hD⟩⟩
  exact norm_pow_le_gram_trace (sourceBlockMatrix D h L cut a D₀ k) ⌊B⌋₊

end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
