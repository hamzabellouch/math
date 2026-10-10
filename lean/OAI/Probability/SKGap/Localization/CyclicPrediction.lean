import Mathlib
import OAI.Probability.SKGap.Matrix.PolynomialCoeListSum

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
open Diagram InverseDiagram WordSeries
variable {ι : Type*} [Fintype ι]

lemma mean_finset_sum {α : Type*} (s : Finset α) (f : α→ι→ℝ) :
    Diagram.mean (fun i =>∑ a∈s,f a i)=∑ a∈s,Diagram.mean (f a) := by
  simp only [Diagram.mean]
  rw [Finset.sum_comm,Finset.sum_div]

lemma ordinary_mean_noise_rotate (j : ℝ) (F : List (Letter (ι→ℝ))) :
    Diagram.mean (ordinary j (.noise::F))=Diagram.mean (ordinary j (F++[.noise])) := by
  have h1 := funext (expect_at j (id : (ι→ℝ)→ι→ℝ) [] F)
  have h2 := funext (expect_at j (id : (ι→ℝ)→ι→ℝ) F [])
  simp only [ordinary]
  simp only [List.nil_append,List.append_nil,Fintype.sum_empty,zero_add,add_zero] at h1 h2
  rw [h1,h2,mean_finset_sum,mean_finset_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [mean_const_mul,mean_const_mul]
  ring

lemma ordinary_mean_cons_rotate (j : ℝ) (a : Letter (ι→ℝ)) (F : List (Letter (ι→ℝ))) :
    Diagram.mean (ordinary j (a::F))=Diagram.mean (ordinary j (F++[a])) := by
  cases a with
  | noise => exact ordinary_mean_noise_rotate j F
  | diag d => congr 1; funext i; simp [mul_comm]

theorem ordinary_mean_cyclic (j : ℝ) (P Q : List (Letter (ι→ℝ))) :
    Diagram.mean (ordinary j (P++Q))=Diagram.mean (ordinary j (Q++P)) := by
  induction P generalizing Q with
  | nil => simp
  | cons a P ih =>
    rw [List.cons_append,ordinary_mean_cons_rotate,List.append_assoc,ih]
    simp [List.append_assoc]

lemma meanSeries_cyclic (j : ℝ) (a : ι→ℝ) (P Q : List (WordLetter ι)) :
    meanSeries (literalSeries j a (P++Q))=meanSeries (literalSeries j a (Q++P)) := by
  have hi : inverseCount (P++Q)=inverseCount (Q++P) := by simp [inverseCount_append,add_comm]
  ext m
  simp only [coeff_meanSeries]
  by_cases h : inverseCount (P++Q)=0
  · have h' : inverseCount (Q++P)=0 := hi ▸ h
    simp only [literalSeries,h,h',ite_true,PowerSeries.coeff_C]
    by_cases hm : m=0
    · simp only [hm,ite_true]
      simpa only [expandWord,List.flatMap_append] using
        ordinary_mean_cyclic j (expandWord j a [] P) (expandWord j a [] Q)
    · simp [hm,Diagram.mean]
  · have h' : inverseCount (Q++P)≠0 := hi ▸ h
    simp only [literalSeries,h,h',ite_false,PowerSeries.coeff_mk]
    rw [mean_finset_sum,mean_finset_sum]
    apply Finset.sum_congr rfl
    intro bs _
    simpa only [expandWord,List.flatMap_append] using
      ordinary_mean_cyclic j (expandWord j a bs.val P) (expandWord j a bs.val Q)

theorem wordPrediction_mean_cyclic (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (P Q : List (WordLetter ι)) (hI : inverseCount (P++Q)≤1) :
    (∑ i,wordPrediction j a z (P++Q) i)=(∑ i,wordPrediction j a z (Q++P) i) := by
  classical
  by_cases hn : Fintype.card ι=0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hn
    simp
  have hc := meanSeries_cyclic j a P Q
  have hI' : inverseCount (Q++P)≤1 := by simpa only [inverseCount_append,add_comm] using hI
  unfold meanSeries at hc
  simp_rw [literalSeries_eq_wordPredictionPolynomial j a (P++Q) hI,
    literalSeries_eq_wordPredictionPolynomial j a (Q++P) hI'] at hc
  have hmult : (PowerSeries.C ((Fintype.card ι:ℝ)⁻¹))≠0 := by
    exact (map_ne_zero PowerSeries.C).mpr (inv_ne_zero (Nat.cast_ne_zero.mpr hn))
  have hs := mul_left_cancel₀ hmult hc
  have hp : (∑ i,wordPredictionPolynomial j a (P++Q) i)=
      ∑ i,wordPredictionPolynomial j a (Q++P) i := by
    apply Polynomial.coe_injective ℝ
    simpa only [polynomial_coe_finset_sum] using hs
  have he := congrArg (Polynomial.eval z) hp
  simpa only [Polynomial.eval_finsetSum,fun F i => (wordPredictionPolynomial_spec j a F i).2 z] using he
end SKGap.Noncrossing

end
end

end OAI
