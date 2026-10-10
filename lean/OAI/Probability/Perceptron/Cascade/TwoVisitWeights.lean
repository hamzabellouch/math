import Mathlib
import OAI.Probability.Perceptron.Variational.StepEntropy
import OAI.Probability.Perceptron.Variational.AtomicPairVisitLaw

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy

def depthMassIncrement : (n : ℕ) → (Fin n→ℝ) → ℝ → Fin (n+1) → ℝ
  | 0,_,a,_ => 1-a
  | n+1,z,a,d => Fin.cases (z 0-a) (fun i => depthMassIncrement n (fun j => z j.succ) (z 0) i) d

lemma depthMassIncrement_nonneg (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z)
    (hz1 : ∀ i,z i<1) (a : ℝ) (ha : a<1) (haz : ∀ i,a<z i) (d : Fin (n+1)) :
    0≤depthMassIncrement n z a d := by
  induction n generalizing a with
  | zero => exact sub_nonneg.mpr ha.le
  | succ n ih =>
    induction d using Fin.cases with
    | zero => exact sub_nonneg.mpr (haz 0).le
    | succ d =>
      exact ih _ (fun i j hij => hz (Fin.succ_lt_succ_iff.mpr hij))
        (fun i => hz1 i.succ) (z 0) (hz1 0) (fun i => hz (Fin.succ_pos i)) d

lemma twoDecoratedVisit_likelihood (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z)
    (hz1 : ∀ i,z i<1) (a : ℝ) (ha : a<1) (haz : ∀ i,a<z i) (d : Fin (n+1)) :
    cascadeShapeLikelihood n z a ((twoDecoratedVisit (X:=Unit) (fun _ => 1) (fun _ => 1) n d).bare n)=
      ENNReal.ofReal (depthMassIncrement n z a d/(1-a)) := by
  induction n generalizing a with
  | zero => simp [cascadeShapeLikelihood,depthMassIncrement,(sub_pos.mpr ha).ne']
  | succ n ih =>
    induction d using Fin.cases with
    | zero =>
      simp only [twoDecoratedVisit,Fin.cases_zero,DecoratedVisitShape.bare,cascadeShapeLikelihood,
        List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,oneDecoratedVisit_count,Nat.cast_one,
        oneDecoratedVisit_likelihood _ _ _ (fun i => hz1 i.succ) _ (hz1 0),one_mul]
      have he := stableEppfValue_new (hz1 0) [1] (by simp) (by simpa using sub_pos.mpr ha)
      simp only [List.length_cons,List.length_nil,List.sum_cons,List.sum_nil,add_zero,
        stableEppfValue_singleton_one ha (hz1 0),mul_one] at he
      rw [he]
      simp [depthMassIncrement]
    | succ d =>
      simp only [twoDecoratedVisit,Fin.cases_succ,DecoratedVisitShape.bare,cascadeShapeLikelihood,
        List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,twoDecoratedVisit_count,Nat.cast_ofNat]
      rw [ih _ (fun i j hij => hz (Fin.succ_lt_succ_iff.mpr hij)) (fun i => hz1 i.succ)
        (z 0) (hz1 0) (fun i => hz (Fin.succ_pos i)) d]
      have he := stableEppfValue_join (hz1 0) ([] : List ℝ) (by simpa using sub_pos.mpr ha)
      simp only [List.sum_nil,add_zero,stableEppfValue_singleton_one ha (hz1 0),mul_one] at he
      rw [show (1:ℝ)+1=2 by norm_num] at he
      rw [he,←ENNReal.ofReal_mul (div_nonneg
        (depthMassIncrement_nonneg n _ (fun i j hij => hz (Fin.succ_lt_succ_iff.mpr hij))
          (fun i => hz1 i.succ) (z 0) (hz1 0) (fun i => hz (Fin.succ_pos i)) d)
        (sub_pos.mpr (hz1 0)).le)]
      congr 1
      change _=depthMassIncrement n (fun i => z i.succ) (z 0) d/(1-a)
      field_simp [(sub_pos.mpr (hz1 0)).ne']

lemma depthMassIncrement_eq (n : ℕ) (z : Fin n→ℝ) (a : ℝ) (d : Fin (n+1)) :
    depthMassIncrement n z a d=(Fin.snoc z 1 : Fin (n+1) → ℝ) d-(Fin.cons a z : Fin (n+1) → ℝ) d := by
  induction n generalizing a with
  | zero => simp [depthMassIncrement,Fin.snoc_zero,Fin.cons_zero,Fin.eq_zero d]
  | succ n ih =>
    induction d using Fin.cases with
    | zero => simp [depthMassIncrement]
    | succ d =>
      change depthMassIncrement n (fun i => z i.succ) (z 0) d=_
      rw [ih,Fin.cons_succ]
      have h1 : (Fin.cons (z 0) (fun i => z i.succ) : Fin (n+1) → ℝ) d=z d := congrFun (Fin.cons_self_tail z) d
      rw [h1]
      congr 1
      induction d using Fin.lastCases with
      | last => simp
      | cast d => simp only [Fin.succ_castSucc,Fin.snoc_castSucc]

lemma depthMassIncrement_stepCumulative {n : ℕ} (w : Fin (n+1)→ℝ) (hw1 : ∑ i,w i=1)
    (d : Fin (n+1)) : depthMassIncrement n (stepCumulative w) 0 d=w d := by
  rw [depthMassIncrement_eq]
  have hu : (Fin.snoc (stepCumulative w) 1 : Fin (n+1) → ℝ) d=∑ i,if i≤d then w i else 0 := by
    induction d using Fin.lastCases with
    | last => simpa only [Fin.snoc_last,Fin.le_last,ite_true] using hw1.symm
    | cast d => simp only [Fin.snoc_castSucc,stepCumulative]
  have hl : (Fin.cons 0 (stepCumulative w) : Fin (n+1) → ℝ) d=∑ i,if i<d then w i else 0 := by
    induction d using Fin.cases with
    | zero => simp
    | succ d =>
      simp only [Fin.cons_succ,stepCumulative]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact propext (by change i.val≤d.val ↔ i.val<d.val+1; omega)
  rw [hu,hl,←Finset.sum_sub_distrib]
  calc
    _ = ∑ i,if i=d then w d else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rcases lt_trichotomy i d with h|rfl|h
      · simp [h,le_of_lt h,ne_of_lt h]
      · simp
      · simp [not_le_of_gt h,not_lt_of_gt h,ne_of_gt h]
    _ = w d := by simp

lemma twoVisitMass_stepCumulative {n : ℕ} (w : Fin (n+1)→ℝ)
    (hw : ∀ i,0<w i) (hw1 : ∑ i,w i=1) (d : Fin (n+1)) :
    (twoVisitMass n (stepCumulative w) d).toReal=w d := by
  rw [twoVisitMass,twoDecoratedVisit_likelihood n _ (stepCumulative_strictMono w hw)
    (stepCumulative_lt_one w hw hw1) 0 (by norm_num) (stepCumulative_pos w hw),
    depthMassIncrement_stepCumulative w hw1]
  simp only [sub_zero,div_one,ENNReal.toReal_ofReal (hw d).le]

end SphericalPerceptronFreeEnergy
end

end OAI
