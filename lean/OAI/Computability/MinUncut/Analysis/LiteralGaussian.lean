import Mathlib
import OAI.Computability.MinUncut.Graphs.HonestRows
import OAI.Computability.MinUncut.Analysis.GaussianPacking
import OAI.Computability.MinUncut.Estimates.AlgebraicSigns

namespace OAI

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace MinUncut.FiniteGaussian
open GaussianBudget MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}

abbrev TestCoordinates (m n : ℕ) := Coordinates (Point m n) (Code m n)
abbrev ScoreIndex (m n : ℕ) := Bool × Code m n

def scoreFamily (σ η : ℝ) (s : ScoreIndex m n) : TestCoordinates m n → ℝ :=
  liftVector (codeVector s.2) (if s.1 then σ else 0) (if s.1 then η else 0) s.2

lemma scoreFamily_variance (hn : 0<n) (σ η : ℝ) (s : ScoreIndex m n) :
    1 ≤ ‖vector (scoreFamily σ η s)‖^2 := by
  have h := liftVector_norm_pos (codeVector s.2) (codeVector_norm hn s.2)
    (if s.1 then σ else 0) (if s.1 then η else 0) s.2
  change 1 ≤ ‖vector (liftVector (codeVector s.2) _ _ s.2)‖^2
  nlinarith

lemma codeVector_abs_le (hn : 0<n) (z : Code m n) (x : Point m n) : |codeVector z x| ≤ 1 := by
  have hN : (1:ℝ) ≤ (n^m:ℕ) := by exact_mod_cast (Nat.one_le_pow m n hn)
  have hs : 1 ≤ Real.sqrt (n^m:ℕ) := (Real.one_le_sqrt).mpr hN
  simp only [codeVector,abs_mul,BinaryFourier.sign_abs,mul_one,abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact inv_le_one_of_one_le₀ hs

lemma liftVector_l1 {X C : Type*} [Fintype X] [Fintype C]
    (v : X → ℝ) (σ η : ℝ) (z : C) :
    (∑ i, |liftVector v σ η z i|)=(1+|σ|)*(∑ x, |v x|)+|η| := by
  simp only [Fintype.sum_sum_type,liftVector,abs_mul,← Finset.mul_sum]
  simp only [apply_ite abs,abs_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  ring

lemma scoreFamily_l1 (hn : 0<n) {σ η : ℝ} (hσ : 0≤σ) (hσ1 : σ≤1)
    (hη : 0≤η) (hη1 : η≤1) (s : ScoreIndex m n) :
    (∑ i, |scoreFamily σ η s i|) ≤ 2*(n^m:ℕ)+1 := by
  have hh : (∑ x, |codeVector s.2 x|) ≤ (n^m:ℕ) := by
    calc
      _ ≤ ∑ _ : Point m n, (1:ℝ) := Finset.sum_le_sum (fun x _ => codeVector_abs_le hn s.2 x)
      _ = _ := by simp [Point]
  have hh0 : 0 ≤ ∑ x, |codeVector s.2 x| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  unfold scoreFamily
  rw [liftVector_l1]
  cases s.1 <;> simp only [Bool.false_eq_true,ite_false,ite_true,abs_zero,abs_of_nonneg hσ,abs_of_nonneg hη]
  · linarith
  · nlinarith [mul_le_mul_of_nonneg_right hσ1 hh0]

lemma scoreFamily_packed (σ η : ℝ) (s : ScoreIndex m n)
    (p : (Point m n → ℝ) × ((Point m n → ℝ) × (Code m n → ℝ))) :
    thresholdTable (scoreFamily σ η) (packEquiv p) s=
      if s.1 then query (p.1+σ • p.2.1) (η • p.2.2) s.2 else query p.1 0 s.2 := by
  unfold thresholdTable scoreFamily
  rw [score_packed]
  simp only [score_codeVector,query,thresholdBit]
  cases s.1
  · simp
  · simp only [ite_true,Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_mul,Finset.sum_add_distrib,
      mul_assoc,← Finset.mul_sum]
    congr 1
    ring_nf

def qSign (b : F₂) : ℚ := if b=0 then 1 else -1

lemma qSign_cast (b : F₂) : (qSign b:ℝ)=BinaryFourier.sign b := by
  unfold qSign BinaryFourier.sign
  split_ifs <;> norm_num

def rationalScoreTable (σ η : ℚ) (x : TestCoordinates m n → ℚ) (s : ScoreIndex m n) : Bool :=
  algebraicNonneg (∑ i, (x (.inl i)+(if s.1 then σ else 0)*x (.inr (.inl i)))*qSign (s.2.val i))
    ((if s.1 then η else 0)*x (.inr (.inr s.2))) (n^m)

lemma rationalScoreTable_correct (hn : 0<n) (σ η : ℚ) (x : TestCoordinates m n → ℚ) :
    rationalScoreTable σ η x=thresholdTable (scoreFamily (σ:ℝ) (η:ℝ)) (fun i => (x i:ℝ)) := by
  funext s
  apply Bool.eq_iff_iff.mpr
  rw [rationalScoreTable,algebraicNonneg_eq]
  simp only [thresholdTable,thresholdBit,ite_eq_left_iff,Bool.false_eq_true,imp_false,not_not]
  have hroot : 0 < Real.sqrt (n^m:ℕ) := Real.sqrt_pos.mpr (by positivity)
  have he : score (scoreFamily (σ:ℝ) (η:ℝ) s) (fun i => (x i:ℝ))=
      (Real.sqrt (n^m:ℕ))⁻¹ *
        (∑ i, ((x (.inl i):ℝ)+(if s.1 then (σ:ℝ) else 0)*(x (.inr (.inl i)):ℝ))*BinaryFourier.sign (s.2.val i))+
        (if s.1 then (η:ℝ) else 0)*(x (.inr (.inr s.2)):ℝ) := by
    cases hs : s.1 <;>
      simp only [score,scoreFamily,liftVector,codeVector,Fintype.sum_sum_type,hs,
        Bool.false_eq_true,ite_false,ite_true,zero_mul,add_zero,
        ite_mul,Finset.sum_ite_eq',Finset.mem_univ,Finset.sum_const_zero]
    · simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    · simp only [add_mul,mul_add,Finset.sum_add_distrib,Finset.mul_sum,← add_assoc]
      congr 2 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
  rw [he]
  simp only [Rat.cast_add,Rat.cast_sum,Rat.cast_mul,apply_ite Rat.cast,Rat.cast_zero,qSign_cast]
  have he' (a b : ℝ) : Real.sqrt (n^m:ℕ)*((Real.sqrt (n^m:ℕ))⁻¹*a+b)=a+b*Real.sqrt (n^m:ℕ) := by
    rw [mul_add,← mul_assoc,mul_inv_cancel₀ hroot.ne',one_mul,mul_comm (Real.sqrt (n^m:ℕ)) b]
  rw [← he',mul_nonneg_iff_of_pos_left hroot]

end MinUncut.FiniteGaussian

end
end

end OAI
