import OAI.Analysis.FreeEntropy.CumulantBound

namespace OAI

noncomputable section
namespace FiniteEntropySeparation
open Finset FreeSeries

section Product
variable {α A : Type} [DecidableEq α] [Monoid A]
def optionTuple (B : α → A) (Y : A) : Option α → A
  | none => Y
  | some i => B i
 theorem option_word_product (B : α → A) (Y : A) (h : ∀ i, Commute Y (B i)) (w : List (Option α)) :
    (w.map (optionTuple B Y)).prod = ((w.filterMap id).map B).prod * Y^(w.count none) := by
  induction w with
  | nil => simp
  | cons a w ih =>
    cases a with
    | none =>
      simp only [List.map_cons, List.prod_cons, optionTuple, List.filterMap_cons, id_eq, ih]
      have hc := Commute.list_prod_right ((w.filterMap id).map B) Y (by
        intro x hx
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
        exact h i)
      simp only [List.count_cons_self]
      change Y * (((w.filterMap id).map B).prod * Y ^ w.count none) = _
      rw [← mul_assoc, hc.eq, mul_assoc, pow_succ']
      rfl
    | some i => simp [optionTuple, ih, mul_assoc]
end Product

section TraceNorm
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
 theorem norm_trace_le_opNorm {M : VonNeumannAlgebra H} (τ : TracialVector M) (A : H →L[ℂ] H) :
    ‖trace τ A‖ ≤ ‖A‖ := by
  apply (norm_inner_le_norm _ _).trans
  simpa only [τ.norm_vacuum, one_mul, mul_one] using A.le_opNorm τ.vacuum
end TraceNorm

namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]
def signalMoments : Series (Fin (p+1)) := wordMoment (τ p) (C p)
 theorem signal_option_product (w : List (Option (Fin p))) :
    wordEval (C p) (w.map (optionFin p)) =
      ((w.filterMap id).map (semicircularB (N := Fin ((p+1)+(p+1))) (G := Multiplicative (ZMod p)))).prod *
        equidiscreteSignal p ^ (w.count none) := by
  unfold wordEval
  rw [List.map_map]
  have hf : (fun a => C p (optionFin p a)) = optionTuple semicircularB (equidiscreteSignal p) := by
    funext a
    cases a <;> simp [optionTuple]
  change (w.map (fun a => C p (optionFin p a))).prod = _
  rw [hf]
  exact option_word_product _ _ (equidiscreteSignal_commutes_B p) w
 theorem signal_option_moments (w : List (Option (Fin p))) :
    signalMoments p (w.map (optionFin p)) = fockMoments p (w.filterMap id) *
      trace (τ p) (equidiscreteSignal p ^ (w.count none)) := by
  unfold signalMoments wordMoment
  rw [signal_option_product, tensor_equidiscrete_moment, equidiscreteSignal_moments]
  rfl
 theorem signal_option_coeff_norm_le (hp : 2 ≤ p) (w : List (Option (Fin p))) :
    ‖signalMoments p (w.map (optionFin p))‖ ≤ ‖ignoreLetter (fockMoments p) w‖ := by
  rw [signal_option_moments, norm_mul]
  change _ ≤ ‖fockMoments p (w.filterMap id)‖
  let : Nontrivial (H p) := ⟨⟨basis empty, 0, by
    intro h
    have he := congrArg (fun f : H p => f empty) h
    simp [basis, lp.single_apply] at he⟩⟩
  have hy : ‖trace (τ p) (equidiscreteSignal p ^ (w.count none))‖ ≤ 1 := by
    apply (norm_trace_le_opNorm _ _).trans
    apply (norm_pow_le _ _).trans
    exact (pow_le_pow_left₀ (norm_nonneg _) (equidiscreteSignal_norm_le p hp) _).trans_eq (one_pow _)
  exact (mul_le_mul_of_nonneg_left hy (norm_nonneg _)).trans_eq (mul_one _)
 theorem signalMoments_norm_le (hp : 2 ≤ p) (n : ℕ) :
    degreeNorm (signalMoments p) n ≤ (4*Real.sqrt (Real.sqrt p))^n := by
  rw [← degreeNorm_equiv (optionFin p) (signalMoments p) n]
  apply (degreeNorm_le_of_coeff (fun w _ => signal_option_coeff_norm_le p hp w)).trans
  apply (ignoreLetter_norm_le (by positivity) (fockMoments_norm_le (by omega)) n).trans
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hq1 : (1:ℝ) ≤ Real.sqrt (Real.sqrt p) := by
    exact Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr hp1)
  exact pow_le_pow_left₀ (by positivity) (by linarith) _
 theorem signalCumulants_norm_le (hp : 2 ≤ p) (n : ℕ) :
    degreeNorm (cumulants (signalMoments p)) n ≤ (128*Real.sqrt (Real.sqrt p))^n := by
  have hM : signalMoments p [] = 1 := by simp [signalMoments]
  have hA : 0 < 4*Real.sqrt (Real.sqrt (p:ℝ)) := by
    have hp' : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    positivity
  have hh := cumulants_norm_le hM hA (fun m _ => signalMoments_norm_le p hp m) n
  norm_num [← mul_assoc] at hh
  exact hh
end Model
end FiniteEntropySeparation

end

end OAI
