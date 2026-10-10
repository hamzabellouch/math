import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightExprBound
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySymbolicStep

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicStep
open Characters.RationalHistory
variable {ι : Type*}

theorem product_realEval (es : List (Expr ι)) (x : ι → ℝ) :
    (product es).realEval x = (es.map (fun e => e.realEval x)).prod := by
  induction es with
  | nil => simp [product,Expr.realEval]
  | cons e es ih => simp [product,Expr.realEval,ih]

theorem product_relativeControl (es : List (Expr ι)) (x : ι → ℝ) (K : ℝ)
    (h : ∀ e ∈ es, e.RelativeControl x K) : (product es).RelativeControl x K := by
  induction es with
  | nil => norm_num [product,Expr.RelativeControl]
  | cons e es ih => exact ⟨h e (by simp),ih (fun z hz => h z (by simp [hz]))⟩

theorem product_logSize (es : List (Expr ι)) :
    (product es).logSize = (es.map Expr.logSize).sum := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [product,Expr.logSize,ih]

theorem product_cancellationDepth_le (es : List (Expr ι)) (d : ℕ)
    (h : ∀ e ∈ es, e.cancellationDepth ≤ d) : (product es).cancellationDepth ≤ d := by
  induction es with
  | nil => exact Nat.zero_le d
  | cons e es ih => exact max_le (h e (by simp)) (ih (fun z hz => h z (by simp [hz])))

theorem pivot_realEval (s v w : ℤ) (plus minus : Expr ι) (u hp hm : List (Expr ι))
    (x : ι → ℝ) :
    (pivot s v w plus minus u hp hm).realEval x =
      ((v:ℝ)*(minus.realEval x*(product hm).realEval x) -
        (w:ℝ)*(plus.realEval x*(product hp).realEval x)) /
      ((s:ℝ)*(product u).realEval x) := rfl

theorem pivot_relativeControl (s v w : ℤ) (plus minus : Expr ι) (u hp hm : List (Expr ι))
    (x : ι → ℝ) (K : ℝ) (hs : s ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (hplus : plus.RelativeControl x K) (hminus : minus.RelativeControl x K)
    (hu : ∀ e ∈ u, e.RelativeControl x K)
    (hhp : ∀ e ∈ hp, e.RelativeControl x K) (hhm : ∀ e ∈ hm, e.RelativeControl x K)
    (hn : (v:ℝ)*(minus.realEval x*(product hm).realEval x) -
      (w:ℝ)*(plus.realEval x*(product hp).realEval x) ≠ 0)
    (hl : |((v:ℝ)*(minus.realEval x*(product hm).realEval x)) /
      ((v:ℝ)*(minus.realEval x*(product hm).realEval x) -
        (w:ℝ)*(plus.realEval x*(product hp).realEval x))| ≤ K)
    (hr : |((w:ℝ)*(plus.realEval x*(product hp).realEval x)) /
      ((v:ℝ)*(minus.realEval x*(product hm).realEval x) -
        (w:ℝ)*(plus.realEval x*(product hp).realEval x))| ≤ K) :
    (pivot s v w plus minus u hp hm).RelativeControl x K := by
  have hs' : (s:ℝ) ≠ 0 := by exact_mod_cast hs
  have hv' : (v:ℝ) ≠ 0 := by exact_mod_cast hv
  have hw' : (w:ℝ) ≠ 0 := by exact_mod_cast hw
  exact ⟨⟨⟨hv',hminus,product_relativeControl hm x K hhm⟩,
    ⟨hw',hplus,product_relativeControl hp x K hhp⟩,hn,hl,hr⟩,
    hs',product_relativeControl u x K hu⟩

theorem pivot_logSize (s v w : ℤ) (plus minus : Expr ι) (u hp hm : List (Expr ι)) :
    (pivot s v w plus minus u hp hm).logSize = plus.logSize + minus.logSize +
      (u.map Expr.logSize).sum + (hp.map Expr.logSize).sum + (hm.map Expr.logSize).sum := by
  simp only [pivot,Expr.logSize,product_logSize]
  omega

theorem pivot_cancellationDepth_le (s v w : ℤ) (plus minus : Expr ι)
    (u hp hm : List (Expr ι)) (d : ℕ)
    (hplus : plus.cancellationDepth ≤ d) (hminus : minus.cancellationDepth ≤ d)
    (hu : ∀ e ∈ u, e.cancellationDepth = 0)
    (hhp : ∀ e ∈ hp, e.cancellationDepth = 0)
    (hhm : ∀ e ∈ hm, e.cancellationDepth = 0) :
    (pivot s v w plus minus u hp hm).cancellationDepth ≤ d + 1 := by
  have hu' := product_cancellationDepth_le u 0 (fun e he => (hu e he).le)
  have hhp' := product_cancellationDepth_le hp 0 (fun e he => (hhp e he).le)
  have hhm' := product_cancellationDepth_le hm 0 (fun e he => (hhm e he).le)
  simp only [pivot,Expr.cancellationDepth]
  omega

end Ostmann.Arithmetic.HistorySymbolicStep

end

end OAI
