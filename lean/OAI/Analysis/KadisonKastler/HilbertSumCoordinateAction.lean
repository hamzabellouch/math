import OAI.Analysis.KadisonKastler.HilbertSumFieldAction

namespace OAI

/-! # Pointwise actions after a Hilbert-sum coordinate change -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {C H : Type*} [CStarAlgebra C]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {X K : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  [∀ n, NormedAddCommGroup (K n)] [∀ n, InnerProductSpace ℂ (K n)]
  [∀ n, CompleteSpace (K n)] (μ : ∀ n, Measure (X n))

local notation "L" => fun n => Lp (K n) 2 (μ n)

theorem conjugated_hilbertSum_action
    (U : H ≃ₗᵢ[ℂ] lp L 2) (σ : C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (R : C → ∀ n, X n → K n →L[ℂ] K n)
    (hR : ∀ a (v : H) n, U (σ a v) n =ᵐ[μ n] fun x => R a n x (U v n x))
    (a : C) (f : lp L 2) (n : ℕ) :
    (U.conjStarAlgEquiv.toStarAlgHom.comp σ) a f n =ᵐ[μ n]
      fun x => R a n x (f n x) := by
  change U (σ a (U.symm f)) n =ᵐ[μ n] fun x => R a n x (f n x)
  exact (hR a (U.symm f) n).mono fun x hx => hx.trans
    (congrArg (fun g : lp L 2 => R a n x (g n x)) (U.apply_symm_apply f))

end

end KadisonKastler

end OAI
