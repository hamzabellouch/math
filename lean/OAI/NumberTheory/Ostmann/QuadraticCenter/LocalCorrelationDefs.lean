import OAI.NumberTheory.Ostmann.QuadraticCenter.LocalCorrelationPhase

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators ComplexConjugate

def normalizedCoefficient {q : ℕ} [NeZero q] (F : ZMod q → ℂ) (h : ZMod q) : ℂ :=
  ZMod.dft F h / (q : ℂ)

def transformCorrelation {d e q : ℕ} [NeZero d] [NeZero e] [NeZero q]
    (hdq : d ∣ q) (heq : e ∣ q) (f : ZMod d → ℂ) (g : ZMod e → ℂ)
    (s : ZMod q) : ℂ :=
  Supply.unitaryDFT f (ZMod.castHom hdq (ZMod d) s) *
    conj (Supply.unitaryDFT g (ZMod.castHom heq (ZMod e) s))

theorem unitaryDFT_restrict_expansion {d q : ℕ} [NeZero d] [NeZero q]
    (hdq : d ∣ q) (f : ZMod d → ℂ) (s : ZMod q) :
    Supply.unitaryDFT f (ZMod.castHom hdq (ZMod d) s) =
      (∑ x : ZMod d, f x * ZMod.stdAddChar (-(frequencyEmbedding (q := q) x * s))) /
        (Real.sqrt d : ℂ) := by
  unfold Supply.unitaryDFT
  rw [ZMod.dft_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  have hp := congrArg conj (stdAddChar_restrict_eq_lift hdq x s)
  simp only [Supply.conj_stdAddChar] at hp
  simp only [smul_eq_mul]
  rw [hp]
  ring

end Ostmann.QuadraticCenter

end

end OAI
