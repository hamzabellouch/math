import OAI.Analysis.IrrationalRotation.Model.ConjugationDefect
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Topology.Order.LiminfLimsup

namespace OAI

noncomputable section
namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

@[simp] theorem IsConjugation.toHilbertConjugation_apply {C : H → H}
    (hC : IsConjugation C) (x : H) : hC.toHilbertConjugation.val x = C x := rfl

theorem HilbertConjugation.isConjugation (C : HilbertConjugation H) :
    IsConjugation C.val := by
  exact ⟨C.property, C.val.map_add, C.val.map_smul', C.val.norm_map⟩

namespace HilbertConjugation

@[simp] theorem conjugate_apply (C : HilbertConjugation H) (T : H →L[ℂ] H) (x : H) :
    C.conjugate T x = C.val (T (C.val x)) := rfl

@[simp] theorem apply_apply (C : HilbertConjugation H) (x : H) :
    C.val (C.val x) = x := C.property x

@[simp] theorem conjugate_one (C : HilbertConjugation H) :
    C.conjugate (1 : H →L[ℂ] H) = 1 := by
  ext x
  simp

@[simp] theorem conjugate_add (C : HilbertConjugation H) (A B : H →L[ℂ] H) :
    C.conjugate (A + B) = C.conjugate A + C.conjugate B := by
  ext x
  simp

@[simp] theorem conjugate_mul (C : HilbertConjugation H) (A B : H →L[ℂ] H) :
    C.conjugate (A * B) = C.conjugate A * C.conjugate B := by
  ext x
  simp

@[simp] theorem conjugate_pow (C : HilbertConjugation H) (A : H →L[ℂ] H) (n : ℕ) :
    C.conjugate (A ^ n) = (C.conjugate A) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

@[simp] theorem conjugate_conjugate (C : HilbertConjugation H) (A : H →L[ℂ] H) :
    C.conjugate (C.conjugate A) = A := by
  ext x
  simp

theorem norm_conjugate_le (C : HilbertConjugation H) (A : H →L[ℂ] H) :
    ‖C.conjugate A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  simpa only [conjugate_apply, LinearIsometryEquiv.norm_map] using A.le_opNorm (C.val x)

@[simp] theorem norm_conjugate (C : HilbertConjugation H) (A : H →L[ℂ] H) :
    ‖C.conjugate A‖ = ‖A‖ := by
  apply le_antisymm (C.norm_conjugate_le A)
  simpa only [conjugate_conjugate] using C.norm_conjugate_le (C.conjugate A)

theorem normQuasinilpotent_conjugate (C : HilbertConjugation H) {A : H →L[ℂ] H}
    (hA : NormQuasinilpotent A) : NormQuasinilpotent (C.conjugate A) := by
  simpa only [NormQuasinilpotent, ← conjugate_pow, norm_conjugate] using hA

end HilbertConjugation

theorem isInfiniteConjugationIsometry_iff_limsup [CompleteSpace H]
    (C : HilbertConjugation H) (T : H →L[ℂ] H) :
    IsInfiniteConjugationIsometry C T ↔
      Filter.limsup (fun m : ℕ => ENNReal.ofReal
        (‖conjugationDefect C T m‖ ^ (1 / (m : ℝ)))) Filter.atTop = 0 := by
  constructor
  · intro h
    have h' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp h
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using h'.limsup_eq
  · intro h
    have h' : Filter.Tendsto (fun m : ℕ => ENNReal.ofReal
        (‖conjugationDefect C T m‖ ^ (1 / (m : ℝ)))) Filter.atTop (nhds 0) :=
      tendsto_of_le_liminf_of_limsup_le bot_le h.le
    have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h'
    simpa only [IsInfiniteConjugationIsometry, Function.comp_def, ENNReal.toReal_zero,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)] using hreal

end Invariant233

end

end OAI
