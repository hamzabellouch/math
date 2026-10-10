import OAI.Analysis.KadisonKastler.RationalCoreExtension
import OAI.Analysis.KadisonKastler.HilbertCoefficientMeasurable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! # Measurable operator fields from a countable vector core

Pointwise bounded rational-linear maps commuting with multiplication by
`i` extend to complex-linear operators. Countability gives simultaneous
identities off one null set; dense coefficient tests give measurability.
-/

namespace KadisonKastler

open MeasureTheory Filter TopologicalSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance vectorCoreNormedSpace : NormedSpace ℚ H := NormedSpace.restrictScalars ℚ ℂ H

structure CoherentVectorCore (C : RationalComplexCore H) (B : ℝ) (g : C.space → H) : Prop where
  add : ∀ x y, g (x + y) = g x + g y
  rat : ∀ (r : ℚ) x, g (r • x) = r • g x
  mulI : ∀ x, g (C.mulI x) = Complex.I • g x
  bound : ∀ x, ‖g x‖ ≤ B * ‖(x : H)‖

namespace CoherentVectorCore

variable {C : RationalComplexCore H} {B : ℝ} {g : C.space → H}

def linearMap (h : CoherentVectorCore C B g) : C.space →ₗ[ℚ] H where
  toFun := g
  map_add' := h.add
  map_smul' := h.rat

def operator (h : CoherentVectorCore C B g) : H →L[ℂ] H :=
  C.extendComplex h.linearMap h.bound h.mulI

theorem operator_coe (h : CoherentVectorCore C B g) (x : C.space) :
    h.operator (x : H) = g x := C.extendComplex_coe _ _ _ x

theorem norm_operator_le (h : CoherentVectorCore C B g) (hB : 0 ≤ B) :
    ‖h.operator‖ ≤ B :=
  ContinuousLinearMap.opNorm_le_bound _ hB (C.norm_extendComplex_le _ h.bound h.mulI)

end CoherentVectorCore

variable (C : RationalComplexCore H) (B : ℝ) (g : C.space → ℝ → H)

omit [CompleteSpace H] in
theorem coherentVectorCore_ae
    (ha : ∀ x y, (fun t => g (x + y) t) =ᵐ[volume] fun t => g x t + g y t)
    (hr : ∀ (r : ℚ) x, (fun t => g (r • x) t) =ᵐ[volume] fun t => r • g x t)
    (hi : ∀ x, (fun t => g (C.mulI x) t) =ᵐ[volume] fun t => Complex.I • g x t)
    (hb : ∀ x, ∀ᵐ t : ℝ, ‖g x t‖ ≤ B * ‖(x : H)‖) :
    ∀ᵐ t : ℝ, CoherentVectorCore C B (fun x => g x t) := by
  let : Countable C.space := C.countable
  have h1 := ae_all_iff.mpr (fun x => ae_all_iff.mpr (ha x))
  have h2 := ae_all_iff.mpr (fun r => ae_all_iff.mpr (hr r))
  have h3 := ae_all_iff.mpr hi
  have h4 := ae_all_iff.mpr hb
  filter_upwards [h1, h2, h3, h4] with t h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-- A bounded operator field agreeing with the supplied core vectors.
The bad set is assigned the zero operator. -/
theorem exists_field_of_vectorCore [SeparableSpace H] (hB : 0 ≤ B)
    (hm : ∀ x, AEStronglyMeasurable (g x) volume)
    (hc : ∀ᵐ t : ℝ, CoherentVectorCore C B (fun x => g x t)) :
    ∃ F : ℝ → H →L[ℂ] H,
      (∀ ξ, AEStronglyMeasurable (fun t => F t ξ) volume) ∧
      (∀ t, ‖F t‖ ≤ B) ∧ ∀ x : C.space, (fun t => F t (x : H)) =ᵐ[volume] g x := by
  classical
  let F : ℝ → H →L[ℂ] H := fun t =>
    if ht : CoherentVectorCore C B (fun x => g x t) then ht.operator else 0
  have he (x : C.space) : (fun t => F t (x : H)) =ᵐ[volume] g x := by
    filter_upwards [hc] with t ht
    dsimp [F]
    rw [dite_eq_left ht]
    exact ht.operator_coe x
  have hFn (t : ℝ) : ‖F t‖ ≤ B := by
    dsimp [F]
    split_ifs with ht
    · exact ht.norm_operator_le hB
    · simpa only [norm_zero] using hB
  refine ⟨F, ?_, hFn, he⟩
  let : Countable C.space := C.countable
  have hmcoeff (η ξ : C.space) :
      AEStronglyMeasurable (fun t => inner ℂ (η : H) (F t (ξ : H))) volume := by
    exact ((hm ξ).const_inner (c := (η : H))).congr
      ((he ξ).mono fun t ht => congrArg (fun x : H => inner ℂ (η : H) x) ht.symm)
  exact fun ξ => (operator_field_aestronglyMeasurable_of_dense_coefficients
    ((↑) : C.space → H) C.dense.denseRange_val F hmcoeff ξ).1

end

end KadisonKastler

end OAI
