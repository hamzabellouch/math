import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BoxNonneg

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

namespace OrdinarySharpWindow
open Finset MeasureTheory
lemma sharpWindow_Ioc_add (a : ℕ→ℂ) (u : ℕ→ℝ) (H x : ℝ)
    {X A B : ℕ} (hXA : X ≤ A) (hAB : A ≤ B) :
    sharpWindow (Ioc X A) a u H x+sharpWindow (Ioc A B) a u H x =
      sharpWindow (Ioc X B) a u H x := by
  unfold sharpWindow
  rw [← sum_union (Ioc_disjoint_Ioc_of_le (le_refl A)), Finset.Ioc_union_Ioc_eq_Ioc hXA hAB]

lemma sharpWindow_Ioc_l1 (a : ℕ→ℂ) (u : ℕ→ℝ) (H : ℝ)
    {X A B : ℕ} (hXA : X ≤ A) (hAB : A ≤ B) :
    (∫x : ℝ,‖sharpWindow (Ioc A B) a u H x‖) ≤
      (∫x : ℝ,‖sharpWindow (Ioc X A) a u H x‖)+
      (∫x : ℝ,‖sharpWindow (Ioc X B) a u H x‖) := by
  rw [← integral_add (sharpWindow_integrable (Ioc X A) a u H).norm
    (sharpWindow_integrable (Ioc X B) a u H).norm]
  apply integral_mono (sharpWindow_integrable (Ioc A B) a u H).norm
    ((sharpWindow_integrable (Ioc X A) a u H).norm.add
      (sharpWindow_integrable (Ioc X B) a u H).norm)
  intro x
  have he := sharpWindow_Ioc_add a u H x hXA hAB
  have hh := norm_sub_le (sharpWindow (Ioc X B) a u H x) (sharpWindow (Ioc X A) a u H x)
  have he' : sharpWindow (Ioc X B) a u H x-sharpWindow (Ioc X A) a u H x =
      sharpWindow (Ioc A B) a u H x := by rw [← he,add_sub_cancel_left]
  rw [he'] at hh
  simpa only [add_comm,Pi.add_apply] using hh
end OrdinarySharpWindow

end

end OAI
