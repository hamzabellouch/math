import OAI.NumberTheory.JointDickman.Amplification.RootFluctuationMGF
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace OAI

/-! # Finite exponential moments control the expectation of a maximum -/

namespace JointDickman
open Finset
open PublishedInputs

theorem finite_exp_expectation_le {Ω : Type*} [Fintype Ω]
    (w f : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hwone : (∑ x, w x) = 1) :
    Real.exp (finiteExpectation w f) ≤ finiteExpectation w (fun x => Real.exp (f x)) := by
  have h := convexOn_exp.map_sum_le (t := univ) (w := w) (p := f)
    (fun x _ => hw x) hwone (fun _ _ => Set.mem_univ _)
  simpa only [smul_eq_mul,finiteExpectation] using h

noncomputable def finiteFamilyMaximum {J Ω : Type*} [Fintype J] [Nonempty J]
    (X : J → Ω → ℝ) (x : Ω) : ℝ :=
  univ.sup' univ_nonempty (fun j => X j x)

theorem finite_maximum_mgf {J Ω : Type*} [Fintype J] [Nonempty J] [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hwone : (∑ x, w x) = 1)
    (X : J → Ω → ℝ) {t V : ℝ} (ht : 0 < t)
    (hmgf : ∀ j, finiteExpectation w (fun x => Real.exp (t*X j x)) ≤ Real.exp V) :
    finiteExpectation w (finiteFamilyMaximum X) ≤
      (Real.log (Fintype.card J)+V)/t := by
  classical
  have hp (x : Ω) : Real.exp (t*finiteFamilyMaximum X x) ≤
      ∑ j, Real.exp (t*X j x) := by
    obtain ⟨j,hj,he⟩ := exists_mem_eq_sup' univ_nonempty (fun j => X j x)
    change univ.sup' univ_nonempty (fun j => X j x) = _ at he
    rw [show finiteFamilyMaximum X x = X j x from he]
    exact single_le_sum (f := fun j => Real.exp (t*X j x))
      (fun k _ => (Real.exp_pos _).le) hj
  have hupper := (finiteExpectation_mono w hw hp).trans
    (show finiteExpectation w (fun x => ∑ j, Real.exp (t*X j x)) ≤
      (Fintype.card J : ℝ)*Real.exp V from by
      rw [finiteExpectation_sum]
      simpa only [sum_const,card_univ,nsmul_eq_mul] using
        sum_le_sum (fun j (_ : j ∈ (univ : Finset J)) => hmgf j))
  have hjensen := finite_exp_expectation_le w
    (fun x => t*finiteFamilyMaximum X x) hw hwone
  rw [finiteExpectation_const_mul] at hjensen
  have hcard : (0 : ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
  have hexp : (Fintype.card J : ℝ)*Real.exp V =
      Real.exp (Real.log (Fintype.card J)+V) := by
    rw [Real.exp_add,Real.exp_log hcard]
  rw [hexp] at hupper
  have h := Real.exp_le_exp.mp (hjensen.trans hupper)
  apply (le_div_iff₀ ht).mpr
  nlinarith only [h]

end JointDickman

end OAI
