import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PhaseEqOneIffInteger

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

namespace OrdinaryAdditiveBilinear
open Finset

lemma rational_phase_of_modEq {l p q : ℕ} (hl : 0<l) (a : ℤ)
    (hpq : p≡q [MOD l]) : phase ((a:ℝ)/l*((p:ℝ)-q))=1 := by
  obtain ⟨k,hk⟩ := hpq.symm.dvd
  have hkr : (p:ℝ)-q=(l:ℝ)*k := by exact_mod_cast hk
  rw [hkr]
  apply (phase_eq_one_iff_integer _).mpr
  refine ⟨a*k,?_⟩
  have hlr : (l:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hl)
  push_cast
  field_simp

theorem progression_frequency_no_gap (P : Finset ℕ) {l r : ℕ} (hl : 0<l)
    (hres : ∀p∈P,p≡r [MOD l]) (hpq : ∃p∈P,∃q∈P,p≠q)
    (a : ℤ) {κ : ℝ} (hκ : 0<κ) :
    ¬(∀p∈P,∀q∈P,p≠q → κ≤‖1-phase ((a:ℝ)/l*((p:ℝ)-q))‖) := by
  intro h
  obtain ⟨p,hp,q,hq,hne⟩ := hpq
  have hh := h p hp q hq hne
  rw [rational_phase_of_modEq hl a ((hres p hp).trans (hres q hq).symm),
    sub_self,norm_zero] at hh
  exact (not_le_of_gt hκ) hh

end OrdinaryAdditiveBilinear

end

end OAI
