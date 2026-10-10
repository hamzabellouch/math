import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PhaseNatMul

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

lemma phase_eq_one_iff_integer (x : ℝ) : phase x=1 ↔ ∃n : ℤ,x=n := by
  constructor
  · intro h
    obtain ⟨n,hn⟩ := Complex.exp_eq_one_iff.mp h
    have hi := congrArg Complex.im hn
    have he : 2*Real.pi*x=(n:ℝ)*(2*Real.pi) := by
      simpa [Complex.mul_im,Complex.mul_re] using hi
    refine ⟨n,?_⟩
    rw [mul_comm (n:ℝ)] at he
    exact mul_left_cancel₀ (mul_ne_zero (by norm_num) Real.pi_ne_zero) he
  · rintro ⟨n,rfl⟩
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨n,?_⟩
    push_cast
    ring

lemma irrational_prime_phase_ne_one {α : ℝ} (hα : Irrational α)
    {p q : ℕ} (hne : p≠q) : phase (α*((p:ℝ)-q))≠1 := by
  intro h
  obtain ⟨n,hn⟩ := (phase_eq_one_iff_integer _).mp h
  have hpq : (p:ℝ)≠q := by exact_mod_cast hne
  apply hα.ne_rational n ((p:ℤ)-(q:ℤ))
  push_cast
  exact (eq_div_iff (sub_ne_zero.mpr hpq)).mpr hn

lemma finite_positive_lower_bound {ι : Type*} (S : Finset ι) (g : ι → ℝ)
    (hg : ∀i∈S,0<g i) : ∃κ : ℝ,0<κ ∧ ∀i∈S,κ≤g i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨κ,hκ,hbound⟩ := ih (fun i hi => hg i (mem_insert_of_mem hi))
    refine ⟨min (g a) κ,lt_min (hg a (mem_insert_self ..)) hκ,?_⟩
    intro i hi
    rcases mem_insert.mp hi with rfl|hi
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hbound i hi)

theorem irrational_finite_prime_gap (P : Finset ℕ) {α : ℝ} (hα : Irrational α) :
    ∃κ : ℝ,0<κ ∧ ∀p∈P,∀q∈P,p≠q → κ≤‖1-phase (α*((p:ℝ)-q))‖ := by
  let S := (P×ˢP).filter (fun x : ℕ×ℕ => x.1≠x.2)
  let g := fun x : ℕ×ℕ => ‖1-phase (α*((x.1:ℝ)-x.2))‖
  have hg : ∀i∈S,0<g i := by
    intro i hi
    apply norm_pos_iff.mpr
    exact sub_ne_zero.mpr (Ne.symm (irrational_prime_phase_ne_one hα (mem_filter.mp hi).2))
  obtain ⟨κ,hκ,hbound⟩ := finite_positive_lower_bound S g hg
  refine ⟨κ,hκ,?_⟩
  intro p hp q hq hne
  exact hbound (p,q) (mem_filter.mpr ⟨mem_product.mpr ⟨hp,hq⟩,hne⟩)

end OrdinaryAdditiveBilinear

end

end OAI
