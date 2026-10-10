import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.FunProp
import OAI.AlgebraicGeometry.PlaneCurves.Automorphic

namespace OAI

/-!
# Analytic factorization, punctured identities, and holomorphic divisibility
-/

section

/-! Genuine holomorphic division used in the collision argument. No Rouché theorem
or assumption of holomorphic quotients appears in these statements. -/

namespace Nagata.W19

open scoped BigOperators Topology
open Filter Set

/-- The divided slope of an analytic function extends analytically at its center. -/
theorem analyticOnNhd_dslope {U : Set ℂ} {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h U) (a : ℂ) (ha : a ∈ U) :
    AnalyticOnNhd ℂ (dslope h a) U := by
  intro z hz
  by_cases hza : z = a
  · subst z
    obtain ⟨P, hP⟩ := hh a ha
    exact ⟨P.fslope, hP.has_fpower_series_dslope_fslope⟩
  · have hquot : AnalyticAt ℂ (fun w => (h w - h a) / (w - a)) z :=
      ((hh z hz).sub analyticAt_const).div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr hza)
    apply hquot.congr
    filter_upwards [isOpen_ne.mem_nhds hza] with w hw
    simp [dslope_of_ne h hw, slope, div_eq_mul_inv, smul_eq_mul, mul_comm]

/-- Divide out one centered zero while preserving holomorphicity on an open set. -/
theorem exists_analytic_centered_factor
    {U : Set ℂ} (hU : IsOpen U) (h : ℂ → ℂ)
    (hh : AnalyticOnNhd ℂ h U) (a : ℂ) (ha : a ∈ U)
    (k : ℕ) (ho : (k : ℕ∞) ≤ analyticOrderAt h a) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧
      ∀ z, h z = (z - a) ^ k * g z := by
  induction k generalizing h with
  | zero => exact ⟨h, hh, fun z => by simp⟩
  | succ k ih =>
    have hzero : h a = 0 := by
      apply apply_eq_zero_of_analyticOrderAt_ne_zero
      intro hz
      rw [hz] at ho
      simp at ho
    let g := dslope h a
    have hg : AnalyticOnNhd ℂ g U := analyticOnNhd_dslope hh a ha
    have heq : ∀ z, h z = (z - a) * g z := by
      intro z
      simpa [g, hzero, smul_eq_mul] using (sub_smul_dslope h a z).symm
    have hfun : h = (fun z => z - a) * g := funext heq
    have hlin : analyticOrderAt (fun z : ℂ => z - a) a = 1 := by
      simp
    have horder : analyticOrderAt h a = 1 + analyticOrderAt g a := by
      rw [hfun, analyticOrderAt_mul (by fun_prop)
        (hg.differentiableOn.analyticAt (hU.mem_nhds ha)), hlin]
    have hgo : (k : ℕ∞) ≤ analyticOrderAt g a := by
      rw [horder] at ho
      apply (ENat.add_le_add_iff_left (by simp : (1 : ℕ∞) ≠ ⊤)).mp
      simpa [Nat.cast_add, add_comm] using ho
    obtain ⟨G, hG, heG⟩ := ih g hg hgo
    refine ⟨G, hG, fun z => ?_⟩
    rw [heq z, heG z, pow_succ]
    ac_rfl

/-- A factor nonvanishing at a point contributes zero to analytic vanishing order. -/
theorem analytic_order_of_nonvanishing_analytic_factor
    {U : Set ℂ} (hU : IsOpen U) {h g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g U) {a b : ℂ} (hb : b ∈ U)
    (hab : b ≠ a) (k : ℕ) (heq : ∀ z, h z = (z - a) ^ k * g z) :
    analyticOrderAt h b = analyticOrderAt g b := by
  have hfun : h = (fun z => (z - a) ^ k) * g := funext heq
  have hfac : AnalyticAt ℂ (fun z => (z - a) ^ k) b := by fun_prop
  rw [hfun, analyticOrderAt_mul hfac (hg.differentiableOn.analyticAt (hU.mem_nhds hb))]
  have hz : analyticOrderAt (fun z => (z - a) ^ k) b = 0 :=
    hfac.analyticOrderAt_eq_zero.mpr (pow_ne_zero k (sub_ne_zero.mpr hab))
  rw [hz, zero_add]

/-- Simultaneously divide out finitely many distinct centers with prescribed order. -/
theorem exists_analytic_finset_factorization
    {I : Type*} (s : Finset I) {U : Set ℂ} (hU : IsOpen U)
    (h : ℂ → ℂ) (hh : AnalyticOnNhd ℂ h U)
    (ξ : I → ℂ) (hξ : Function.Injective ξ) (hmem : ∀ i ∈ s, ξ i ∈ U)
    (k : ℕ) (ho : ∀ i ∈ s, (k : ℕ∞) ≤ analyticOrderAt h (ξ i)) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧
      ∀ z, h z = (∏ i ∈ s, (z - ξ i) ^ k) * g z := by
  classical
  induction s using Finset.induction_on generalizing h with
  | empty => exact ⟨h, hh, fun z => by simp⟩
  | @insert i s his ih =>
    obtain ⟨g, hg, hfg⟩ := exists_analytic_centered_factor hU h hh (ξ i)
      (hmem i (Finset.mem_insert_self i s)) k (ho i (Finset.mem_insert_self i s))
    have hmems : ∀ j ∈ s, ξ j ∈ U := fun j hj =>
      hmem j (Finset.mem_insert_of_mem hj)
    have hgos : ∀ j ∈ s, (k : ℕ∞) ≤ analyticOrderAt g (ξ j) := by
      intro j hj
      have hji : ξ j ≠ ξ i := hξ.ne (fun e => his (e ▸ hj))
      rw [← analytic_order_of_nonvanishing_analytic_factor hU hg (hmems j hj) hji k hfg]
      exact ho j (Finset.mem_insert_of_mem hj)
    obtain ⟨G, hG, heG⟩ := ih g hg hmems hgos
    refine ⟨G, hG, fun z => ?_⟩
    rw [hfg z, heG z, Finset.prod_insert his, mul_assoc]

/-- Interface consumed by the holomorphic collision estimate. -/
theorem exists_analytic_factorization
    {q : ℕ} {U : Set ℂ} (hU : IsOpen U) (h : ℂ → ℂ)
    (hh : AnalyticOnNhd ℂ h U) (ξ : Fin q → ℂ)
    (hξ : Function.Injective ξ) (hmem : ∀ i, ξ i ∈ U)
    (k : ℕ) (ho : ∀ i, (k : ℕ∞) ≤ analyticOrderAt h (ξ i)) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧
      ∀ z, h z = (∏ i, (z - ξ i) ^ k) * g z := by
  exact exists_analytic_finset_factorization Finset.univ hU h hh ξ hξ
    (fun i _ => hmem i) k (fun i _ => ho i)

end Nagata.W19

end

section

/-! Identity-principle zero-product results on the actual punctured complex
plane. Connectedness and nonemptiness are proved for that precise domain. -/

namespace Nagata.W19

theorem puncturedPlane_nonempty : ({z : ℂ | z ≠ 0} : Set ℂ).Nonempty :=
  ⟨1, one_ne_zero⟩

theorem puncturedPlane_eq_exp_range : {z : ℂ | z ≠ 0} = Set.range Complex.exp := by
  ext z
  constructor
  · intro hz
    exact ⟨Complex.log z, Complex.exp_log hz⟩
  · rintro ⟨w, rfl⟩
    exact Complex.exp_ne_zero w

theorem puncturedPlane_isConnected : IsConnected {z : ℂ | z ≠ 0} := by
  rw [puncturedPlane_eq_exp_range]
  exact isConnected_range Complex.continuous_exp

theorem holomorphic_punctured_mul_zero (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {z : ℂ | z ≠ 0})
    (hg : DifferentiableOn ℂ g {z : ℂ | z ≠ 0})
    (hfg : ∀ z, z ≠ 0 → f z * g z = 0) :
    (∀ z, z ≠ 0 → f z = 0) ∨ (∀ z, z ≠ 0 → g z = 0) := by
  have ho : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne
  exact (hf.analyticOnNhd ho).eq_zero_or_eq_zero_of_mul_eq_zero
    (hg.analyticOnNhd ho) hfg puncturedPlane_isConnected.isPreconnected

end Nagata.W19

end

section

/-! Holomorphic wrappers for the checked analytic factorization core. -/
namespace Nagata.W19
open scoped BigOperators

theorem exists_holomorphic_centered_factor
    {U : Set ℂ} (hU : IsOpen U) (h : ℂ → ℂ)
    (hh : DifferentiableOn ℂ h U) (a : ℂ) (ha : a ∈ U)
    (k : ℕ) (ho : (k : ℕ∞) ≤ analyticOrderAt h a) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧
      ∀ z, h z = (z - a) ^ k * g z := by
  obtain ⟨g, hg, heq⟩ := exists_analytic_centered_factor hU h (hh.analyticOnNhd hU) a ha k ho
  exact ⟨g, hg.differentiableOn, heq⟩

theorem analytic_order_of_nonvanishing_factor
    {U : Set ℂ} (hU : IsOpen U) {h g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {a b : ℂ} (hb : b ∈ U)
    (hab : b ≠ a) (k : ℕ) (heq : ∀ z, h z = (z - a) ^ k * g z) :
    analyticOrderAt h b = analyticOrderAt g b :=
  analytic_order_of_nonvanishing_analytic_factor hU (hg.analyticOnNhd hU) hb hab k heq

theorem exists_holomorphic_finset_factorization
    {I : Type*} (s : Finset I) {U : Set ℂ} (hU : IsOpen U)
    (h : ℂ → ℂ) (hh : DifferentiableOn ℂ h U)
    (ξ : I → ℂ) (hξ : Function.Injective ξ) (hmem : ∀ i ∈ s, ξ i ∈ U)
    (k : ℕ) (ho : ∀ i ∈ s, (k : ℕ∞) ≤ analyticOrderAt h (ξ i)) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧
      ∀ z, h z = (∏ i ∈ s, (z - ξ i) ^ k) * g z := by
  obtain ⟨g, hg, heq⟩ := exists_analytic_finset_factorization s hU h
    (hh.analyticOnNhd hU) ξ hξ hmem k ho
  exact ⟨g, hg.differentiableOn, heq⟩

/-- Interface consumed by the holomorphic collision estimate. -/
theorem exists_holomorphic_factorization
    {q : ℕ} {U : Set ℂ} (hU : IsOpen U) (h : ℂ → ℂ)
    (hh : DifferentiableOn ℂ h U) (ξ : Fin q → ℂ)
    (hξ : Function.Injective ξ) (hmem : ∀ i, ξ i ∈ U)
    (k : ℕ) (ho : ∀ i, (k : ℕ∞) ≤ analyticOrderAt h (ξ i)) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧
      ∀ z, h z = (∏ i, (z - ξ i) ^ k) * g z := by
  obtain ⟨g, hg, heq⟩ := exists_analytic_factorization hU h
    (hh.analyticOnNhd hU) ξ hξ hmem k ho
  exact ⟨g, hg.differentiableOn, heq⟩

end Nagata.W19

end

section

/-! Polynomial evaluations in actual holomorphic section-cover functions.
The resulting zero-product alternative is the analytic input for primality
of the polynomial relation ideal; no function-domain property is assumed. -/

namespace Nagata.W19

theorem differentiableOn_polynomial_eval {σ : Type*} {U : Set ℂ}
    (s : σ → ℂ → ℂ) (hs : ∀ i, DifferentiableOn ℂ (s i) U)
    (P : MvPolynomial σ ℂ) :
    DifferentiableOn ℂ (fun z => MvPolynomial.eval (fun i => s i z) P) U := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa only [MvPolynomial.eval_C] using differentiableOn_const a
  | add P Q hP hQ =>
    simp only [map_add]
    exact hP.add hQ
  | mul_X P i hP =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hP.mul (hs i)

theorem polynomial_eval_punctured_mul_zero {σ : Type*}
    (s : σ → ℂ → ℂ) (hs : ∀ i, DifferentiableOn ℂ (s i) {z : ℂ | z ≠ 0})
    (P Q : MvPolynomial σ ℂ)
    (hPQ : ∀ z, z ≠ 0 → MvPolynomial.eval (fun i => s i z) (P * Q) = 0) :
    (∀ z, z ≠ 0 → MvPolynomial.eval (fun i => s i z) P = 0) ∨
      (∀ z, z ≠ 0 → MvPolynomial.eval (fun i => s i z) Q = 0) := by
  apply holomorphic_punctured_mul_zero
    (fun z => MvPolynomial.eval (fun i => s i z) P)
    (fun z => MvPolynomial.eval (fun i => s i z) Q)
    (differentiableOn_polynomial_eval s hs P) (differentiableOn_polynomial_eval s hs Q)
  intro z hz
  simpa only [map_mul] using hPQ z hz

/-- The exact three-section specialization used for the degree-three map. -/
theorem cubic_sections_polynomial_mul_zero {τ γ : ℂ}
    (s : Fin 3 → Nagata.W08.automorphicSections τ 3 γ)
    (P Q : MvPolynomial (Fin 3) ℂ)
    (hPQ : ∀ z, z ≠ 0 → MvPolynomial.eval (fun i => (s i).val z) (P * Q) = 0) :
    (∀ z, z ≠ 0 → MvPolynomial.eval (fun i => (s i).val z) P = 0) ∨
      (∀ z, z ≠ 0 → MvPolynomial.eval (fun i => (s i).val z) Q = 0) := by
  exact polynomial_eval_punctured_mul_zero (fun i => (s i).val)
    (fun i z hz => ((s i).property.2.1 z hz).differentiableWithinAt) P Q hPQ

end Nagata.W19

end

end OAI
