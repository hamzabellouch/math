import Mathlib
import OAI.Geometry.SplitTangent.RationalFamilies
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.FormalBoxes

namespace OAI

/-! Rational Encoding. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold BigOperators
universe u
namespace SplitTangent.RationalParameters

 
def ofPolynomials {N : ℕ} (d : ℕ) (P : Fin (N+1) → Polynomial ℂ) : Coeff N d :=
  fun k => (P (finProdFinEquiv.symm k).1).coeff (finProdFinEquiv.symm k).2.val

lemma ev_ofPolynomials_false {N d : ℕ} (P : Fin (N+1) → Polynomial ℂ)
    (hP : ∀ i, (P i).natDegree≤d) (z : ℂ) :
    ev false (ofPolynomials d P) z = fun i => (P i).eval z := by
  ext i
  simp only [ev,ofPolynomials,Equiv.symm_apply_apply,Bool.false_eq_true,↓reduceIte]
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hP i))]
  exact Fin.sum_univ_eq_sum_range (fun k : ℕ => (P i).coeff k * z^k) (d+1)

lemma ev_ofPolynomials_true {N d : ℕ} (P : Fin (N+1) → Polynomial ℂ)
    (hP : ∀ i, (P i).natDegree≤d) (z : ℂ) :
    ev true (ofPolynomials d P) z = fun i => ((P i).reflect d).eval z := by
  ext i
  apply tendsto_nhds_unique_of_frequently_eq
    ((continuous_apply i).comp ((ev_continuous true).comp (continuous_id.prodMk continuous_const))).continuousAt
    (by fun_prop : ContinuousAt (fun w => ((P i).reflect d).eval w) z)
  have hfreq : ∃ᶠ w in 𝓝 z, w≠(0 : ℂ) := by
    simpa only [Polynomial.eval_X] using
      PolynomialTuple.frequently_eval_ne_zero Polynomial.X Polynomial.X_ne_zero z
  apply hfreq.mono
  intro w hw
  have he := congrFun (ev_transition (ofPolynomials d P) (inv_ne_zero hw)) i
  rw [ev_ofPolynomials_false P hP,inv_inv] at he
  have hp := PolynomialTuple.reflect_transition (P i) d (hP i) w⁻¹ (inv_ne_zero hw)
  simp only [inv_inv] at hp
  change (P i).eval w⁻¹ = w⁻¹ ^ d * ev true (ofPolynomials d P) w i at he
  exact mul_left_cancel₀ (pow_ne_zero d (inv_ne_zero hw))
    (he.symm.trans (hp.symm.trans (mul_comm _ _)))

 

theorem curve_encoding {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X) (g : RationalCurve X) :
    ∃ d : ℕ, ∃ τ : Coeff e.N d, τ∈regular e.N d ∩ accepted e d ∧
      (∀ z, e.Incidence (g.finite z) (ev false τ z)) ∧
      (∀ z, e.Incidence (g.infinity z) (ev true τ z)) := by
  classical
  obtain ⟨d,P,Q,hP,hQ,hdeg,hfinite,hinfty,htrans⟩ := rationalCurve_two_chart_polynomials e g
  let τ := ofPolynomials d P
  have hτf (z : ℂ) : ev false τ z = fun i => (P i).eval z :=
    ev_ofPolynomials_false P (fun i => (hdeg i).1) z
  have hτi (z : ℂ) : ev true τ z = fun i => (Q i).eval z := by
    rw [ev_ofPolynomials_true P (fun i => (hdeg i).1)]
    ext i
    rw [← (hdeg i).2]
  have hf (z : ℂ) : e.Incidence (g.finite z) (ev false τ z) := by
    obtain ⟨k,hk⟩ := Function.ne_iff.mp (e.map (g.finite z)).rep_nonzero
    apply (e.incidence_iff_coordinates hk).mpr
    intro j
    simpa only [hτf] using (hfinite z k j hk).trans (mul_comm _ _)
  have hi (z : ℂ) : e.Incidence (g.infinity z) (ev true τ z) := by
    obtain ⟨k,hk⟩ := Function.ne_iff.mp (e.map (g.infinity z)).rep_nonzero
    apply (e.incidence_iff_coordinates hk).mpr
    intro j
    simpa only [hτi] using (hinfty z k j hk).trans (mul_comm _ _)
  refine ⟨d,τ,⟨?_,?_⟩,hf,hi⟩
  · intro b z hz
    cases b
    · obtain ⟨i,hi⟩ := PolynomialTuple.basepoint_free P hP z
      intro he
      have hh := congrFun he i
      rw [hτf] at hh
      exact hi hh
    · obtain ⟨i,hi⟩ := PolynomialTuple.basepoint_free Q hQ z
      intro he
      have hh := congrFun he i
      rw [hτi] at hh
      exact hi hh
  · intro b z
    cases b
    · exact ⟨g.finite z,hf z⟩
    · exact ⟨g.infinity z,hi z⟩

end SplitTangent.RationalParameters

end

end OAI
