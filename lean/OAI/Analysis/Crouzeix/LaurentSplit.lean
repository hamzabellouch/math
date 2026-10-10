import Mathlib
import OAI.Analysis.Crouzeix.Faber

namespace OAI

/-! Laurent Split. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

namespace CrouzeixHilbert.Conformal

lemma exists_finite_principal_part {V : Set ℂ} (hV : IsOpen V) (h0V : (0 : ℂ) ∈ V)
    (n : ℕ) {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h V) :
    ∃ (p : Polynomial ℂ) (q : ℂ → ℂ), DifferentiableOn ℂ q V ∧ q 0 = 0 ∧
      ∀ t : ℂ, t ≠ 0 → t⁻¹ ∈ V → t^n * h t⁻¹ = p.eval t + q t⁻¹ := by
  induction n generalizing h with
  | zero =>
    refine ⟨Polynomial.C (h 0), fun u => h u - h 0, hh.sub_const _, sub_self _, ?_⟩
    intro t ht htV
    simp
  | succ n ih =>
    have hd : DifferentiableOn ℂ (dslope h 0) V :=
      (differentiableOn_dslope (hV.mem_nhds h0V)).mpr hh
    obtain ⟨p,q,hq,hq0,he⟩ := ih hd
    refine ⟨Polynomial.C (h 0) * Polynomial.X^(n+1) + p, q, hq, hq0, ?_⟩
    intro t ht htV
    have hh' : h t⁻¹ = h 0 + t⁻¹ * dslope h 0 t⁻¹ := by
      rw [dslope_of_ne _ (inv_ne_zero ht), slope_def_field]
      simp only [sub_zero]
      field_simp
      ring
    rw [hh', mul_add, pow_succ]
    have hp : t^n * t * (t⁻¹ * dslope h 0 t⁻¹) = t^n * dslope h 0 t⁻¹ := by
      field_simp
    rw [hp, he t ht htV]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, pow_succ]
    ring

namespace ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U)

lemma power_finite_principal_part (n : ℕ) :
    ∃ (p : Polynomial ℂ) (q : ℂ → ℂ), DifferentiableOn ℂ q C.reciprocalDisk ∧ q 0 = 0 ∧
      ∀ t : ℂ, C.radius < ‖t‖ → (C.G t)^n = p.eval t + q t⁻¹ := by
  have hh : DifferentiableOn ℂ (fun u => (C.leading + u * C.regular u)^n) C.reciprocalDisk :=
    ((differentiableOn_const _).add
      (differentiableOn_id.mul C.regular_analytic.differentiableOn)).pow n
  obtain ⟨p,q,hq,hq0,he⟩ := exists_finite_principal_part isOpen_ball
    (mem_ball_self (inv_pos.mpr C.radius_pos)) n hh
  refine ⟨p,q,hq,hq0,fun t ht => ?_⟩
  have ht0 := norm_pos_iff.mp (C.radius_pos.trans ht)
  rw [← he t ht0 (C.inverse_mem_reciprocalDisk ht), ← mul_pow, C.laurent t ht]
  congr 1
  field_simp

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
