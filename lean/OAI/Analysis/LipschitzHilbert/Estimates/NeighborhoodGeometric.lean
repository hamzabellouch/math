import OAI.Analysis.LipschitzHilbert.Estimates.TopNeighborhood
import OAI.Analysis.LipschitzHilbert.Estimates.MomentSuperlevel

namespace OAI

/-! A common vertical-neighborhood exceptional set has exponentially
small area when the chosen even line moment has polynomial growth. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem quarter_area_of_even_moment (X M : ℝ≥0∞) (A : ℝ) (hA : 0 < A) (n : ℕ)
    (h : (ENNReal.ofReal (4*A))^(2*n)*X ≤ (ENNReal.ofReal (2*A))^(2*n)*M) :
    X ≤ (1/4:ℝ≥0∞)^n*M := by
  have ha0 : (ENNReal.ofReal (4*A))^(2*n) ≠ 0 :=
    pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))
  have hat : (ENNReal.ofReal (4*A))^(2*n) ≠ ⊤ := by finiteness
  have hr : ENNReal.ofReal (2*A)/ENNReal.ofReal (4*A) = (1/2:ℝ≥0∞) := by
    rw [← ENNReal.ofReal_div_of_pos (by positivity : 0 < 4*A)]
    have heq : (2*A)/(4*A) = (1/2:ℝ) := by field_simp [hA.ne']; norm_num
    rw [heq, ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2)]
    norm_num [pow_two]
  calc
    X = ((ENNReal.ofReal (4*A))^(2*n))⁻¹ *
        ((ENNReal.ofReal (4*A))^(2*n)*X) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 hat, one_mul]
    _ ≤ ((ENNReal.ofReal (4*A))^(2*n))⁻¹ *
        ((ENNReal.ofReal (2*A))^(2*n)*M) := mul_le_mul' le_rfl h
    _ = (ENNReal.ofReal (2*A)/ENNReal.ofReal (4*A))^(2*n)*M := by
      rw [ENNReal.div_eq_inv_mul, mul_pow, ENNReal.inv_pow]
      ring
    _ = _ := by
      have hquarter : (1/2:ℝ≥0∞)^2 = 1/4 := by
        rw [ENNReal.div_eq_inv_mul, mul_one, ← ENNReal.inv_pow]
        norm_num [pow_two]
      rw [hr, pow_mul, hquarter]

theorem top_neighborhood_geometric {α κ : Type*} [Fintype κ]
    (frequency : κ → ℝ) (f : α → κ → ℝ → ℝ → ℂ)
    (V D : ℝ × ℝ → ℝ) (hV : Continuous V) (hD : Continuous D)
    (U : Set ℝ) (hU : MeasurableSet U) (c r A : ℝ)
    (hr : 0 < r) (hA : 0 < A) (n : ℕ) (M : ℝ≥0∞)
    (hline : ∀ y, (∫⁻ x in U, ENNReal.ofReal
      (V (y,x)^(2*n)+(4*r*D (y,x))^(2*n))) ≤ 2*(ENNReal.ofReal A)^(2*n)*M)
    (hf : ∀ i x y, y ∈ Icc (c-2*r) (c+2*r) → ∀ k,
      DifferentiableAt ℝ (f i k x) y)
    (hmem : ∀ i x, MemLp (covariantSignal frequency (fun k => f i k x)) 2
      (volume.restrict (Icc (c-2*r) (c+2*r))))
    (hbV : ∀ i x y, y ∈ Icc (c-2*r) (c+2*r) →
      ‖(WithLp.toLp 2 (fun k => f i k x y) : EuclideanSpace ℂ κ)‖ ≤ V (y,x))
    (hbD : ∀ i x y, y ∈ Icc (c-2*r) (c+2*r) →
      ‖covariantSignal frequency (fun k => f i k x) y‖ ≤ D (y,x)) :
    ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧ bad ⊆ U ×ˢ Icc (c-r) (c+r) ∧
      (volume.prod volume) bad ≤ 2*(1/4:ℝ≥0∞)^n*M*ENNReal.ofReal (2*r) ∧
      ∀ i x z v, x ∈ U → |z-c| ≤ r → |v| ≤ r → (x,z) ∉ bad →
        ‖(WithLp.toLp 2 (fun k => f i k x (z+v)) : EuclideanSpace ℂ κ)‖ ≤ 4*A := by
  obtain ⟨bad,hbad,hsub,harea,hpoint⟩ := top_neighborhood_exceptional frequency f V D hV hD U hU
    c r (4*A) hr (by positivity) n (2*(ENNReal.ofReal A)^(2*n)*M) hline hf hmem hbV hbD
  refine ⟨bad,hbad,hsub,?_,hpoint⟩
  have heq : (4:ℝ≥0∞)^n*(2*(ENNReal.ofReal A)^(2*n)*M)*ENNReal.ofReal (2*r) =
      (ENNReal.ofReal (2*A))^(2*n)*(2*M*ENNReal.ofReal (2*r)) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    simp only [ENNReal.ofReal_ofNat, pow_mul]
    norm_num
    ring
  have h := quarter_area_of_even_moment ((volume.prod volume) bad)
    (2*M*ENNReal.ofReal (2*r)) A hA n (harea.trans_eq heq)
  convert h using 1
  ring

end LipschitzHilbert

end

end OAI
