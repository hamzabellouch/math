import OAI.NumberTheory.Ostmann.Tree.AffineHilbertSchmidt
import OAI.NumberTheory.Ostmann.Tree.Parseval

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]

def meanInner (f h : ZMod p → ℂ) : ℂ := mean (fun t => conj (f t)*h t)

theorem meanInner_self (f : ZMod p → ℂ) : meanInner f f = (l2Sq f : ℂ) := by
  simp only [meanInner, mean, l2Sq, Complex.conj_mul']
  push_cast
  rfl

theorem mean_add (f h : ZMod p → ℂ) : mean (fun t => f t+h t) = mean f+mean h := by
  simp only [mean, Finset.sum_add_distrib, mul_add]

theorem mean_const_mul (c : ℂ) (f : ZMod p → ℂ) :
    mean (fun t => c*f t) = c*mean f := by
  simp only [mean, ← Finset.mul_sum]
  ring

theorem mean_const (c : ℂ) : mean (fun _ : ZMod p => c) = c := by
  have hp : (p:ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  simp only [mean, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  exact inv_mul_cancel_left₀ hp c

theorem mean_conj (f : ZMod p → ℂ) : mean (fun t => conj (f t)) = conj (mean f) := by
  simp only [mean, map_mul, map_inv₀, map_natCast, map_sum]

theorem l2Sq_const_mul (c : ℂ) (f : ZMod p → ℂ) :
    l2Sq (fun t => c*f t) = ‖c‖^2*l2Sq f := by
  simp only [l2Sq, norm_mul, mul_pow, ← Finset.mul_sum]
  ring

theorem l2Sq_const (c : ℂ) : l2Sq (fun _ : ZMod p => c) = ‖c‖^2 := by
  have hp : (p:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  simp only [l2Sq, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  exact inv_mul_cancel_left₀ hp _

theorem l2Sq_conj (f : ZMod p → ℂ) : l2Sq (fun t => conj (f t)) = l2Sq f := by
  simp only [l2Sq, Complex.norm_conj]

theorem mean_sub_mean (f : ZMod p → ℂ) : mean (fun t => f t-mean f) = 0 := by
  simp only [mean, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul, mul_sub]
  have hp : (p:ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  field_simp
  ring

theorem meanInner_norm_sq_le (f h : ZMod p → ℂ) :
    ‖meanInner f h‖^2 ≤ l2Sq f*l2Sq h := by
  have hc := norm_sum_mul_sq_le Finset.univ (fun t => conj (f t)) h
  simp only [Complex.norm_conj] at hc
  simp only [meanInner, mean, norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
  calc
    _ ≤ ((p:ℝ)⁻¹)^2 * ((∑ t, ‖f t‖^2)*(∑ t, ‖h t‖^2)) :=
      mul_le_mul_of_nonneg_left hc (sq_nonneg _)
    _ = _ := by dsimp [l2Sq]; ring

theorem l2Sq_add_const (f : ZMod p → ℂ) (c : ℂ) (hf : mean f=0) :
    l2Sq (fun t => f t+c) = l2Sq f+‖c‖^2 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_add, ← meanInner_self, ← meanInner_self, Complex.ofReal_pow]
  rw [← Complex.conj_mul' c]
  unfold meanInner
  have he : (fun t => conj (f t+c)*(f t+c)) =
      (fun t => ((conj (f t)*f t + conj c*f t) + c*conj (f t)) + conj c*c) := by
    funext t
    rw [map_add]
    ring
  rw [he, mean_add, mean_add, mean_add, mean_const_mul, mean_const_mul,
    mean_conj, mean_const, hf]
  simp

end
end Ostmann.FiniteField

end OAI
