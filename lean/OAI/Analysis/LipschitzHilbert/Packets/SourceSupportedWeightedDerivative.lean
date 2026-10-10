import OAI.Analysis.LipschitzHilbert.Estimates.SelectedCoefficientDerivative

namespace OAI

/-! The weighted derivative estimate uses upper scale bounds only at
actual packet items. Empty scales do not constrain the top window. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
theorem top_weighted_selected_derivative_of_supported {N : ℕ} {κ : Type} {ι : Fin N → Type}
    [Fintype κ] [∀ j, Fintype (ι j)]
    (c : ∀ j, ι j → EuclideanSpace ℂ κ)
    (f : ∀ j, ι j → κ → SchwartzMap ℝ ℂ)
    (site : ∀ j, ι j → ℤ × ℤ) (hinj : ∀ j, Function.Injective (site j))
    (a b L W u v r R x y C cutoff : ℝ) (q : ℕ)
    (hL : 0 < L) (hW : 0 < W) (hr : 0 < r) (hR : 0 < R)
    (hLr : ∀ j (_i : ι j), L/(2:ℝ)^j.val ≤ r) (hWR : W ≤ R) (hC : 0 ≤ C) (hcutoff : 0 < cutoff)
    (hc : ∀ j i, ‖c j i‖ ≤ 1)
    (hcx : ∀ j i, |a+(L/(2:ℝ)^j.val)*(site j i).1-u| ≤ r)
    (hcy : ∀ j i, |b+W*(site j i).2-v| ≤ R)
    (s : Finset (Fin N)) (hs : ∀ j ∈ s, cutoff ≤ L/(2:ℝ)^j.val)
    (hf : ∀ j i k, ‖deriv (f j i k) x‖ ≤ (C/(L/(2:ℝ)^j.val))*
      (lineEnvelope (a+(L/(2:ℝ)^j.val)*(site j i).1) (L/(2:ℝ)^j.val) (3+2*q) x *
        lineEnvelope (b+W*(site j i).2) W (2+2*q) y)) :
    (polynomialWeight u r q x*polynomialWeight v R q y)*
      ‖deriv (fun t => ∑ j ∈ s, vectorPacketSynthesis (c j) (f j) t) x‖ ≤
        4*((16^q*(16^q*C))*(4*Real.pi)^2)/cutoff := by
  apply selected_scale_weighted_derivative_bound c f site hinj a b L W x y
    (16^q*(16^q*C)) (polynomialWeight u r q x*polynomialWeight v R q y) cutoff
    hL hW.ne' (by positivity)
    (mul_nonneg (zero_le_one.trans (polynomialWeight_one_le _ _ _ _))
      (zero_le_one.trans (polynomialWeight_one_le _ _ _ _))) hcutoff hc s hs
  intro j i k
  have hlen : 0 < L/(2:ℝ)^j.val := div_pos hL (by positivity)
  have h := topWeight_mul_envelope x y u r v R
    (a+(L/(2:ℝ)^j.val)*(site j i).1) (L/(2:ℝ)^j.val) (b+W*(site j i).2) W
    (C/(L/(2:ℝ)^j.val)) q 3 2 hlen hr hW hR (hLr j i) hWR
    (hcx j i) (hcy j i) (div_nonneg hC hlen.le)
  have hw : 0 ≤ polynomialWeight u r q x*polynomialWeight v R q y :=
    mul_nonneg (zero_le_one.trans (polynomialWeight_one_le _ _ _ _))
      (zero_le_one.trans (polynomialWeight_one_le _ _ _ _))
  exact (mul_le_mul_of_nonneg_left (hf j i k) hw).trans (by convert h using 1; ring)


theorem top_weighted_selected_derivative_bounded_of_supported {N : ℕ} {κ : Type} {ι : Fin N → Type}
    [Fintype κ] [∀ j, Fintype (ι j)]
    (c : ∀ j, ι j → EuclideanSpace ℂ κ)
    (f : ∀ j, ι j → κ → SchwartzMap ℝ ℂ)
    (site : ∀ j, ι j → ℤ × ℤ) (hinj : ∀ j, Function.Injective (site j))
    (a b L W u v r R x y C B cutoff : ℝ) (q : ℕ)
    (hL : 0 < L) (hW : 0 < W) (hr : 0 < r) (hR : 0 < R)
    (hLr : ∀ j (_i : ι j), L/(2:ℝ)^j.val ≤ r) (hWR : W ≤ R) (hC : 0 ≤ C) (hB : 0 < B) (hcutoff : 0 < cutoff)
    (hc : ∀ j i, ‖c j i‖ ≤ B)
    (hcx : ∀ j i, |a+(L/(2:ℝ)^j.val)*(site j i).1-u| ≤ r)
    (hcy : ∀ j i, |b+W*(site j i).2-v| ≤ R)
    (s : Finset (Fin N)) (hs : ∀ j ∈ s, cutoff ≤ L/(2:ℝ)^j.val)
    (hf : ∀ j i k, ‖deriv (f j i k) x‖ ≤ (C/(L/(2:ℝ)^j.val))*
      (lineEnvelope (a+(L/(2:ℝ)^j.val)*(site j i).1) (L/(2:ℝ)^j.val) (3+2*q) x *
        lineEnvelope (b+W*(site j i).2) W (2+2*q) y)) :
    (polynomialWeight u r q x*polynomialWeight v R q y)*
      ‖deriv (fun t => ∑ j ∈ s, vectorPacketSynthesis (c j) (f j) t) x‖ ≤
        B*(4*((16^q*(16^q*C))*(4*Real.pi)^2)/cutoff) := by
  have hn (j : Fin N) (i : ι j) : ‖B⁻¹ • c j i‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB)]
    exact (mul_le_mul_of_nonneg_left (hc j i) (inv_nonneg.mpr hB.le)).trans_eq
      (inv_mul_cancel₀ hB.ne')
  have h := top_weighted_selected_derivative_of_supported (fun j i => B⁻¹ • c j i) f site hinj
    a b L W u v r R x y C cutoff q hL hW hr hR hLr hWR hC hcutoff hn hcx hcy s hs hf
  have hd := HasDerivAt.fun_sum (u := s) (fun j _ =>
    (vectorPacketSynthesis_hasDerivAt (c j) (f j) x).differentiableAt.hasDerivAt)
  have hdn := HasDerivAt.fun_sum (u := s) (fun j _ =>
    (vectorPacketSynthesis_hasDerivAt (fun i => B⁻¹ • c j i) (f j) x).differentiableAt.hasDerivAt)
  have hdscaled : deriv
      (fun t => ∑ j ∈ s, vectorPacketSynthesis (fun i => B⁻¹ • c j i) (f j) t) x =
      B⁻¹ • deriv (fun t => ∑ j ∈ s, vectorPacketSynthesis (c j) (f j) t) x := by
    rw [hdn.deriv,hd.deriv]
    simp only [vectorPacketSynthesis_deriv_coeff_smul,Finset.smul_sum]
  rw [hdscaled, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB)] at h
  have hh := mul_le_mul_of_nonneg_left h hB.le
  calc
    _ = B*((polynomialWeight u r q x*polynomialWeight v R q y)*
        (B⁻¹*‖deriv (fun t => ∑ j ∈ s, vectorPacketSynthesis (c j) (f j) t) x‖)) := by
      rw [show B*((polynomialWeight u r q x*polynomialWeight v R q y)*
        (B⁻¹*‖deriv (fun t => ∑ j ∈ s, vectorPacketSynthesis (c j) (f j) t) x‖)) =
        (B*B⁻¹)*((polynomialWeight u r q x*polynomialWeight v R q y)*
          ‖deriv (fun t => ∑ j ∈ s, vectorPacketSynthesis (c j) (f j) t) x‖) by ring,
        mul_inv_cancel₀ hB.ne', one_mul]
    _ ≤ _ := hh

end LipschitzHilbert

end

end OAI
