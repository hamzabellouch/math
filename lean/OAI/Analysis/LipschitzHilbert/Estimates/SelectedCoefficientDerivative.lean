import OAI.Analysis.LipschitzHilbert.Estimates.TopEnvelopeDerivative
import OAI.Analysis.LipschitzHilbert.Estimates.PlanarCoefficientNorm

namespace OAI

/-! The weighted horizontal derivative bound with the original, uniformly
bounded coefficients, without normalizing the resulting synthesis. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem vectorPacketSynthesis_coeff_smul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap ℝ ℂ) (s x : ℝ) :
    vectorPacketSynthesis (fun i => s • c i) f x = s • vectorPacketSynthesis c f x := by
  ext k
  simp only [vectorPacketSynthesis, packetSynthesis_apply, WithLp.ofLp_toLp,
    PiLp.smul_apply, Complex.real_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem vectorPacketSynthesis_deriv_coeff_smul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap ℝ ℂ) (s x : ℝ) :
    deriv (vectorPacketSynthesis (fun i => s • c i) f) x =
      s • deriv (vectorPacketSynthesis c f) x := by
  rw [vectorPacketSynthesis_deriv,vectorPacketSynthesis_deriv]
  ext k
  simp only [WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,
    Complex.real_smul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem top_weighted_selected_derivative_bounded {N : ℕ} {κ : Type} {ι : Fin N → Type}
    [Fintype κ] [∀ j, Fintype (ι j)]
    (c : ∀ j, ι j → EuclideanSpace ℂ κ)
    (f : ∀ j, ι j → κ → SchwartzMap ℝ ℂ)
    (site : ∀ j, ι j → ℤ × ℤ) (hinj : ∀ j, Function.Injective (site j))
    (a b L W u v r R x y C B cutoff : ℝ) (q : ℕ)
    (hL : 0 < L) (hW : 0 < W) (hr : 0 < r) (hR : 0 < R)
    (hLr : L ≤ r) (hWR : W ≤ R) (hC : 0 ≤ C) (hB : 0 < B) (hcutoff : 0 < cutoff)
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
  have h := top_weighted_selected_derivative (fun j i => B⁻¹ • c j i) f site hinj
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
