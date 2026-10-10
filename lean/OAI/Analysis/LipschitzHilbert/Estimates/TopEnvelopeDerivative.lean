import OAI.Analysis.LipschitzHilbert.Packets.TopWeightedPacket
import OAI.Analysis.LipschitzHilbert.Estimates.SelectedScaleDerivative

namespace OAI

/-! Fixed top weights preserve the pointwise derivative envelopes needed
for the unconditional horizontal derivative estimate. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem topWeight_mul_envelope (x y a r b R s l t W C : ℝ) (q m n : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hW : 0 < W) (hR : 0 < R)
    (hlr : l ≤ r) (hWR : W ≤ R) (hs : |s-a| ≤ r) (ht : |t-b| ≤ R) (hC : 0 ≤ C) :
    (polynomialWeight a r q x*polynomialWeight b R q y)*
      (C*(lineEnvelope s l (m+2*q) x*lineEnvelope t W (n+2*q) y)) ≤
    (16^q*(16^q*C))*(lineEnvelope s l m x*lineEnvelope t W n y) := by
  have hx := polynomialWeight_mul_envelope x s a l r q m hl hr hlr hs
  have hy := polynomialWeight_mul_envelope y t b W R q n hW hR hWR ht
  have hy0 : 0 ≤ polynomialWeight b R q y*lineEnvelope t W (n+2*q) y :=
    mul_nonneg (zero_le_one.trans (polynomialWeight_one_le _ _ _ _)) (lineEnvelope_nonneg _ _ _ _)
  have hb := mul_le_mul hx hy hy0 (mul_nonneg (by positivity) (lineEnvelope_nonneg _ _ _ _))
  have h := mul_le_mul_of_nonneg_left hb hC
  convert h using 1 <;> ring


theorem top_weighted_selected_derivative {N : ℕ} {κ : Type} {ι : Fin N → Type}
    [Fintype κ] [∀ j, Fintype (ι j)]
    (c : ∀ j, ι j → EuclideanSpace ℂ κ)
    (f : ∀ j, ι j → κ → SchwartzMap ℝ ℂ)
    (site : ∀ j, ι j → ℤ × ℤ) (hinj : ∀ j, Function.Injective (site j))
    (a b L W u v r R x y C cutoff : ℝ) (q : ℕ)
    (hL : 0 < L) (hW : 0 < W) (hr : 0 < r) (hR : 0 < R)
    (hLr : L ≤ r) (hWR : W ≤ R) (hC : 0 ≤ C) (hcutoff : 0 < cutoff)
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
  have hlen_top : L/(2:ℝ)^j.val ≤ L := div_le_self hL.le (one_le_pow₀ (by norm_num))
  have h := topWeight_mul_envelope x y u r v R
    (a+(L/(2:ℝ)^j.val)*(site j i).1) (L/(2:ℝ)^j.val) (b+W*(site j i).2) W
    (C/(L/(2:ℝ)^j.val)) q 3 2 hlen hr hW hR (hlen_top.trans hLr) hWR
    (hcx j i) (hcy j i) (div_nonneg hC hlen.le)
  have hw : 0 ≤ polynomialWeight u r q x*polynomialWeight v R q y :=
    mul_nonneg (zero_le_one.trans (polynomialWeight_one_le _ _ _ _))
      (zero_le_one.trans (polynomialWeight_one_le _ _ _ _))
  exact (mul_le_mul_of_nonneg_left (hf j i k) hw).trans (by convert h using 1; ring)

end LipschitzHilbert

end

end OAI
