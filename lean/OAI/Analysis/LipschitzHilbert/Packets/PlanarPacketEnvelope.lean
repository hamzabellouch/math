import OAI.Analysis.LipschitzHilbert.Packets.ScaledPlanarPacket
import OAI.Analysis.LipschitzHilbert.Estimates.ShearedEnvelope

namespace OAI

/-! Uniform packet envelopes from general normalized planar profiles.
The bound does not depend on the carrier frequency or physical scales. -/

noncomputable section
namespace LipschitzHilbert

theorem modulatedPlanarSlice_jointContinuous (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency : ℝ) (hl : l ≠ 0) :
    Continuous (fun z : ℝ × ℝ => modulatedPlanarSlice f a cy l W delta frequency z.1 hl z.2) := by
  have heq : (fun z : ℝ × ℝ => modulatedPlanarSlice f a cy l W delta frequency z.1 hl z.2) =
      (fun z : ℝ × ℝ => Complex.exp ((frequency*(z.1-cy+delta*(z.2-a)):ℝ)*Complex.I)*
        f ((z.2-a)/l,(z.1-cy+delta*(z.2-a))/W)) := by
    funext z
    exact modulatedPlanarSlice_apply f a cy l W delta frequency z.1 hl z.2
  rw [heq]
  apply Continuous.mul (by fun_prop)
  exact f.continuous.comp (by fun_prop)

theorem modulatedPlanarSlice_envelope (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency y C : ℝ) (hl : l ≠ 0) (n : ℕ)
    (hC : 0 ≤ C) (hshear : |delta*l/W| ≤ 1)
    (hf : ∀ z, ‖f z‖ ≤ C*(lineEnvelope 0 1 (2*n) z.1*lineEnvelope 0 1 (2*n) z.2))
    (x : ℝ) :
    ‖modulatedPlanarSlice f a cy l W delta frequency y hl x‖ ≤
      (2^n*C)*(lineEnvelope a l n x*lineEnvelope cy W n y) := by
  rw [modulatedPlanarSlice_norm]
  have heq : (y-cy+delta*(x-a))/W =
      (y-cy)/W-(-delta*l/W)*((x-a)/l) := by
    field_simp
    ring
  have hs := unit_shear_envelope ((x-a)/l) ((y-cy)/W) (-delta*l/W) n
    (by simpa only [neg_mul, neg_div, abs_neg] using hshear)
  have hb := hf ((x-a)/l,(y-cy+delta*(x-a))/W)
  rw [heq] at hb ⊢
  apply hb.trans
  have h := mul_le_mul_of_nonneg_left hs hC
  simpa only [lineEnvelope, sub_zero, div_one, mul_left_comm C (2^n), mul_assoc] using h

theorem modulatedPlanarSlice_fixed_envelope (f : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a cy l W delta frequency y (hl : l ≠ 0),
      |delta*l/W| ≤ 1 → ∀ x,
      ‖modulatedPlanarSlice f a cy l W delta frequency y hl x‖ ≤
        C*(lineEnvelope a l n x*lineEnvelope cy W n y) := by
  refine ⟨2^n*planarEnvelopeConstant f (2*n),
    mul_pos (pow_pos (by norm_num) _) (planarEnvelopeConstant_pos _ _), ?_⟩
  intro a cy l W delta frequency y hl hs x
  exact modulatedPlanarSlice_envelope f a cy l W delta frequency y
    (planarEnvelopeConstant f (2*n)) hl n (planarEnvelopeConstant_pos _ _).le hs
    (planar_schwartz_envelope f (2*n)) x

end LipschitzHilbert

end

end OAI
