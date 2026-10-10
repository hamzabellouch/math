import OAI.Analysis.LipschitzHilbert.Fourier.PlanarModulatedJet
import OAI.Analysis.LipschitzHilbert.Packets.PlanarPacketDerivative

namespace OAI

/-! Uniform profile constants for the first three raw waves. Scaling a
covariant derivative costs only the square of its dimensionless width. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem planarVerticalDerivative_smul (c : ℂ) (f : SchwartzMap (ℝ × ℝ) ℂ) :
    planarVerticalDerivative (c • f) = c • planarVerticalDerivative f := by
  unfold planarVerticalDerivative
  rw [map_smul, map_smul]

theorem planarHorizontalDerivative_smul (c : ℂ) (f : SchwartzMap (ℝ × ℝ) ℂ) :
    planarHorizontalDerivative (c • f) = c • planarHorizontalDerivative f := by
  unfold planarHorizontalDerivative
  rw [map_smul, map_smul]

def planarVerticalJet (f : SchwartzMap (ℝ × ℝ) ℂ) (i : Fin 3) : SchwartzMap (ℝ × ℝ) ℂ :=
  if i = 0 then f else if i = 1 then planarVerticalDerivative f else
    planarVerticalDerivative (planarVerticalDerivative f)

theorem planarProfileJet_eq (f : SchwartzMap (ℝ × ℝ) ℂ) (ratio : ℝ) (i : Fin 3) :
    planarProfileJet f ratio i = (ratio:ℂ)^i.val • planarVerticalJet f i := by
  fin_cases i
  · simp [planarProfileJet,planarVerticalJet]
  · simp [planarProfileJet,planarVerticalJet]
  · change (ratio:ℂ) • planarVerticalDerivative ((ratio:ℂ) • planarVerticalDerivative f) =
      (ratio:ℂ)^2 • planarVerticalDerivative (planarVerticalDerivative f)
    rw [planarVerticalDerivative_smul,smul_smul,pow_two]

def planarProfileConstant (f : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ) : ℝ :=
  ∑ i : Fin 3, (planarEnvelopeConstant (planarVerticalJet f i) n +
    planarEnvelopeConstant (planarHorizontalDerivative (planarVerticalJet f i)) n +
    planarEnvelopeConstant (planarVerticalDerivative (planarVerticalJet f i)) n)

theorem planarProfileConstant_pos (f : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ) :
    0 < planarProfileConstant f n := by
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro i _
  exact add_pos (add_pos (planarEnvelopeConstant_pos _ _) (planarEnvelopeConstant_pos _ _))
    (planarEnvelopeConstant_pos _ _)

theorem planar_profile_base_envelope (f : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ) (i : Fin 3) :
    ∀ z, ‖planarVerticalJet f i z‖ ≤ planarProfileConstant f n *
      (lineEnvelope 0 1 n z.1*lineEnvelope 0 1 n z.2) := by
  intro z
  apply (planar_schwartz_envelope _ n z).trans
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin 3 => planarEnvelopeConstant (planarVerticalJet f j) n +
      planarEnvelopeConstant (planarHorizontalDerivative (planarVerticalJet f j)) n +
      planarEnvelopeConstant (planarVerticalDerivative (planarVerticalJet f j)) n)
    (fun j _ => (add_pos
      (add_pos (planarEnvelopeConstant_pos _ _) (planarEnvelopeConstant_pos _ _))
      (planarEnvelopeConstant_pos _ _)).le) (Finset.mem_univ i)
  change _ ≤ planarProfileConstant f n at h
  have h1 := planarEnvelopeConstant_pos (planarHorizontalDerivative (planarVerticalJet f i)) n
  have h2 := planarEnvelopeConstant_pos (planarVerticalDerivative (planarVerticalJet f i)) n
  exact (by linarith : planarEnvelopeConstant (planarVerticalJet f i) n ≤ planarProfileConstant f n)

theorem planar_profile_horizontal_base_envelope (f : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ) (i : Fin 3) :
    ∀ z, ‖planarHorizontalDerivative (planarVerticalJet f i) z‖ ≤ planarProfileConstant f n *
      (lineEnvelope 0 1 n z.1*lineEnvelope 0 1 n z.2) := by
  intro z
  apply (planar_schwartz_envelope _ n z).trans
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin 3 => planarEnvelopeConstant (planarVerticalJet f j) n +
      planarEnvelopeConstant (planarHorizontalDerivative (planarVerticalJet f j)) n +
      planarEnvelopeConstant (planarVerticalDerivative (planarVerticalJet f j)) n)
    (fun j _ => (add_pos
      (add_pos (planarEnvelopeConstant_pos _ _) (planarEnvelopeConstant_pos _ _))
      (planarEnvelopeConstant_pos _ _)).le) (Finset.mem_univ i)
  change _ ≤ planarProfileConstant f n at h
  have h1 := planarEnvelopeConstant_pos (planarVerticalJet f i) n
  have h2 := planarEnvelopeConstant_pos (planarVerticalDerivative (planarVerticalJet f i)) n
  linarith

theorem planar_profile_vertical_base_envelope (f : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ) (i : Fin 3) :
    ∀ z, ‖planarVerticalDerivative (planarVerticalJet f i) z‖ ≤ planarProfileConstant f n *
      (lineEnvelope 0 1 n z.1*lineEnvelope 0 1 n z.2) := by
  intro z
  apply (planar_schwartz_envelope _ n z).trans
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin 3 => planarEnvelopeConstant (planarVerticalJet f j) n +
      planarEnvelopeConstant (planarHorizontalDerivative (planarVerticalJet f j)) n +
      planarEnvelopeConstant (planarVerticalDerivative (planarVerticalJet f j)) n)
    (fun j _ => (add_pos
      (add_pos (planarEnvelopeConstant_pos _ _) (planarEnvelopeConstant_pos _ _))
      (planarEnvelopeConstant_pos _ _)).le) (Finset.mem_univ i)
  change _ ≤ planarProfileConstant f n at h
  have h1 := planarEnvelopeConstant_pos (planarVerticalJet f i) n
  have h2 := planarEnvelopeConstant_pos (planarHorizontalDerivative (planarVerticalJet f i)) n
  linarith

theorem planar_profile_envelope (f : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ) (ratio R : ℝ)
    (hR : 1 ≤ R) (hr : |ratio| ≤ R) (i : Fin 3) (z : ℝ × ℝ) :
    ‖planarProfileJet f ratio i z‖ ≤ (R^2*planarProfileConstant f n)*
      (lineEnvelope 0 1 n z.1*lineEnvelope 0 1 n z.2) := by
  rw [planarProfileJet_eq,smul_apply,norm_smul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  have hp : |ratio|^i.val ≤ R^2 := (pow_le_pow_left₀ (abs_nonneg _) hr _).trans
    (pow_le_pow_right₀ hR (by omega))
  have hb := planar_profile_base_envelope f n i z
  have h := mul_le_mul hp hb (norm_nonneg _) (by positivity)
  simpa only [mul_assoc] using h

theorem planar_profile_horizontal_envelope (f : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ) (ratio R : ℝ)
    (hR : 1 ≤ R) (hr : |ratio| ≤ R) (i : Fin 3) (z : ℝ × ℝ) :
    ‖planarHorizontalDerivative (planarProfileJet f ratio i) z‖ ≤ (R^2*planarProfileConstant f n)*
      (lineEnvelope 0 1 n z.1*lineEnvelope 0 1 n z.2) := by
  rw [planarProfileJet_eq,planarHorizontalDerivative_smul,smul_apply,norm_smul,norm_pow,
    Complex.norm_real,Real.norm_eq_abs]
  have hp : |ratio|^i.val ≤ R^2 := (pow_le_pow_left₀ (abs_nonneg _) hr _).trans
    (pow_le_pow_right₀ hR (by omega))
  have hb := planar_profile_horizontal_base_envelope f n i z
  have h := mul_le_mul hp hb (norm_nonneg _) (by positivity)
  simpa only [mul_assoc] using h

theorem planar_profile_vertical_envelope (f : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ) (ratio R : ℝ)
    (hR : 1 ≤ R) (hr : |ratio| ≤ R) (i : Fin 3) (z : ℝ × ℝ) :
    ‖planarVerticalDerivative (planarProfileJet f ratio i) z‖ ≤ (R^2*planarProfileConstant f n)*
      (lineEnvelope 0 1 n z.1*lineEnvelope 0 1 n z.2) := by
  rw [planarProfileJet_eq,planarVerticalDerivative_smul,smul_apply,norm_smul,norm_pow,
    Complex.norm_real,Real.norm_eq_abs]
  have hp : |ratio|^i.val ≤ R^2 := (pow_le_pow_left₀ (abs_nonneg _) hr _).trans
    (pow_le_pow_right₀ hR (by omega))
  have hb := planar_profile_vertical_base_envelope f n i z
  have h := mul_le_mul hp hb (norm_nonneg _) (by positivity)
  simpa only [mul_assoc] using h

end LipschitzHilbert

end

end OAI
