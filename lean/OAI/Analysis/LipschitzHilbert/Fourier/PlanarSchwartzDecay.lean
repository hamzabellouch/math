import OAI.Analysis.LipschitzHilbert.Fourier.PlanarCovariantJet
import OAI.Analysis.LipschitzHilbert.Estimates.PolynomialEnvelope

namespace OAI

/-! Fixed product-envelope bounds for general planar Schwartz packets.
The constants are obtained from their actual weighted seminorms. -/

noncomputable section
namespace LipschitzHilbert

def planarPolynomialWeight (n : ℕ) (z : ℝ × ℝ) : ℝ :=
  (1+z.1^2)^n*(1+z.2^2)^n

theorem planarPolynomialWeight_pos (n : ℕ) (z : ℝ × ℝ) :
    0 < planarPolynomialWeight n z := by unfold planarPolynomialWeight; positivity

theorem planarPolynomialWeight_temperate (n : ℕ) :
    Function.HasTemperateGrowth (fun z : ℝ × ℝ => (planarPolynomialWeight n z : ℂ)) := by
  have hx : Function.HasTemperateGrowth (fun z : ℝ × ℝ => z.1) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasTemperateGrowth
  have hy : Function.HasTemperateGrowth (fun z : ℝ × ℝ => z.2) :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasTemperateGrowth
  unfold planarPolynomialWeight
  fun_prop

def planarEnvelopeConstant (f : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.smulLeftCLM ℂ
    (fun z => (planarPolynomialWeight n z : ℂ)) f)+1

theorem planarEnvelopeConstant_pos (f : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ) :
    0 < planarEnvelopeConstant f n := by unfold planarEnvelopeConstant; positivity

theorem planar_schwartz_envelope (f : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ) (z : ℝ × ℝ) :
    ‖f z‖ ≤ planarEnvelopeConstant f n *
      (lineEnvelope 0 1 n z.1*lineEnvelope 0 1 n z.2) := by
  have hpos := planarPolynomialWeight_pos n z
  have h := SchwartzMap.norm_le_seminorm ℝ (SchwartzMap.smulLeftCLM ℂ
    (fun z => (planarPolynomialWeight n z : ℂ)) f) z
  rw [SchwartzMap.smulLeftCLM_apply_apply (planarPolynomialWeight_temperate n),
    norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hpos] at h
  have hb : planarPolynomialWeight n z*‖f z‖ ≤ planarEnvelopeConstant f n := by
    unfold planarEnvelopeConstant
    linarith
  calc
    _ ≤ planarEnvelopeConstant f n/planarPolynomialWeight n z :=
      (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hb)
    _ = _ := by simp [planarPolynomialWeight,lineEnvelope,div_eq_mul_inv,mul_comm]

theorem planar_covariant_jet_envelope (f : SchwartzMap (ℝ × ℝ) ℂ)
    (frequency scale : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i z, ‖planarCovariantJet f frequency scale i z‖ ≤
      C*(lineEnvelope 0 1 n z.1*lineEnvelope 0 1 n z.2) := by
  let C := ∑ i : Fin 3, planarEnvelopeConstant (planarCovariantJet f frequency scale i) n
  have hC : 0 < C := Finset.sum_pos (fun i _ => planarEnvelopeConstant_pos _ _) Finset.univ_nonempty
  refine ⟨C,hC,?_⟩
  intro i z
  apply (planar_schwartz_envelope (planarCovariantJet f frequency scale i) n z).trans
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
  exact Finset.single_le_sum (fun j _ => (planarEnvelopeConstant_pos _ _).le) (Finset.mem_univ i)

end LipschitzHilbert

end

end OAI
