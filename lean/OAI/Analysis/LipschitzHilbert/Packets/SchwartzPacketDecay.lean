import OAI.Analysis.LipschitzHilbert.Packets.PolynomialPacket
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

namespace OAI

/-! Obtain the finite packet decay orders directly from Schwartz
seminorms, including the first two vertical derivatives. -/

noncomputable section
namespace LipschitzHilbert

def schwartzEnvelopeConstant (f : SchwartzMap ℝ ℂ) (n : ℕ) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 (polynomialLocalization 0 1 n f)+1

theorem schwartzEnvelopeConstant_pos (f : SchwartzMap ℝ ℂ) (n : ℕ) :
    0 < schwartzEnvelopeConstant f n := by
  unfold schwartzEnvelopeConstant
  positivity

theorem schwartz_lineEnvelope_bound (f : SchwartzMap ℝ ℂ) (n : ℕ) (x : ℝ) :
    ‖f x‖ ≤ schwartzEnvelopeConstant f n*lineEnvelope 0 1 n x := by
  have hp : 0 < polynomialWeight 0 1 n x :=
    zero_lt_one.trans_le (polynomialWeight_one_le _ _ _ _)
  have h := SchwartzMap.norm_le_seminorm ℝ (polynomialLocalization 0 1 n f) x
  rw [polynomialLocalization_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hp] at h
  have hbound : polynomialWeight 0 1 n x*‖f x‖ ≤ schwartzEnvelopeConstant f n := by
    dsimp [schwartzEnvelopeConstant]
    linarith
  calc
    ‖f x‖ ≤ schwartzEnvelopeConstant f n/polynomialWeight 0 1 n x :=
      (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hbound)
    _ = schwartzEnvelopeConstant f n*lineEnvelope 0 1 n x := by
      simp [polynomialWeight, lineEnvelope, div_eq_mul_inv]

def schwartzVerticalJet (f : SchwartzMap ℝ ℂ) (i : Fin 3) : SchwartzMap ℝ ℂ :=
  if i=0 then f else if i=1 then SchwartzMap.derivCLM ℂ ℂ f
    else SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f)

theorem schwartz_vertical_jet_envelope (f : SchwartzMap ℝ ℂ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i x,
      ‖schwartzVerticalJet f i x‖ ≤ C*lineEnvelope 0 1 n x := by
  let C := ∑ i : Fin 3, schwartzEnvelopeConstant (schwartzVerticalJet f i) n
  have hpos : 0 < C := Finset.sum_pos (fun i _ => schwartzEnvelopeConstant_pos _ _) Finset.univ_nonempty
  refine ⟨C,hpos,?_⟩
  intro i x
  apply (schwartz_lineEnvelope_bound (schwartzVerticalJet f i) n x).trans
  apply mul_le_mul_of_nonneg_right _ (lineEnvelope_nonneg _ _ _ _)
  exact Finset.single_le_sum (fun j _ => (schwartzEnvelopeConstant_pos _ _).le) (Finset.mem_univ i)

end LipschitzHilbert

end

end OAI
