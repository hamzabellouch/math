import OAI.Analysis.LiebThirring.EigenvalueSum

namespace OAI


noncomputable section
namespace SharpLiebThirring.OperatorProof
open MeasureTheory Set
open scoped Topology ENNReal

/-- Retain the largest weight of a single negative eigenvalue of the actual
operator. The supremum of the empty family is zero. -/
def oneEigenvalueMoment (γ : ℝ) (A : L2C →ₗ.[ℂ] L2C) : ℝ≥0∞ :=
  ⨆ (f : L2C) (e : ℝ) (_ : inner ℂ f f = 1)
    (_ : e < 0 ∧ IsOperatorEigenfunction A e f), (ENNReal.ofReal |e|)^γ

lemma oneStateMoment_eq_oneEigenvalueMoment {W : ℝ → ℝ} {A : L2C →ₗ.[ℂ] L2C}
    (hA : IsAssociated W A) (γ : ℝ) : oneStateMoment γ W = oneEigenvalueMoment γ A := by
  apply le_antisymm
  · unfold oneStateMoment
    refine iSup_le (fun u ↦ iSup_le (fun k ↦ iSup_le (fun hu ↦ iSup_le (fun hk ↦ ?_))))
    let f := u.val_memLp.toLp u.val
    have hf : inner ℂ f f = 1 := by simpa only [f,← l2Pairing_eq_inner] using hu
    have he : -(k^2) < 0 ∧ IsOperatorEigenfunction A (-(k^2)) f := by
      refine ⟨neg_neg_of_pos (sq_pos_of_pos hk.1),?_⟩
      simpa only [IsOperatorEigenfunction,f,Complex.ofReal_neg] using
        ((negativeEigenfunction_iff_operator hA k u).mp hk).2
    have hle : (ENNReal.ofReal |-(k^2)|)^γ ≤ oneEigenvalueMoment γ A :=
      le_iSup_of_le f (le_iSup_of_le (-(k^2)) (le_iSup_of_le hf (le_iSup_of_le he le_rfl)))
    simpa only [energy_weight _ γ hk.1.le] using hle
  · unfold oneEigenvalueMoment
    refine iSup_le (fun f ↦ iSup_le (fun e ↦ iSup_le (fun hf ↦ iSup_le (fun he ↦ ?_))))
    obtain ⟨u,hu,hq⟩ := (hA f ((e:ℂ) • f)).mp he.2
    let k := Real.sqrt (-e)
    have hk : 0 < k := Real.sqrt_pos.mpr (neg_pos.mpr he.1)
    have hks : -(k^2) = e := by
      rw [show k^2 = -e from Real.sq_sqrt (le_of_lt (neg_pos.mpr he.1)),neg_neg]
    have hne : IsNegativeEigenfunction W k u := by
      rw [negativeEigenfunction_iff_operator hA]
      refine ⟨hk,?_⟩
      have hc : -(↑(k^2):ℂ) = (e:ℂ) := by exact_mod_cast hks
      simpa only [IsOperatorEigenfunction,hc,hu] using he.2
    have hon : l2Pairing u u = 1 := by rw [l2Pairing_eq_inner,hu]; exact hf
    have hle : (ENNReal.ofReal k)^(2*γ) ≤ oneStateMoment γ W :=
      le_iSup_of_le u (le_iSup_of_le k (le_iSup_of_le hon (le_iSup_of_le hne le_rfl)))
    rw [← hks,energy_weight _ _ hk.le]
    exact hle

end SharpLiebThirring.OperatorProof

end

end OAI
