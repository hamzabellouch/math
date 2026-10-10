import OAI.Geometry.SurfaceImmersion.Correction.PolynomialFrameEnvelope

namespace OAI

/-! Convert geometric lower margins into the reciprocal bounds used by the
quantitative reconstruction and normal-frame estimates. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates

lemma norm_le_sqrt_dot_self (V : RVec 4) : ‖V‖ ≤ Real.sqrt (V ⬝ᵥ V) := by
  have hd : 0 ≤ V ⬝ᵥ V := Finset.sum_nonneg fun i _ => mul_self_nonneg (V i)
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro i
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hd,Real.norm_eq_abs,sq_abs]
  simpa only [pow_two,dotProduct] using
    (Finset.single_le_sum (fun j _ => mul_self_nonneg (V j)) (Finset.mem_univ i))

lemma norm_inv_dot_self_le {V : RVec 4} {b : ℝ} (hb : 0 < b) (hV : b ≤ ‖V‖) :
    ‖(V ⬝ᵥ V)⁻¹‖ ≤ (b^2)⁻¹ := by
  have hd : 0 ≤ V ⬝ᵥ V := Finset.sum_nonneg fun i _ => mul_self_nonneg (V i)
  have hs : b ≤ Real.sqrt (V ⬝ᵥ V) := hV.trans (norm_le_sqrt_dot_self V)
  have hsq : b^2 ≤ V ⬝ᵥ V := by
    nlinarith [Real.sq_sqrt hd]
  rw [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hd)]
  exact (inv_le_inv₀ ((sq_pos_of_pos hb).trans_le hsq) (sq_pos_of_pos hb)).mpr hsq

theorem frame_bounds_of_geometric_margins (m : ℕ) :
    ∃ d : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ {U : Set Base} {F : RField 4}, ContDiff ℝ ∞ F → RealModeDomain F U →
      ∀ {s B c b : ℝ}, 0 < s → 1 ≤ B → 0 < c → 0 < b →
      c⁻¹ ≤ B → (b^2)⁻¹ ≤ B → WeightedBound U s m B (realTwoJet F) →
      (∀ x ∈ U, c ≤ NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x)) →
      (∀ x ∈ U, b ≤ ‖realSecond F x‖) →
      ReconstructionCoefficientBound (fun x => complexify (F x)) U s m (A*B^d) ∧
      WeightedBound U s m (A*B^d) (freeNormal F) := by
  obtain ⟨d,A,hA,hbound⟩ := polynomial_frame_envelope m
  refine ⟨d,A,hA,?_⟩
  intro U F hF hU s B c b hs hB hc hb hcB hbB hjet hG hN
  apply hbound hF hU hs hB hjet
  · intro x hx
    have hg := hc.trans_le (hG x hx)
    rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hg)]
    exact ((inv_le_inv₀ hg hc).mpr (hG x hx)).trans hcB
  · intro x hx
    exact (norm_inv_dot_self_le hb (hN x hx)).trans hbB

end ClosedSurfaceR4.RealModes

end

end OAI
