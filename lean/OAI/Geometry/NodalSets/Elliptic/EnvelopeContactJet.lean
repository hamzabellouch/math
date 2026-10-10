import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import OAI.Geometry.NodalSets.Elliptic.ContactTaylor
import OAI.Geometry.NodalSets.Elliptic.PhaseActualJet

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section

lemma coord_expansion (x : Coord) : x = ∑ i, x i • Pi.single i (1:ℝ) := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply, mul_ite]

def envelopeHessian (S : Coord → ℝ) (i j : Fin 4) : ℝ :=
  fderiv ℝ (fderiv ℝ S) 0 (Pi.single j 1) (Pi.single i 1)

lemma envelopeHessian_symmetric (S : Coord → ℝ) (hS : ContDiff ℝ ∞ S) :
    ∀ i j, envelopeHessian S i j = envelopeHessian S j i := by
  intro i j
  exact hS.contDiffAt.isSymmSndFDerivAt
    (by simp) _ _

lemma envelopeHessian_diagonal (S : Coord → ℝ) (x : Coord) :
    iteratedFDeriv ℝ 2 S 0 (fun _ ↦ x) = ∑ i, ∑ j, envelopeHessian S i j*x i*x j := by
  rw [iteratedFDeriv_two_apply]
  conv_lhs => arg 1; rw [coord_expansion x]
  conv_lhs => arg 2; rw [coord_expansion x]
  simp only [map_sum, map_smul, sum_apply, smul_apply,
    smul_eq_mul, Finset.mul_sum, envelopeHessian]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma coord_norm_sq_le (x : Coord) : ‖x‖^2 ≤ ∑ i, (x i)^2 := by
  have hs : 0 ≤ ∑ i, (x i)^2 := Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
  have hb : ‖x‖ ≤ Real.sqrt (∑ i, (x i)^2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    have hi : (x i)^2 ≤ ∑ j, (x j)^2 := Finset.single_le_sum
      (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i)
    rw [Real.norm_eq_abs]
    nlinarith [Real.sq_sqrt hs, Real.sqrt_nonneg (∑ i, (x i)^2), sq_abs (x i), abs_nonneg (x i)]
  nlinarith [Real.sq_sqrt hs, norm_nonneg x, Real.sqrt_nonneg (∑ i, (x i)^2)]

theorem retained_phase_envelope_contact (p : CPoly) (S : Coord → ℝ)
    (hS : ContDiff ℝ ∞ S) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hfirst : ∀ x : Coord, fderiv ℝ S 0 x = a*x 0)
    (hkeep : ∀ k, k ≤ 2 → homogeneousComponent k p =
      initialPhaseJet (S 0) (normalFrameVector a b)
        (normalComplexHessian a b (envelopeHessian S)) k)
    (hstrict : 0 < a^2*envelopeHessian S 0 0+b^2*envelopeHessian S 1 1) :
    (reval p 0).re-S 0 = 0 ∧
    fderiv ℝ (fun x ↦ (reval p x).re-S x) 0 = 0 ∧
    ∀ x : Coord, iteratedFDeriv ℝ 2 (fun z ↦ (reval p z).re-S z) 0 (fun _ ↦ x) ≤
      -Yau.contactEta a b (envelopeHessian S 0 0) (envelopeHessian S 1 1)*‖x‖^2 := by
  obtain ⟨h0,h1,h2⟩ := retained_normal_phase_derivatives p (S 0) a b (envelopeHessian S)
    ha hb (envelopeHessian_symmetric S hS) hkeep
  have hR : ContDiff ℝ ∞ (fun x ↦ (reval p x).re) := Complex.reCLM.contDiff.comp (reval_contDiff p)
  refine ⟨by rw [h0, sub_self], ?_, ?_⟩
  · rw [fderiv_fun_sub (hR.differentiable (by simp) 0) (hS.differentiable (by simp) 0)]
    ext x
    have hc := Complex.reCLM.hasFDerivAt.comp 0 ((reval_contDiff p).differentiable (by simp) 0).hasFDerivAt
    change fderiv ℝ (Complex.reCLM ∘ reval p) 0 x - fderiv ℝ S 0 x = 0
    rw [hc.fderiv]
    simp [h1 x, hfirst x]
  · intro x
    change iteratedFDeriv ℝ 2 ((fun z ↦ (reval p z).re) - S) 0 (fun _ ↦ x) ≤ _
    rw [iteratedFDeriv_sub_apply
      (hR.contDiffAt.of_le (by change (↑(2:ℕ∞):ℕ∞ω) ≤ ↑(⊤:ℕ∞); exact WithTop.coe_le_coe.mpr le_top))
      (hS.contDiffAt.of_le (by change (↑(2:ℕ∞):ℕ∞ω) ≤ ↑(⊤:ℕ∞); exact WithTop.coe_le_coe.mpr le_top))]
    change iteratedFDeriv ℝ 2 (Complex.reCLM ∘ reval p) 0 (fun _ ↦ x) -
      iteratedFDeriv ℝ 2 S 0 (fun _ ↦ x) ≤ _
    rw [Complex.reCLM.iteratedFDeriv_comp_left (reval_contDiff p).contDiffAt
      (by change (↑(2:ℕ∞):ℕ∞ω) ≤ ↑(⊤:ℕ∞); exact WithTop.coe_le_coe.mpr le_top)]
    change (iteratedFDeriv ℝ 2 (reval p) 0 (fun _ ↦ x)).re - _ ≤ _
    rw [h2, envelopeHessian_diagonal]
    have he := Yau.contactEta_pos ha hstrict
    have hn := mul_le_mul_of_nonneg_left (coord_norm_sq_le x) he.le
    linarith

end
end Yau.Jets

end OAI
