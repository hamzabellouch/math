import OAI.Geometry.SurfaceImmersion.Correction.PolynomialReconstruction
import OAI.Geometry.SurfaceImmersion.Correction.PositivePolynomialBounds

namespace OAI

/-! A single polynomial envelope for the actual reconstruction coefficients
and free normal. Its degree is chosen before any geometric bounds. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4
open WeightedEstimates

namespace SmallModes

lemma ReconstructionCoefficientBound.mono_const {n : ℕ} {F : Field n}
    {U : Set Base} {s C D : ℝ} {m : ℕ}
    (h : ReconstructionCoefficientBound F U s m C) (hCD : C ≤ D) :
    ReconstructionCoefficientBound F U s m D :=
  ⟨⟨⟨h.xxX.mono_const hCD,h.xxY.mono_const hCD,h.xyX.mono_const hCD,
      h.xyY.mono_const hCD,h.yyX.mono_const hCD,h.yyY.mono_const hCD,
      h.ratioxx.mono_const hCD,h.ratioxy.mono_const hCD⟩,
      h.secondxx.mono_const hCD,h.secondxy.mono_const hCD⟩,
      h.dualx.mono_const hCD,h.dualy.mono_const hCD,h.dualn.mono_const hCD⟩

end SmallModes

namespace RealModes
open SmallModes

theorem polynomial_frame_envelope (m : ℕ) :
    ∃ d : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ {U : Set Base} {F : RField 4}, ContDiff ℝ ∞ F → RealModeDomain F U →
      ∀ {s B : ℝ}, 0 < s → 1 ≤ B →
      WeightedBound U s m B (realTwoJet F) →
      (∀ x ∈ U, ‖(NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹‖ ≤ B) →
      (∀ x ∈ U, ‖(realSecond F x ⬝ᵥ realSecond F x)⁻¹‖ ≤ B) →
      ReconstructionCoefficientBound (fun x => complexify (F x)) U s m (A*B^d) ∧
      WeightedBound U s m (A*B^d) (freeNormal F) := by
  obtain ⟨D,hD,hfree⟩ := polynomial_freeNormal_bound m
  obtain ⟨d,A,hA,hpoly⟩ :=
    (reconstructionBudget_polynomial m).add (freeNormalBudget_polynomial m (zero_le_one.trans hD))
  refine ⟨d,A,hA,?_⟩
  intro U F hF hU s B hs hB hb hG hN
  have hp := hpoly B hB
  have hfb : 0 ≤ freeNormalBudget m D B B := by
    unfold freeNormalBudget freeNormalInputBudget
    have hnormal := normalBudget_nonneg m (zero_le_one.trans hB) (zero_le_one.trans hB)
    unfold perpBudget minorTermBudget crossBudget dotBudget
    positivity
  have hrb := (reconstructionBudget_bounds m (zero_le_one.trans hB) (zero_le_one.trans hB)).1
  constructor
  · exact (polynomial_reconstruction_bound hF hU hs hB hB hb hG hN).mono_const
      ((le_add_of_nonneg_right hfb).trans hp.2)
  · exact (hfree hF hU hs hB hB hb hG
      (fun x hx => (le_abs_self _).trans (hN x hx))).mono_const
      ((le_add_of_nonneg_left (zero_le_one.trans hrb)).trans hp.2)

end RealModes
end ClosedSurfaceR4

end

end OAI
