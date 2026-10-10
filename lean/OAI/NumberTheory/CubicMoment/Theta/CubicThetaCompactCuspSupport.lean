import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompactHeight
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSmoothTests
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSectionDifferential

namespace OAI

/-! A compact smooth automorphic section vanishes uniformly high in
every arithmetic cusp. This is derived from its actual quotient support,
not imposed as a separate cusp-decay hypothesis. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaSmoothTests_cusp_support (F : cubicThetaSmoothTests) :
    ∃ C≥0, ∀ δ : SL(2,Eisenstein), ∀ p : CubicThetaPoint,
      C<cubicThetaPointHeight p → F.val.val (δ • p)=0 := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaCompact_all_cusp_height_bound F.property.2
  refine ⟨C,hC,fun δ p hp => ?_⟩
  by_contra hn
  have hs : cubicThetaQuotientMap (δ • p)∈tsupport (cubicThetaSectionNorm F) := by
    apply subset_tsupport
    change cubicThetaSectionNorm F (cubicThetaQuotientMap (δ • p))≠0
    rw [cubicThetaSectionNorm_apply]
    exact norm_ne_zero_iff.mpr hn
  have h := hbound (δ • p) hs δ⁻¹
  rw [inv_smul_smul] at h
  exact (not_lt_of_ge h) hp

lemma cubicThetaSmoothTests_cusp_function_support (F : cubicThetaSmoothTests) :
    ∃ C≥0, ∀ δ : SL(2,Eisenstein), ∀ z : ℂ, ∀ v : ℝ, 0<v → C<v →
      cubicThetaSectionFunction F (cubicThetaMobius (cubicThetaFullComplex δ) (z,v))=0 := by
  obtain ⟨C,hC,h⟩ := cubicThetaSmoothTests_cusp_support F
  refine ⟨C,hC,fun δ z v hv hCv => ?_⟩
  rw [cubicThetaSectionFunction_apply F (cubicThetaMobius_height_pos _ hv)]
  exact h δ ⟨(z,v),hv⟩ hCv

end CubicFirstMoment

end

end OAI
