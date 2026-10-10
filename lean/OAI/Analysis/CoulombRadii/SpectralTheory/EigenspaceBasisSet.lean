import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
namespace Coulomb
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
noncomputable def eigenspaceBasisSet (T : E →L[ℂ] E) (z : ℂ) : Set (eigenspace T.toLinearMap z) := by
  letI : CompleteSpace (eigenspace T.toLinearMap z) :=
    (T.isClosed_eigenspace z).isComplete.completeSpace_coe
  exact (exists_hilbertBasis ℂ (eigenspace T.toLinearMap z)).choose
noncomputable def eigenspaceHilbertBasis (T : E →L[ℂ] E) (z : ℂ) :
    HilbertBasis (eigenspaceBasisSet T z) ℂ (eigenspace T.toLinearMap z) := by
  letI : CompleteSpace (eigenspace T.toLinearMap z) :=
    (T.isClosed_eigenspace z).isComplete.completeSpace_coe
  exact (exists_hilbertBasis ℂ (eigenspace T.toLinearMap z)).choose_spec.choose
noncomputable def spectralVectors (T : E →L[ℂ] E) (i : Σ z, eigenspaceBasisSet T z) : E :=
  eigenspaceHilbertBasis T i.1 i.2
lemma spectralVectors_orthonormal (T : E →L[ℂ] E) (hT : T.IsSymmetric) :
    Orthonormal ℂ (spectralVectors T) :=
  hT.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal
    (fun z => (eigenspaceHilbertBasis T z).orthonormal)
lemma spectralVectors_eigen (T : E →L[ℂ] E) (i : Σ z, eigenspaceBasisSet T z) :
    T (spectralVectors T i) = i.1 • spectralVectors T i :=
  (mem_eigenspace_iff).mp (eigenspaceHilbertBasis T i.1 i.2).property
lemma spectralVectors_orthogonal_eq_bot (T : E →L[ℂ] E)
    (hc : IsCompactOperator T) (hT : T.IsSymmetric) :
    (Submodule.span ℂ (Set.range (spectralVectors T)))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hx' : x ∈ (⨆ z, eigenspace T.toLinearMap z)ᗮ := by
    rw [←Submodule.iInf_orthogonal]
    rw [Submodule.mem_iInf]
    intro z
    rw [Submodule.mem_orthogonal']
    intro v hv
    let v' : eigenspace T.toLinearMap z := ⟨v,hv⟩
    have hs := (eigenspaceHilbertBasis T z).hasSum_repr v'
    have he : ∀ i : eigenspaceBasisSet T z,
        inner ℂ x ((eigenspaceHilbertBasis T z i : eigenspace T.toLinearMap z) : E) = 0 := by
      intro i
      exact ((Submodule.mem_orthogonal' _ _).mp hx) _
        (Submodule.subset_span (Set.mem_range.mpr ⟨⟨z,i⟩,rfl⟩))
    have hsum := (hs.mapL (eigenspace T.toLinearMap z).subtypeL).mapL (innerSL ℂ x)
    have hz : HasSum (fun _ : eigenspaceBasisSet T z => (0:ℂ)) (inner ℂ x v) := by
      simpa only [ContinuousLinearMap.map_smul,Submodule.subtypeL_apply,
        innerSL_apply_apply,he,smul_zero] using hsum
    exact hz.unique hasSum_zero
  simpa only [T.orthogonalComplement_iSup_eigenspaces_eq_bot hc hT] using hx'
noncomputable def compactSpectralBasis (T : E →L[ℂ] E)
    (hc : IsCompactOperator T) (hT : T.IsSymmetric) :
    HilbertBasis (Σ z, eigenspaceBasisSet T z) ℂ E :=
  HilbertBasis.mkOfOrthogonalEqBot (spectralVectors_orthonormal T hT)
    (spectralVectors_orthogonal_eq_bot T hc hT)
lemma compactSpectralBasis_eigen (T : E →L[ℂ] E)
    (hc : IsCompactOperator T) (hT : T.IsSymmetric) (i : Σ z, eigenspaceBasisSet T z) :
    T (compactSpectralBasis T hc hT i) = i.1 • compactSpectralBasis T hc hT i := by
  simpa only [compactSpectralBasis,HilbertBasis.coe_mkOfOrthogonalEqBot] using spectralVectors_eigen T i
omit [CompleteSpace E] in
lemma orthonormal_countable {ι : Type*} [SeparableSpace E] {v : ι → E}
    (hv : Orthonormal ℂ v) : Countable ι := by
  have hd : Pairwise (Disjoint on (fun i => Metric.ball (v i) (1/2:ℝ))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have hs : ‖v i-v j‖^2 = 2 := by
      rw [norm_sub_sq (𝕜 := ℂ), hv.1 i, hv.1 j, hv.2 hij]
      norm_num
    rw [dist_eq_norm]
    have hn := norm_nonneg (v i-v j)
    nlinarith
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨v i,by simp⟩)
lemma compactSpectralBasis_eigen_real (T : E →L[ℂ] E)
    (hc : IsCompactOperator T) (hT : T.IsSymmetric) (i : Σ z, eigenspaceBasisSet T z) :
    i.1.im = 0 := by
  have h := hT.im_inner_self_apply (compactSpectralBasis T hc hT i)
  simpa [compactSpectralBasis_eigen,inner_smul_right,inner_self_eq_norm_sq_to_K,
    (compactSpectralBasis T hc hT).orthonormal.1 i] using h
lemma compactSpectralBasis_eigen_nonneg (T : E →L[ℂ] E)
    (hc : IsCompactOperator T) (hT : T.toLinearMap.IsPositive) (i : Σ z, eigenspaceBasisSet T z) :
    0 ≤ i.1.re := by
  have h := hT.re_inner_nonneg_right (compactSpectralBasis T hc hT.1 i)
  simpa [compactSpectralBasis_eigen,inner_smul_right,inner_self_eq_norm_sq_to_K,
    (compactSpectralBasis T hc hT.1).orthonormal.1 i] using h
lemma compactSpectralBasis_eigen_le_one (T : E →L[ℂ] E)
    (hc : IsCompactOperator T) (hT : T.toLinearMap.IsPositive)
    (hI : (ContinuousLinearMap.id ℂ E-T).toLinearMap.IsPositive)
    (i : Σ z, eigenspaceBasisSet T z) : i.1.re ≤ 1 := by
  have h := hI.re_inner_nonneg_right (compactSpectralBasis T hc hT.1 i)
  change 0 ≤ RCLike.re (inner ℂ _ (_-T _)) at h
  rw [inner_sub_right,map_sub] at h
  simpa [compactSpectralBasis_eigen,inner_smul_right,inner_self_eq_norm_sq_to_K,
    (compactSpectralBasis T hc hT.1).orthonormal.1 i,sub_nonneg] using h
end Coulomb

open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate

end

end OAI
