import OAI.Geometry.NodalSets.Charts.RoundCotangentSmooth
import OAI.Geometry.NodalSets.Charts.SphereLocalLimitGluing
import OAI.Geometry.NodalSets.Coefficients.CoefficientAmbientReconstruction
import OAI.Geometry.NodalSets.SmoothLimit.SphereSummableChartLimit

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Filter
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
local instance summablePairTangentNormedGroup (x : Base) : NormedAddCommGroup (TangentSpace (𝓡 4) x) :=
  inferInstanceAs (NormedAddCommGroup BaseModel)
local instance summablePairTangentNormedSpace (x : Base) : NormedSpace ℝ (TangentSpace (𝓡 4) x) :=
  inferInstanceAs (NormedSpace ℝ BaseModel)
local instance summablePairCotangentNormedGroup (x : Base) : NormedAddCommGroup (SphereCotangent x) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance summablePairCotangentNormedSpace (x : Base) : NormedSpace ℝ (SphereCotangent x) :=
  ContinuousLinearMap.toNormedSpace

lemma intrinsicChartCoefficient_tendsto_of_pairings (d : ℕ → SphereEnergyData)
    (A : IntrinsicTensor) (rho : Base → ℝ)
    (hA : ∀ x alpha beta, Tendsto (fun n ↦ (d n).tensor x alpha beta)
      atTop (𝓝 (A x alpha beta)))
    (hr : ∀ x, Tendsto (fun n ↦ (d n).density x) atTop (𝓝 (rho x)))
    (p : Base) (z : BaseModel) :
    Tendsto (fun n ↦ intrinsicChartCoefficient (d n).tensor (d n).density p z)
      atTop (𝓝 (intrinsicChartCoefficient A rho p z)) := by
  apply Tendsto.prodMk_nhds _ (hr _)
  unfold matrixContravariant
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro j hj
  exact (hA _ _ _).smul tendsto_const_nhds

theorem sphere_summable_smooth_pair (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ interior sphereAtlasCore,
      (extChartAt (𝓡 4) p).symm z=x)
    (d : ℕ → SphereEnergyData)
    (hd : ∀ n, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (d n).density)
    (hseq : ∀ J, Summable (fun n ↦ sphereCoefficientDistance P J
      (d n).tensor (d n).density (d (n+1)).tensor (d (n+1)).density)) :
    ∃ (A : IntrinsicTensor) (rho : Base → ℝ), IntrinsicTensorSmooth A ∧
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho ∧
      (∀ x alpha beta, Tendsto (fun n ↦ (d n).tensor x alpha beta)
        atTop (𝓝 (A x alpha beta))) ∧
      (∀ x, Tendsto (fun n ↦ (d n).density x) atTop (𝓝 (rho x))) := by
  classical
  choose c hc ht using (fun p : P ↦ sphere_summable_chart_limit P d hd hseq p.val p.property)
  have hentry (i j : Fin 5) : ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧
      ∀ x, Tendsto (fun n ↦ intrinsicAmbientMatrix (d n).tensor x i j) atTop (𝓝 (v x)) := by
    apply sphere_local_limit_gluing P hcover
      (fun n x ↦ intrinsicAmbientMatrix (d n).tensor x i j)
    intro p hp
    let q : P := ⟨p,hp⟩
    refine ⟨coefficientAmbientEntry p (c q) i j,
      coefficientAmbientEntry_smoothOn p (c q) (hc q) i j,?_⟩
    intro z hz
    have h := ((sphereChartAmbientCovector p (EuclideanSpace.basisFun (Fin 5) ℝ i) z).continuous.tendsto _).comp
      (((ContinuousLinearMap.apply ℝ BaseModel
        (sphereChartAmbientCovector p (EuclideanSpace.basisFun (Fin 5) ℝ j) z)).continuous.tendsto _).comp
        (continuous_fst.tendsto _ |>.comp (ht q z hz)))
    have hh := h.add (tendsto_const_nhds (x :=
      (((extChartAt (𝓡 4) p).symm z : AmbientBase) i) *
        (((extChartAt (𝓡 4) p).symm z : AmbientBase) j)))
    change Tendsto (fun n ↦ coefficientAmbientEntry p
      (intrinsicChartCoefficient (d n).tensor (d n).density p) i j z) atTop
      (𝓝 (coefficientAmbientEntry p (c q) i j z)) at hh
    simpa only [coefficientAmbientEntry_intrinsic] using hh
  choose B hB hBt using hentry
  obtain ⟨rho,hr,hrt⟩ := sphere_local_limit_gluing P hcover (fun n ↦ (d n).density) (by
    intro p hp
    refine ⟨fun z ↦ (c ⟨p,hp⟩ z).2,(hc ⟨p,hp⟩).snd,?_⟩
    intro z hz
    exact continuous_snd.tendsto _ |>.comp (ht ⟨p,hp⟩ z hz))
  let A : IntrinsicTensor := fun x ↦ bilinearPullback
    (ambientMatrixForm (fun i j ↦ B i j x)) (sphereCotangentRepresentative x)
  have hAs : IntrinsicTensorSmooth A := smooth_bilinear_pullback
    (fun x ↦ ambientMatrixForm (fun i j ↦ B i j x)) sphereCotangentRepresentative
    (ambientMatrixForm_smooth _ hB) sphereCotangentRepresentative_smooth
  refine ⟨A,rho,hAs,hr,?_,hrt⟩
  intro x alpha beta
  have h (n : ℕ) : (d n).tensor x alpha beta =
      ambientMatrixForm (intrinsicAmbientMatrix (d n).tensor x)
        (sphereCotangentRepresentative x alpha) (sphereCotangentRepresentative x beta) := by
    rw [intrinsicAmbientMatrix_pairing,sphereCotangentRepresentative_restriction,
      sphereCotangentRepresentative_restriction,sphereCotangentRepresentative_orthogonal,
      zero_mul,add_zero]
  simp only [h,A,bilinearPullback_apply,ambientMatrixForm_apply]
  erw [ambientMatrixForm_apply]
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro j hj
  exact (tendsto_const_nhds.mul (hBt i j x)).mul tendsto_const_nhds

end
end Yau.Target

end OAI
