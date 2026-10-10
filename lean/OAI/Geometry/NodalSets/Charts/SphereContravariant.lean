import OAI.Geometry.NodalSets.Charts.BaseChartFlux
import OAI.Geometry.NodalSets.Charts.InvariantFrameInverse

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
noncomputable section
local instance : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩

lemma sphereChartFrame_spans (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) (v : Fin 5 → ℝ)
    (hv : (fun i ↦ ((extChartAt (𝓡 4) p).symm z : AmbientBase) i) ⬝ᵥ v = 0) :
    ∃ w : Fin 4 → ℝ, sphereChartFrame p z *ᵥ w = v := by
  have hm : WithLp.toLp 2 v ∈
      (ℝ ∙ (((extChartAt (𝓡 4) p).symm z : Base) : AmbientBase))ᗮ := by
    apply (Submodule.mem_orthogonal_singleton_iff_inner_left (𝕜 := ℝ) (E := AmbientBase)).mpr
    simpa [PiLp.inner_apply,dotProduct,mul_comm] using hv
  rw [← range_mvfderiv_subtypeVal (n := 4)] at hm
  obtain ⟨u,hu⟩ := hm
  have hs := (isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 4) hz).surjective
  rw [ModelWithCorners.range_eq_univ,mfderivWithin_univ] at hs
  obtain ⟨w,hw⟩ := hs u
  refine ⟨WithLp.ofLp w,?_⟩
  rw [sphereChartFrame_mulVec]
  change (fun i ↦ (sphereAmbientDerivative _
    (mfderiv 𝓘(ℝ,BaseModel) (𝓡 4) (extChartAt (𝓡 4) p).symm z w)) i) = v
  rw [hw]
  exact congrArg WithLp.ofLp hu

lemma sphereChartFrame_invariant (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    (p : Base) {z : BaseModel} (hz : z ∈ (extChartAt (𝓡 4) p).target)
    (hrad : A *ᵥ (fun i ↦ ((extChartAt (𝓡 4) p).symm z : AmbientBase) i) =
      (fun i ↦ ((extChartAt (𝓡 4) p).symm z : AmbientBase) i)) :
    ∃ T : Matrix (Fin 4) (Fin 4) ℝ, A * sphereChartFrame p z = sphereChartFrame p z * T := by
  have he (j : Fin 4) : ∃ w : Fin 4 → ℝ,
      sphereChartFrame p z *ᵥ w = A *ᵥ (fun i ↦ sphereChartFrame p z i j) := by
    apply sphereChartFrame_spans p hz
    apply radial_orthogonal_preserved A hA.1 _ _ hrad
    have h := congrFun (sphereChartFrame_orthogonal p z) j
    simpa [mulVec,transpose_apply,dotProduct,mul_comm] using h
  choose t ht using he
  refine ⟨fun i j ↦ t j i,?_⟩
  ext i j
  exact (congrFun (ht j) i).symm

lemma sphereChart_contravariant (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    {rho : ℝ} (hr : 0 < rho) (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target)
    (hrad : A *ᵥ (fun i ↦ ((extChartAt (𝓡 4) p).symm z : AmbientBase) i) =
      (fun i ↦ ((extChartAt (𝓡 4) p).symm z : AmbientBase) i)) :
    frameContravariant A (sphereChartFrame p z) =
      rho • (sphereWeightedChartMatrix A rho p z)⁻¹ := by
  obtain ⟨T,hT⟩ := sphereChartFrame_invariant A hA p hz hrad
  exact invariant_frame_inverse A hA _ (sphereChartFrame_injective p hz) T hT hr

end
end Yau.Target

end OAI
