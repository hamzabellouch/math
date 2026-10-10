import OAI.GroupTheory.PolycyclicRecognition.Geometry.ConstructExponential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothIntegralCurve

namespace OAI

/-! # Smooth one-parameter curves of the intrinsic exponential -/

noncomputable section
namespace PolycyclicRecognition

open Bundle Function
open scoped Manifold ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

theorem contMDiff_invariantVectorField_infty (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞
      (fun g => (⟨g, mulInvariantVectorField v g⟩ : TangentBundle (𝓘(ℝ, E)) G)) := by
  let z : G → TangentBundle (𝓘(ℝ, E)) G := fun g => TotalSpace.mk' E g 0
  let c : G → TangentBundle (𝓘(ℝ, E)) G := fun _ => TotalSpace.mk' E 1 v
  have hz : ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞ z :=
    contMDiff_zeroSection _ _
  have hc : ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞ c :=
    contMDiff_const
  have hj := (contMDiff_equivTangentBundleProd_symm
    (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) (n := ∞) (M := G) (M' := G))
  have hm := (contMDiff_mul (G := G) (𝓘(ℝ, E)) ∞).contMDiff_tangentMap (m := ∞) (by simp)
  have h := (hm.comp hj).comp (hz.prodMk hc)
  convert! h with g
  · simp [z, c, equivTangentBundleProd, tangentMap]
  · change mulInvariantVectorField v g =
      mfderiv ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (𝓘(ℝ, E))
        (fun p : G × G => p.1 * p.2) (g, 1) (0, v)
    have hp := mfderiv_prod_eq_add_apply (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
      (I'' := 𝓘(ℝ, E)) (p := (g, 1)) (v := (0, v))
      ((contMDiff_mul (𝓘(ℝ, E)) ∞).mdifferentiableAt (by simp))
    have hzero : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun z : G => z * 1) g)
        (0 : TangentSpace (𝓘(ℝ, E)) g) = 0 := map_zero _
    dsimp only at hp
    let w : E := mulInvariantVectorField v g
    exact (zero_add w).symm.trans
      ((congrArg (fun z : E => z + w) hzero).symm.trans hp.symm)

theorem IsGroupExponential.contMDiff_curve
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) ∞ (fun t : ℝ => Exp (t • v)) :=
  PolycyclicRecognition.IsMIntegralCurve.contMDiff (hExp.isMIntegralCurve v)
    (contMDiff_invariantVectorField_infty v)

end PolycyclicRecognition

end

end OAI
