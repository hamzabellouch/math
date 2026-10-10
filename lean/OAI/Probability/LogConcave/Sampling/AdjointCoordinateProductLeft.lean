import Mathlib
import OAI.Probability.LogConcave.Sampling.TensorVector

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace
open TensorEnergy

lemma adjointCoordinate_product_left {d e : ℕ} {H f : Point d → ℝ} {G : Point e → ℝ}
    (hH : Differentiable ℝ H) (hG : Differentiable ℝ G) (hf : Differentiable ℝ f)
    (i : Fin d) (y : Point (d+e)) :
    adjointCoordinate (productPotential H G) (EuclideanSpace.basisFun (Fin (d+e)) ℝ (i.castAdd e))
      (fun z => f (productPointEquiv d e z).1) y=
      adjointCoordinate H (EuclideanSpace.basisFun (Fin d) ℝ i) f (productPointEquiv d e y).1 := by
  let L := coordinateProjection (leftCoordinates d e)
  have he : (fun z => f (productPointEquiv d e z).1)=(fun z => f (L z)) := by
    funext z; rw [coordinateProjection_left]
  unfold adjointCoordinate
  rw [he,productPotential_directional_left hH hG,directional_comp_linear hf L]
  have hb := coordinateProjection_basis_in (leftCoordinates d e) i
  change L (EuclideanSpace.basisFun (Fin (d+e)) ℝ (i.castAdd e)) = _ at hb
  rw [hb]
  simp only [L,coordinateProjection_left]

lemma adjointCoordinate_product_right {d e : ℕ} {H f : Point d → ℝ} {G : Point e → ℝ}
    (hH : Differentiable ℝ H) (hG : Differentiable ℝ G) (hf : Differentiable ℝ f)
    (i : Fin e) (y : Point (d+e)) :
    adjointCoordinate (productPotential H G) (EuclideanSpace.basisFun (Fin (d+e)) ℝ (i.natAdd d))
      (fun z => f (productPointEquiv d e z).1) y=
      directional (EuclideanSpace.basisFun (Fin e) ℝ i) G (productPointEquiv d e y).2*
        f (productPointEquiv d e y).1 := by
  let L := coordinateProjection (leftCoordinates d e)
  have he : (fun z => f (productPointEquiv d e z).1)=(fun z => f (L z)) := by
    funext z; rw [coordinateProjection_left]
  unfold adjointCoordinate
  rw [he,productPotential_directional_right hH hG,directional_comp_linear hf L]
  have hb := congrArg Prod.fst (productPointEquiv_basis_right (d:=d) i)
  rw [←coordinateProjection_left] at hb
  change L _=0 at hb
  rw [hb]
  simp only [directional,map_zero,neg_zero,zero_add,L,coordinateProjection_left]

lemma jointSkewEntry_LL {d : ℕ} (K : Point d → Point d →L[ℝ] Point d) (s : ℝ) (i j : Fin d) :
    jointSkewEntry K s (i.castAdd d) (j.castAdd d)=fun _ => 0 := by
  funext y; simp only [jointSkewEntry,Fin.addCases_left,mul_zero]
lemma jointSkewEntry_RR {d : ℕ} (K : Point d → Point d →L[ℝ] Point d) (s : ℝ) (i j : Fin d) :
    jointSkewEntry K s (i.natAdd d) (j.natAdd d)=fun _ => 0 := by
  funext y; simp only [jointSkewEntry,Fin.addCases_right,mul_zero]
lemma jointSkewEntry_LR {d : ℕ} (K : Point d → Point d →L[ℝ] Point d) (s : ℝ) (i j : Fin d) :
    jointSkewEntry K s (i.castAdd d) (j.natAdd d)=fun y => s⁻¹*
      inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ j)
        (K (productPointEquiv d d y).1 (EuclideanSpace.basisFun (Fin d) ℝ i)) := by
  funext y; simp only [jointSkewEntry,Fin.addCases_left,Fin.addCases_right]
lemma jointSkewEntry_RL {d : ℕ} (K : Point d → Point d →L[ℝ] Point d) (s : ℝ) (i j : Fin d) :
    jointSkewEntry K s (i.natAdd d) (j.castAdd d)=fun y => (-s⁻¹)*
      inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
        (K (productPointEquiv d d y).1 (EuclideanSpace.basisFun (Fin d) ℝ j)) := by
  funext y; simp only [jointSkewEntry,Fin.addCases_left,Fin.addCases_right,mul_neg,neg_mul]
end LogConcaveSampling

end

end

end

end OAI
