import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.Coordinates

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local instance : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

lemma coordinateChristoffel_smul_left (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x u v : E) (c : ℝ) :
    coordinateChristoffel g x (c • u) v = c • coordinateChristoffel g x u v := by
  unfold coordinateChristoffel
  rw [←map_smul]
  congr 1
  ext w
  simp only [smul_apply,map_smul,sub_apply,add_apply,flip_apply,smul_eq_mul]
  ring

lemma coordinateChristoffel_smul_right (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x u v : E) (c : ℝ) :
    coordinateChristoffel g x u (c • v) = c • coordinateChristoffel g x u v := by
  unfold coordinateChristoffel
  rw [←map_smul]
  congr 1
  ext w
  simp only [smul_apply,map_smul,sub_apply,add_apply,flip_apply,smul_eq_mul]
  ring
end WeakMTWTransport

end

end OAI
