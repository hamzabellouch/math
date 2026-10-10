import Mathlib
import OAI.Analysis.Conductivity.Flux.CollarCartesianDifferential

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

def sourceCollarOpenBox : Set (Fin 3 → ℝ) :=
  {x | (-(1:ℝ)/100 < x 0 ∧ x 0 < 1/100) ∧ |x 1|<1 ∧ |x 2|<1}

lemma isOpen_sourceCollarOpenBox : IsOpen sourceCollarOpenBox := by
  exact ((isOpen_lt continuous_const (continuous_apply 0)).inter
    (isOpen_lt (continuous_apply 0) continuous_const)).inter
    ((isOpen_lt (continuous_apply 1).abs continuous_const).inter
      (isOpen_lt (continuous_apply 2).abs continuous_const))

lemma sourceCollarOpenBox_subset : sourceCollarOpenBox ⊆
    sourceExtendedBox (-(1:ℝ)/100) (1/100) := by
  intro x hx
  exact mem_sourceExtendedBox.mpr ⟨⟨hx.1.1.le,hx.1.2.le⟩,hx.2.1.le,hx.2.2.le⟩

def sourceCollarTangentEquiv (i j : Fin 4) (x : Fin 3 → ℝ)
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ) :=
  (LinearMap.equivOfDetNeZero (Matrix.toLin' (sourceCollarJacobian i j x))
    (by rw [LinearMap.det_toLin']; exact sourceCollarJacobian_extended_ne_zero i j hx)).toContinuousLinearEquiv

lemma sourceCollarTangentEquiv_apply (i j : Fin 4) (x : Fin 3 → ℝ)
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) (v : Fin 3 → ℝ) :
    sourceCollarTangentEquiv i j x hx v = sourceCollarJacobian i j x *ᵥ v := rfl

lemma sourceCollarPiece_hasStrictFDeriv (i j : Fin 4) (x : Fin 3 → ℝ)
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    HasStrictFDerivAt (sourceCollarPiece i j) (sourceCollarTangentEquiv i j x hx).toContinuousLinearMap
      x := by
  have hf := (sourceCollarPiece_contDiff i j).hasStrictFDerivAt (x:=x) (by simp)
  rw [(sourceCollarPiece_hasFDeriv i j x).fderiv] at hf
  exact hf

lemma sourceCollarInverse_eventually_left (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) :
    ∀ᶠ y in 𝓝 x,sourceCollarInverse i j (sourceCollarPiece i j y)=y := by
  filter_upwards [isOpen_sourceCollarOpenBox.mem_nhds hx] with y hy
  exact sourceCollarInverse_left_pos i j
    (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/50)
      (sourceCollarRadius_extended j ⟨hy.1.1.le,hy.1.2.le⟩ hy.2.2.le).1)
    (by linarith [hy.1.2]) hy.2.1.le hy.2.2.le

lemma sourceCollarInverse_hasStrictFDeriv (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) :
    HasStrictFDerivAt (sourceCollarInverse i j)
      (sourceCollarTangentEquiv i j x (sourceCollarOpenBox_subset hx)).symm.toContinuousLinearMap
      (sourceCollarPiece i j x) :=
  (sourceCollarPiece_hasStrictFDeriv i j x (sourceCollarOpenBox_subset hx)).to_local_left_inverse
    (sourceCollarInverse_eventually_left i j hx)

lemma sourceCollarPiece_map_nhds (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) :
    Filter.map (sourceCollarPiece i j) (𝓝 x)=𝓝 (sourceCollarPiece i j x) :=
  (sourceCollarPiece_hasStrictFDeriv i j x (sourceCollarOpenBox_subset hx)).map_nhds_eq_of_equiv

lemma sourceCollarInverse_eventually_right (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) :
    ∀ᶠ y in 𝓝 (sourceCollarPiece i j x),sourceCollarPiece i j (sourceCollarInverse i j y)=y := by
  rw [←sourceCollarPiece_map_nhds i j hx,Filter.eventually_map]
  filter_upwards [sourceCollarInverse_eventually_left i j hx] with y hy
  rw [hy]

end ScalarConductivity

end

end OAI
