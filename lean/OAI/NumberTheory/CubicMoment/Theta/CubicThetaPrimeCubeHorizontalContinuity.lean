import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeBottomMean
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaComplexPointMeasure

namespace OAI

/-! Horizontal slices of the literal Hecke summands are integrable on the
actual finite cell. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaContinuous_cell_integrable (f : ℂ → ℂ) (hf : Continuous f) :
    IntegrableOn f cubicThetaHorizontalCell := by
  obtain ⟨K,hK,hsub⟩ := cubicThetaHorizontalCell_compact_container
  exact (hf.continuousOn.integrableOn_compact hK).mono_set hsub

lemma cubicThetaPrimeCubeBranch_horizontal_continuous {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (b : Eisenstein) (v : ℝ) (hv : 0<v) :
    Continuous (fun z : ℂ => cubicThetaPrimeCubeBranchPoint hp k b (cubicThetaHorizontalPoint v hv z)) := by
  unfold cubicThetaPrimeCubeBranchPoint cubicThetaHorizontalPoint
  fun_prop

lemma cubicThetaPrimeCubeUnit_horizontal_integrable {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (F : CubicThetaSection) (v : ℝ) (hv : 0<v) :
    IntegrableOn (fun z => cubicThetaPrimeCubeUnitFunctionSum hp k F.val
      (cubicThetaHorizontalPoint v hv z)) cubicThetaHorizontalCell := by
  let : Finite (Residues (p^(3-k.val))) := finite_residues (pow_ne_zero _ hp.2.ne_zero)
  let : Fintype (Residues (p^(3-k.val)))ˣ := Fintype.ofFinite _
  apply cubicThetaContinuous_cell_integrable
  unfold cubicThetaPrimeCubeUnitFunctionSum
  simp_rw [tsum_fintype]
  apply continuous_finsetSum
  intro u _
  exact continuous_const.mul (F.val.continuous.comp
    (cubicThetaPrimeCubeBranch_horizontal_continuous hp k _ v hv))

lemma cubicThetaPrimeCubeBottom_horizontal_integrable {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) :
    IntegrableOn (fun z => cubicThetaPrimeCubeBottomFunctionSum hp F.val
      (cubicThetaHorizontalPoint v hv z)) cubicThetaHorizontalCell := by
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero _ hp.2.ne_zero)
  let : Fintype (Residues (p^3)) := Fintype.ofFinite _
  apply cubicThetaContinuous_cell_integrable
  unfold cubicThetaPrimeCubeBottomFunctionSum
  simp_rw [tsum_fintype]
  apply continuous_finsetSum
  intro u _
  exact F.val.continuous.comp (cubicThetaPrimeCubeBranch_horizontal_continuous hp 0 _ v hv)

lemma cubicThetaPrimeCubeDilation_horizontal_integrable {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) :
    IntegrableOn (fun z => F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
      cubicThetaHorizontalPoint v hv z)) cubicThetaHorizontalCell := by
  apply cubicThetaContinuous_cell_integrable
  exact F.val.continuous.comp ((continuous_const_smul _).comp (cubicThetaHorizontalPoint_continuous v hv))

end CubicFirstMoment

end

end OAI
