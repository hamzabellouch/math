import OAI.Geometry.Kahler.HartogsGaugeTransfer

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
namespace PinchedHartogs
open PlaneAlgebra PlaneAlgebra.MatrixAlgebra PlaneAlgebra.TensorAlgebra Matrix

lemma hermitianValue_pairValue (A : CMatrix) (u v : Ambient) :
    hermitianValue A u v = pairValue A (coordinates u) (coordinates v) := by
  simp only [hermitianValue, pairValue, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma realArea_positive {A : CMatrix} (hA : A.IsHermitian)
    (hpos : ∀ u : Ambient, u ≠ 0 → 0 < (hermitianValue A u u).re)
    {u v : Ambient} (hind : LinearIndependent ℝ ![u,v]) : 0 < realArea A u v := by
  have hp : (form A hA).Pos := by
    intro w hw
    have hh := hpos (coordinateEquiv.symm w) (coordinateEquiv.symm.map_ne_zero_iff.mpr hw)
    rwa [hermitianValue_pairValue, coordinates_equiv_symm] at hh
  have hi : LinearIndependent ℝ ![coordinates u,coordinates v] := by
    convert hind.map' (coordinateLinearEquiv.restrictScalars ℝ).toLinearMap
      (LinearMap.ker_eq_bot_of_injective (coordinateLinearEquiv.restrictScalars ℝ).injective) using 1
    all_goals first | rfl | (ext i; fin_cases i <;> rfl)
  have hh := (form A hA).area_pos (coordinates u) (coordinates v) hp hi
  simp only [realArea, hermitianValue_pairValue]
  exact hh

lemma metric_isHermitian {M : Set Ambient} {g : Ambient → CMatrix}
    (hg : IsKahlerMetric M g) {p : Ambient} (hp : p ∈ M) : (g p).IsHermitian := by
  ext i j
  exact (hg.2.1 p hp i j).symm

lemma curvature_continuousAt {g : Ambient → CMatrix} {p : Ambient}
    (hg : ContDiffAt ℝ 2 g p) (hdet : (g p).det ≠ 0) : ContinuousAt (curvature g) p := by
  have hcomp (i j : Fin 3) : ContDiffAt ℝ 2 (fun q => g q i j) p :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j
  have hi := (matrix_contDiffAt_inv hg hdet).continuousAt
  apply continuousAt_pi.mpr
  intro a
  apply continuousAt_pi.mpr
  intro b
  apply continuousAt_pi.mpr
  intro c
  apply continuousAt_pi.mpr
  intro d
  change ContinuousAt (fun q => -dbar (fun r => dz (fun t => g t c d) r a) q b +
    ∑ e, ∑ k, (g q)⁻¹ e k * dz (fun r => g r c e) q a * dbar (fun r => g r k d) q b) p
  apply ContinuousAt.add
  · exact (_root_.OAI.ContDiffAt.hartogs_dbar (_root_.OAI.ContDiffAt.hartogs_dz (hcomp c d) (m := 1) (by norm_num) a) (m := 0) (by norm_num) b).continuousAt.neg
  · apply tendsto_finsetSum
    intro e he
    apply tendsto_finsetSum
    intro k hk
    exact ((continuousAt_pi.mp (continuousAt_pi.mp hi e) k).mul
      (_root_.OAI.ContDiffAt.hartogs_dz (hcomp c e) (m := 1) (by norm_num) a).continuousAt).mul
      (_root_.OAI.ContDiffAt.hartogs_dbar (hcomp k d) (m := 1) (by norm_num) b).continuousAt

lemma tensorValue_continuousAt {R : Ambient → CurvatureTensor} {p : Ambient}
    (hR : ContinuousAt R p) (u v w y : Ambient) :
    ContinuousAt (fun q => tensorValue (R q) u v w y) p := by
  unfold tensorValue
  apply tendsto_finsetSum
  intro a ha
  apply tendsto_finsetSum
  intro b hb
  apply tendsto_finsetSum
  intro c hc
  apply tendsto_finsetSum
  intro d hd
  exact ((((continuousAt_pi.mp (continuousAt_pi.mp (continuousAt_pi.mp (continuousAt_pi.mp hR a) b) c) d).mul
    continuousAt_const).mul continuousAt_const).mul continuousAt_const).mul continuousAt_const

lemma hermitianValue_continuousAt {g : Ambient → CMatrix} {p : Ambient}
    (hg : ContinuousAt g p) (u v : Ambient) : ContinuousAt (fun q => hermitianValue (g q) u v) p := by
  unfold hermitianValue
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro j hj
  exact ((continuousAt_pi.mp (continuousAt_pi.mp hg i) j).mul continuousAt_const).mul continuousAt_const

lemma sectional_continuousAt {M : Set Ambient} {g : Ambient → CMatrix}
    (hM : IsOpen M) (hg : IsKahlerMetric M g) {p : Ambient} (hp : p ∈ M)
    {u v : Ambient} (hind : LinearIndependent ℝ ![u,v]) :
    ContinuousAt (fun q => sectional g q u v) p := by
  have hgs := hg.1.contDiffAt (hM.mem_nhds hp)
  have hR := curvature_continuousAt (hgs.of_le (WithTop.coe_le_coe.mpr le_top)) (kahler_metric_det_ne_zero hg hp)
  have ha : 0 < realArea (g p) u v := realArea_positive (metric_isHermitian hg hp) (hg.2.2.1 p hp) hind
  apply ContinuousAt.div
  · exact (Complex.continuous_re.continuousAt.comp (tensorValue_continuousAt hR u u v v)).sub
      (Complex.continuous_re.continuousAt.comp (tensorValue_continuousAt hR u v u v))
  · apply continuousAt_const.mul
    apply ContinuousAt.sub
    · exact (Complex.continuous_re.continuousAt.comp (hermitianValue_continuousAt hgs.continuousAt u u)).mul
        (Complex.continuous_re.continuousAt.comp (hermitianValue_continuousAt hgs.continuousAt v v))
    · exact (Complex.continuous_re.continuousAt.comp (hermitianValue_continuousAt hgs.continuousAt u v)).pow 2
  · exact mul_ne_zero (by norm_num) ha.ne'

end PinchedHartogs

end

end OAI
