import OAI.Analysis.HyperbolicCones.NormCongruence
import OAI.Analysis.HyperbolicCones.NormLimits
import OAI.Analysis.HyperbolicCones.MaxEigenvalue
import OAI.Analysis.HyperbolicCones.RankNorm
import OAI.Analysis.HyperbolicCones.OperatorEntries

namespace OAI

/-! The norm identity follows from the exact scalar thresholds and their rank-one limits. -/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix Filter Topology
namespace Paper256

theorem NormalizedPencil.norm_identity (P : NormalizedPencil)
    (u v : Vec 4) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (y : Fin 3 → ℝ) :
    choiLam (wedgeCoordinates v u) y =
      operatorNorm (P.leftProjection v * P.B y * P.rightProjection u) ^ 2 := by
  let X (w : Vec 4) (t : ℝ) : Sym 4 := 1 + (t - 1) • (1 - outerSym w)
  have hH (w : Vec 4) (hw : ‖w‖ = 1) :
      ((1 - outerSym w : Sym 4) : Mat 4 ℝ).PosSemidef :=
    one_sub_outer_posSemidef w hw
  have hX (w : Vec 4) (hw : ‖w‖ = 1) (t : ℝ) (ht : 1 ≤ t) :
      (X w t : Mat 4 ℝ).PosDef := affine_posDef _ (hH w hw) t ht
  have hS (w : Vec 4) (hw : ‖w‖ = 1) :
      Tendsto (fun t => inverseSquareRoot (X w t)) atTop (𝓝 (outer w)) := by
    have h := inverseSquareRoot_affine_tendsto (1 - outerSym w) (hH w hw)
    change Tendsto (fun t => inverseSquareRoot (X w t)) atTop
      (𝓝 (kernelProjection (1 - outer w))) at h
    simpa only [kernelProjection_one_sub_outer w hw] using h
  have hXi : Tendsto (fun t => (X v t : Mat 4 ℝ)⁻¹) atTop (𝓝 (outer v)) := by
    have h := (hS v hv).mul (hS v hv)
    rw [outer_mul_self v hv] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    exact inverseSquareRoot_sq (X v t) (hX v hv t ht)
  let A (t : ℝ) := inverseSquareRoot (X u t) * phi y (X v t : Mat 4 ℝ)⁻¹ *
    inverseSquareRoot (X u t)
  let C (t : ℝ) := inverseSquareRoot (P.D (X v t)) * P.B y *
    inverseSquareRoot (P.E (X u t))
  have hthreshold : (fun t => ‖A t‖) =ᶠ[atTop] fun t => ‖C t‖ ^ 2 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    exact P.positive_threshold (X v t) (X u t) y (hX v hv t ht) (hX u hu t ht)
      (positive_unital_map_affine_posDef P.D P.D_positive P.D_unital _ (hH v hv) t ht)
      (positive_unital_map_affine_posDef P.E P.E_positive P.E_unital _ (hH u hu) t ht)
  have hphi : Tendsto (fun t => phi y (X v t : Mat 4 ℝ)⁻¹) atTop
      (𝓝 (phi y (outer v))) :=
    (phiLinear y).continuous_of_finiteDimensional.continuousAt.tendsto.comp hXi
  have hA : Tendsto A atTop (𝓝 (choiLam (wedgeCoordinates v u) y • outer u)) := by
    have h := ((hS u hu).mul hphi).mul (hS u hu)
    simpa only [outer_mul_mul_outer, phi_rank_one] using h
  have hA' : Tendsto (fun t => ‖A t‖) atTop (𝓝 (choiLam (wedgeCoordinates v u) y)) := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (choiLam_nonnegative _ _),
      norm_outer_unit u hu, mul_one] using hA.norm
  have hD : Tendsto (fun t => inverseSquareRoot (P.D (X v t))) atTop
      (𝓝 (P.leftProjection v)) :=
    positive_unital_map_inverseSquareRoot_tendsto P.D P.D_positive P.D_unital _ (hH v hv)
  have hE : Tendsto (fun t => inverseSquareRoot (P.E (X u t))) atTop
      (𝓝 (P.rightProjection u)) :=
    positive_unital_map_inverseSquareRoot_tendsto P.E P.E_positive P.E_unital _ (hH u hu)
  have hC : Tendsto C atTop (𝓝 (P.leftProjection v * P.B y * P.rightProjection u)) :=
    matrix_mul_tendsto (matrix_mul_tendsto hD tendsto_const_nhds) hE
  have heq := tendsto_nhds_unique (hA'.congr' hthreshold) (hC.norm.pow 2)
  simpa only [operatorNorm_eq_norm] using heq

theorem NormalizedPencil.same_direction_zero (P : NormalizedPencil)
    (v : Vec 4) (hv : ‖v‖ = 1) (y : Fin 3 → ℝ) :
    P.leftProjection v * P.B y * P.rightProjection v = 0 := by
  have h := P.norm_identity v v hv hv y
  have hz : wedgeCoordinates v v = 0 := by ext i; simp [wedgeCoordinates]
  rw [hz] at h
  have hc : choiLam (0 : Fin 3 → ℝ) y = 0 := by simp [choiLam]
  rw [hc, operatorNorm_eq_norm] at h
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp h.symm)

end Paper256

end

end OAI
