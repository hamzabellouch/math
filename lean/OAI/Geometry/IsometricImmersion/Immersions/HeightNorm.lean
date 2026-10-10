import OAI.Geometry.IsometricImmersion.Curvature.GaussFormula
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
open scoped ContDiff BigOperators Matrix
namespace SmoothLocal.Geometry

theorem height_normal_tangent_norm {g : MetricField} {F : Coord → Ambient}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    (hU : IsOpen U) {p : Coord} (hp : p ∈ U) {n : Ambient}
    (hn : IsUnitNormalAt F n p) (e : Ambient) :
    covectorNormSq g (height F e) p + (inner ℝ n e) ^ 2 = inner ℝ e e := by
  let d : Coord := fun i => coordPartial i (height F e) p
  let c : Coord := (g p)⁻¹ *ᵥ d
  let T : Ambient := fderiv ℝ F p c
  have hgc : g p *ᵥ c = d := by
    dsimp only [c]
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (hg.2 p hp).isUnit),
      Matrix.one_mulVec]
  have hdF : DifferentiableAt ℝ F p :=
    ((hF.1 p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have horth (i : Fin 2) : inner ℝ (coordPartial i F p) (e - T) = 0 := by
    rw [inner_sub_right]
    have he : inner ℝ (coordPartial i F p) e = d i := (partial_height hdF e i).symm
    rw [he]
    have ht := hF.2 p hp (Pi.single i 1) c
    have ht' : inner ℝ (coordPartial i F p) T = d i := by
      simpa only [hgc, single_one_dotProduct, coordPartial, T] using ht
    rw [ht', sub_self]
  have hnT : inner ℝ n T = 0 := by
    rw [real_inner_comm]
    exact hn.2 c
  have hdecomp := normal_eq_inner_smul_of_independent_tangents
    (fun i => coordPartial i F p) (isometric_tangents_independent hg hF hp)
    n (e - T) hn.1 (fun i => hn.2 (Pi.single i 1)) horth
  rw [inner_sub_right, hnT, sub_zero] at hdecomp
  have hT : T = e - (inner ℝ n e) • n := by
    apply eq_sub_iff_add_eq.mpr
    have h := (sub_eq_iff_eq_add).mp hdecomp
    simpa only [add_comm] using h.symm
  have hnorm : inner ℝ T T = covectorNormSq g (height F e) p := by
    calc
      inner ℝ T T = c ⬝ᵥ (g p *ᵥ c) := hF.2 p hp c c
      _ = c ⬝ᵥ d := by rw [hgc]
      _ = covectorNormSq g (height F e) p := by
        simp only [c, d, Matrix.mulVec, dotProduct, covectorNormSq, inverseMetric,
          Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [← hnorm, hT]
  exact SmoothLocal.normal_tangent_identity e n hn.1

end SmoothLocal.Geometry

end

end OAI
