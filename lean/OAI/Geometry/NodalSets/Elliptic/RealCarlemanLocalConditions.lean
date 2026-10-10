import OAI.Geometry.NodalSets.Elliptic.CompactParameterEllipticityLemmas
import OAI.Geometry.NodalSets.Elliptic.RealTransportQuadratic

namespace OAI

namespace Yau.Geometry
open Matrix Metric
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def realTransportBilinear (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord) (x : Yau.Jets.Coord) :
    Yau.Jets.Coord →L[ℝ] Yau.Jets.Coord →L[ℝ] ℝ :=
  ∑ i, ∑ j, ∑ k,
    ((2*B x i j*Yau.coordPartial (fun y ↦ V y k) x i) •
      ((ContinuousLinearMap.proj k).smulRight (ContinuousLinearMap.proj j)) -
    (V x k*Yau.coordPartial (fun y ↦ B y i j) x k) •
      ((ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj j)))

lemma realTransportBilinear_diagonal (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord) (x xi : Yau.Jets.Coord) :
    realTransportBilinear B V x xi xi = realTransportQuadratic B V x xi := by
  simp [realTransportBilinear,realTransportQuadratic,mul_assoc]

lemma realTransportBilinear_continuous (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) : Continuous (realTransportBilinear B V) := by
  apply continuous_finsetSum; intro i _
  apply continuous_finsetSum; intro j _
  apply continuous_finsetSum; intro k _
  exact ((((continuous_const.mul (hB i j).continuous).mul
    (Yau.real_coordPartial_smooth _ (hV k) i).continuous).smul continuous_const)).sub
    (((hV k).continuous.mul (Yau.real_coordPartial_smooth _ (hB i j) k).continuous).smul continuous_const)

theorem real_carleman_local_conditions (gamma q : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0) (hq : ContDiff ℝ ∞ q)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) (x0 : Yau.Jets.Coord) (s : ℝ)
    (hquad : ∀ xi : Yau.Jets.Coord, xi ≠ 0 →
      0 < realTransportQuadratic B V x0 xi+s*coordMatrixForm (B x0) xi xi)
    (hweight : 0 < Yau.pairing q V x0-s*q x0) :
    ∃ r > 0, ∃ a > 0, ∃ b > 0, ∃ C > 0, ∀ x ∈ ball x0 r,
      (∀ xi : Yau.Jets.Coord, a*(∑ i, (xi i)^2) ≤
        realTransportQuadratic B V x xi+s*coordMatrixForm (B x) xi xi) ∧
      b ≤ Yau.pairing q V x-s*q x ∧
      realWeightedElliptic gamma B (Yau.weightedDiv gamma V) x ≤ C := by
  let g := fun x ↦ realTransportBilinear B V x+s • coordMatrixForm (B x)
  have hgc : Continuous g := (realTransportBilinear_continuous B V hB hV).add
    ((coordMatrixForm_continuous B (fun i j ↦ (hB i j).continuous)).const_smul s)
  have hgp (xi : Yau.Jets.Coord) (hxi : xi ≠ 0) : 0 < g x0 xi xi := by
    simpa only [g,_root_.add_apply,_root_.smul_apply,smul_eq_mul,realTransportBilinear_diagonal] using hquad xi hxi
  obtain ⟨r0,hr0,a,ha,hqa⟩ := local_bilinear_coercivity g hgc x0 hgp
  let F := fun x ↦ Yau.pairing q V x-s*q x
  have hF : Continuous F := (Yau.pairing_smooth hq hV).continuous.sub (continuous_const.mul hq.continuous)
  have ho : IsOpen {x | F x0/2 < F x} := isOpen_lt continuous_const hF
  obtain ⟨r1,hr1,hrF⟩ := Metric.isOpen_iff.mp ho x0 (by change F x0/2 < F x0; dsimp [F]; linarith only [hweight])
  let r := min r0 r1
  have hr : 0 < r := lt_min hr0 hr1
  have hR := realWeightedElliptic_smooth gamma B (Yau.weightedDiv gamma V) hg hgn hB
    (Yau.weightedDiv_smooth hg hgn hV)
  obtain ⟨C,hC,hCB⟩ := ((isCompact_closedBall x0 r).image hR.continuous).isBounded.exists_pos_norm_le
  refine ⟨r,hr,a,ha,F x0/2,by dsimp [F]; positivity,C,hC,?_⟩
  intro x hx
  have hx0 : x ∈ ball x0 r0 := mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hx) (min_le_left _ _))
  have hx1 : x ∈ ball x0 r1 := mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hx) (min_le_right _ _))
  refine ⟨?_,(hrF hx1).le,?_⟩
  · intro xi
    simpa only [g,_root_.add_apply,_root_.smul_apply,smul_eq_mul,realTransportBilinear_diagonal] using hqa x hx0 xi
  · exact (le_abs_self _).trans (hCB _ ⟨x,mem_closedBall.mpr (le_of_lt (mem_ball.mp hx)),rfl⟩)

end
end Yau.Geometry

end OAI
