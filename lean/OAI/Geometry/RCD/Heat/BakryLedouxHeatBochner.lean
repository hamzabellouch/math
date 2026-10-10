import OAI.Geometry.RCD.Heat.BakryLedouxInput
import OAI.Geometry.RCD.Sobolev.RightSlopeCorrection
import OAI.Geometry.RCD.Heat.HeatCutoffIntegral

namespace OAI

/-! # The finite-dimensional heat comparison gives weak Bochner on heat data

The extra term in EKS (4.14) is retained in the one-sided derivative.
The test has only bounded Sobolev regularity; its heat pairing is
right differentiable by the energy form, without a Laplacian of the test.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] (μ : Measure X) [μ.Regular]
  (hQ : QuadraticCheegerEnergy μ)

theorem IntegratedBakryLedoux.heat_bochner {K N : ℝ}
    (hBL : IntegratedBakryLedoux μ hQ K N) (f : Lp ℝ 2 μ) {t : ℝ} (ht : 0<t)
    (G : SobolevSpace μ hQ)
    (hG : SobolevSpace.toLp μ hQ G =ᵐ[μ] fun x =>
      (SobolevSpace.minimalSlope μ hQ (heatSobolev μ hQ t ht f) x)^2)
    (w : SobolevSpace μ hQ) (C : ℝ≥0)
    (hw0 : 0≤SobolevSpace.toLp μ hQ w)
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x|≤C) :
    let F := heatSobolev μ hQ t ht f
    let D := heatSobolevMap μ hQ (t/2) (half_pos ht)
      (-heatGeneratorAt μ hQ (t-t/2) f)
    energyForm μ hQ G w+
      2*K*inner ℝ (SobolevSpace.toLp μ hQ w) (SobolevSpace.toLp μ hQ G)+
      2*weightedGamma μ hQ (SobolevSpace.toLp μ hQ w) F D+
      (2/N)*(∫ x, SobolevSpace.toLp μ hQ w x*(SobolevSpace.toLp μ hQ D x)^2 ∂μ)≤0 := by
  obtain ⟨c,hc,hBL⟩ := hBL
  let F := heatSobolev μ hQ t ht f
  let D := heatSobolevMap μ hQ (t/2) (half_pos ht)
    (-heatGeneratorAt μ hQ (t-t/2) f)
  let W := SobolevSpace.toLp μ hQ w
  let H := SobolevSpace.toLp μ hQ G
  let q (r : ℝ) := ∫ x, W x*(SobolevSpace.minimalSlope μ hQ
    (heatTail μ hQ (t/2) (half_pos ht) f (t+r)) x)^2 ∂μ
  let b (r : ℝ) := Real.exp (-2*K*r)*inner ℝ (heatAt μ hQ r W) H
  let j (r : ℝ) := ∫ x, W x*(heatAt μ hQ r (SobolevSpace.toLp μ hQ D) x)^2 ∂μ
  have hF : heatTail μ hQ (t/2) (half_pos ht) f t=F :=
    heatTail_eq μ hQ (t/2) (half_pos ht) f t (by linarith)
  have hWb : ∀ᵐ x ∂μ, ‖W x‖≤(C:ℝ) := by simpa only [Real.norm_eq_abs] using hw
  have hq : HasDerivAt q (2*weightedGamma μ hQ W F D) 0 := by
    have hd0 : HasDerivAt (heatTail μ hQ (t/2) (half_pos ht) f) D (t+0) := by
      simpa only [add_zero] using heatTail_hasDerivAt μ hQ (t/2) (half_pos ht) f t (by linarith)
    have hd := hd0.scomp 0 ((hasDerivAt_id (0:ℝ)).const_add t)
    simp only [one_smul] at hd
    simpa only [Function.comp_apply,add_zero,hF] using
      weighted_gradient_hasDerivAt μ hQ (Lp.aestronglyMeasurable W) hWb hd
  have hb : HasDerivWithinAt b
      ((-2*K)*inner ℝ W H-energyForm μ hQ w G) (Ici 0) 0 := by
    have he := ((hasDerivAt_id (0:ℝ)).const_mul (-2*K)).exp
    have hi := heatAt_inner_hasDerivWithinAt_zero μ hQ w G
    convert! he.hasDerivWithinAt.mul hi using 1
    simp only [W,H,id_eq,mul_zero,Real.exp_zero,one_mul,mul_one,
      heatAt_zero,one_apply_eq_self,sub_eq_add_neg]
  have hb' : Tendsto (fun r => (b r-b 0)/r) (𝓝[>] 0)
      (𝓝 ((-2*K)*inner ℝ W H-energyForm μ hQ w G)) := by
    have hh := (hasDerivWithinAt_iff_tendsto_slope' (s:=Ioi (0:ℝ)) (lt_irrefl (0:ℝ))).mp
      hb.Ioi_of_Ici
    simpa only [slope_fun_def_field,sub_zero] using hh
  have hWi : MemLp (fun x => W x) ∞ μ := memLp_top_of_bound (Lp.aestronglyMeasurable W) C hWb
  have hj := (heat_weighted_square_continuous μ hQ (SobolevSpace.toLp μ hQ D) hWi).tendsto 0
  have hj' : Tendsto j (𝓝[>] 0) (𝓝 (∫ x, W x*(SobolevSpace.toLp μ hQ D x)^2 ∂μ)) := by
    simpa only [j,heatAt_zero,one_apply_eq_self] using hj.mono_left nhdsWithin_le_nhds
  have hcorr := (hc.mul hj').const_mul (2/N)
  simp only [one_mul] at hcorr
  have hq0 : q 0=inner ℝ W H := by
    dsimp only [q]
    rw [add_zero,hF,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hG] with x hx
    change H x=(SobolevSpace.minimalSlope μ hQ F x)^2 at hx
    simp only [Real.inner_apply,hx]
  have hb0 : b 0=inner ℝ W H := by simp only [b,mul_zero,Real.exp_zero,one_mul,heatAt_zero,one_apply_eq_self]
  have hineq (r : ℝ) (hr : 0<r) : q r+r*((2/N)*(c r*j r))≤b r := by
    have hh := hBL F (SobolevSpace.toLp μ hQ D)
      (heatTail_weak_laplacian μ hQ t ht f) W C hw0 hw r hr
    have heF : heatSobolev μ hQ r hr (SobolevSpace.toLp μ hQ F)=
        heatTail μ hQ (t/2) (half_pos ht) f (t+r) := by
      apply Subtype.ext
      change SobolevSpace.toLp μ hQ (heatSobolev μ hQ r hr (SobolevSpace.toLp μ hQ F))=
        SobolevSpace.toLp μ hQ (heatTail μ hQ (t/2) (half_pos ht) f (t+r))
      rw [heatSobolev_toLp,heatTail_toLp μ hQ (t/2) (half_pos ht) f (t+r) (by linarith)]
      dsimp only [F]
      rw [heatSobolev_toLp,←mul_apply_eq_comp,←heatAt_add μ hQ r t hr.le ht.le,add_comm r t]
    rw [heF] at hh
    have hI : (∫ x, heatAt μ hQ r W x*(SobolevSpace.minimalSlope μ hQ F x)^2 ∂μ)=
        inner ℝ (heatAt μ hQ r W) H := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hG] with x hx
      change H x=(SobolevSpace.minimalSlope μ hQ F x)^2 at hx
      simp only [Real.inner_apply,hx]
    rw [hI] at hh
    convert hh using 1
    dsimp only [q,j]
    ring
  have hder := right_slope_correction_le
    (by simpa only [zero_add,smul_eq_mul,div_eq_mul_inv,mul_comm] using hq.tendsto_slope_zero_right)
    hb' hcorr (hq0.trans hb0.symm) hineq
  dsimp only
  rw [energyForm_comm μ hQ G w]
  dsimp only [W,H] at hder
  linarith

end RegularPointCoordinates

end

end OAI
