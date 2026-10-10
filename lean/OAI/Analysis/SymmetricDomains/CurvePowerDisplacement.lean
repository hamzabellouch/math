import Mathlib
import OAI.Analysis.SymmetricDomains.OneParameterJointStrict

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

namespace Biholomorph

section
open Set Filter Topology Metric MeasureTheory
open scoped NNReal
open scoped NNReal
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
variable (a b : ℝ → Biholomorph U U) (ha : Continuous a) (hb : Continuous b)
include hU ha hb

theorem productCurve_joint_hasStrictFDerivAt (hbd : Bornology.IsBounded U)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
    (hb0 : b 0=1) (hbm : ∀ s t, b (s+t)=b s*b t) (p : U) :
    HasStrictFDerivAt (fun z : ℝ × Affine n => (a z.1*b z.1).ambientAut z.2)
      ((ContinuousLinearMap.toSpanSingleton ℝ
        (infinitesimalGenerator a p.val+infinitesimalGenerator b p.val)).coprod 1) (0,p.val) := by
  have hA := oneParameter_joint_hasStrictFDerivAt hU a ha hbd ha0 ham 0 p
  have hB := oneParameter_joint_hasStrictFDerivAt hU b hb hbd hb0 hbm 0 p
  rw [ha0,one_apply,derivativeAt_one hU] at hA
  rw [hb0,one_apply,derivativeAt_one hU] at hB
  have hB0 : (b 0).ambientAut p.val=p.val := by rw [hb0,ambientAut_apply,one_apply]
  have he : (fun z : ℝ × Affine n => (a z.1*b z.1).ambientAut z.2) =ᶠ[𝓝 (0,p.val)]
      (fun z : ℝ × Affine n => (a z.1).ambientAut ((b z.1).ambientAut z.2)) := by
    filter_upwards [continuous_snd.continuousAt (hU.mem_nhds p.property)] with z hz
    rw [ambientAut_apply (a z.1*b z.1) ⟨z.2,hz⟩, mul_apply,
      ambientAut_apply (b z.1) ⟨z.2,hz⟩,ambientAut_apply]
  rw [show ((0 : ℝ),p.val)=(0,(b 0).ambientAut p.val) from by rw [hB0]] at hA
  have hC := hA.comp ((0 : ℝ),p.val)
    ((hasStrictFDerivAt_fst (𝕜 := ℝ) (p := ((0 : ℝ),p.val))).prodMk hB)
  have hD :
      (((ContinuousLinearMap.toSpanSingleton ℝ (infinitesimalGenerator a p.val)).coprod
        ((1 : Affine n →L[ℂ] Affine n).restrictScalars ℝ)).comp
        ((ContinuousLinearMap.fst ℝ ℝ (Affine n)).prod
          ((ContinuousLinearMap.toSpanSingleton ℝ (infinitesimalGenerator b p.val)).coprod
            ((1 : Affine n →L[ℂ] Affine n).restrictScalars ℝ)))) =
      ((ContinuousLinearMap.toSpanSingleton ℝ
        (infinitesimalGenerator a p.val+infinitesimalGenerator b p.val)).coprod 1) := by
    apply DFunLike.ext
    intro z
    change z.1 • infinitesimalGenerator a p.val +
      (z.1 • infinitesimalGenerator b p.val+z.2) =
      z.1 • (infinitesimalGenerator a p.val+infinitesimalGenerator b p.val)+z.2
    rw [smul_add,add_assoc]
  rw [hD] at hC
  exact hC.congr_of_eventuallyEq he.symm

end

open Set Filter Topology Metric MeasureTheory
open scoped NNReal
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U)
include hU

theorem curve_uniform_displacement (c : ℝ → Biholomorph U U) (hc0 : c 0=1)
    (p : U) {A : (ℝ × Affine n) →L[ℝ] Affine n}
    (hd : HasStrictFDerivAt (fun z : ℝ × Affine n => (c z.1).ambientAut z.2) A (0,p.val)) :
    ∃ r > (0:ℝ), ∃ L : ℝ≥0, closedBall p.val r ⊆ U ∧
      ∀ t : ℝ, |t| ≤ r → ∀ y ∈ closedBall p.val r,
        ‖(c t).ambientAut y-y‖ ≤ L*|t| := by
  obtain ⟨L,S,hS,hL⟩ := hd.exists_lipschitzOnWith
  obtain ⟨r,hr,hrs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hS
  obtain ⟨R,hR,hRU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds p.property)
  refine ⟨min r R,lt_min hr hR,L,fun y hy => hRU (closedBall_subset_closedBall (min_le_right _ _) hy),?_⟩
  intro t ht y hy
  have hyr : dist y p.val ≤ r := (mem_closedBall.mp hy).trans (min_le_left _ _)
  have htr : |t| ≤ r := ht.trans (min_le_left _ _)
  have hts : (t,y) ∈ S := hrs (by simpa only [mem_closedBall,Prod.dist_eq,Real.dist_eq,
    sub_zero,max_le_iff] using And.intro htr hyr)
  have hzs : ((0:ℝ),y) ∈ S := hrs (by simpa only [mem_closedBall,Prod.dist_eq,
    dist_self,max_le_iff] using And.intro hr.le hyr)
  have hyu : y ∈ U := hRU (closedBall_subset_closedBall (min_le_right _ _) hy)
  have h0 : (c 0).ambientAut y=y := by rw [hc0,ambientAut_apply 1 ⟨y,hyu⟩,one_apply]
  have hv := hL.dist_le_mul (x := (t,y)) (y := (0,y)) hts hzs
  simpa [h0,dist_eq_norm,Prod.norm_def] using hv

omit hU

theorem curve_power_displacement (c : ℝ → Biholomorph U U) (p : U)
    {r : ℝ} {L : ℝ≥0}
    (hstep : ∀ t : ℝ, |t| ≤ r → ∀ y ∈ closedBall p.val r,
      ‖(c t).ambientAut y-y‖ ≤ L*|t|)
    {t : ℝ} {N : ℕ} (hN : N ≠ 0) (ht : |t| ≤ r) (hLt : L*|t| ≤ r) :
    ∀ j ≤ N, dist (((c (t/N))^j).toHomeomorph p).val p.val ≤ (j:ℝ)*(L*|t|/(N:ℝ)) := by
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hN1 : (1:ℝ)≤N := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hN)
  have hdiv : |t/(N:ℝ)| ≤ r := by
    rw [abs_div,abs_of_pos hNr]
    exact (div_le_self (abs_nonneg t) hN1).trans ht
  intro j hj
  induction j with
  | zero => simp [one_apply]
  | succ j ih =>
    have hjN : j≤N := (Nat.le_succ j).trans hj
    have hi := ih hjN
    have hsmall : dist (((c (t/N))^j).toHomeomorph p).val p.val ≤ r := by
      refine hi.trans ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hjN)
        (div_nonneg (mul_nonneg L.coe_nonneg (abs_nonneg t)) hNr.le)).trans ?_)
      simpa only [mul_div_cancel₀ _ (ne_of_gt hNr)] using hLt
    have hst := hstep (t/N) hdiv (((c (t/N))^j).toHomeomorph p).val hsmall
    rw [ambientAut_apply] at hst
    have hdist := dist_triangle
      (((c (t/N))^ (j+1)).toHomeomorph p).val
      (((c (t/N))^j).toHomeomorph p).val p.val
    rw [pow_succ',mul_apply]
    rw [pow_succ',mul_apply] at hdist
    refine hdist.trans ?_
    rw [dist_eq_norm]
    refine (add_le_add hst hi).trans_eq ?_
    rw [abs_div,abs_of_pos hNr,Nat.cast_add,Nat.cast_one]
    ring

end Biholomorph
end Release061

end

end OAI
