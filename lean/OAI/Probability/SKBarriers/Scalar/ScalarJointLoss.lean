import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarListBounds
import OAI.Probability.SKBarriers.Hierarchy.ConstantWeightStats
import OAI.Probability.SKBarriers.Scalar.ScalarHessianFloor
import OAI.Probability.SKBarriers.Scalar.ScalarCompactAverage
import OAI.Probability.SKBarriers.Scalar.ScalarHessianLoss

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem BoundedScalar.mul {f g : ℝ → ℝ} (hf : BoundedScalar f) (hg : BoundedScalar g) :
    BoundedScalar (fun x => f x*g x) := by
  obtain ⟨A,hA,hfA⟩ := hf.bounded
  obtain ⟨B,hB,hgB⟩ := hg.bounded
  exact ⟨hf.continuous.mul hg.continuous,A*B,mul_nonneg hA hB,fun x => by
    rw [abs_mul]; exact mul_le_mul (hfA x) (hgB x) (abs_nonneg _) hA⟩

theorem scalarIncrementAverage_mono (l : List (ℝ × ℝ)) {f g h : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedScalar g) (hh : BoundedScalar h)
    (hle : ∀ x,g x≤h x) (x : ℝ) :
    scalarIncrementAverage l f g x≤ scalarIncrementAverage l f h x := by
  simp only [scalarIncrementAverage_get]
  exact scalarHierarchyAverage_mono hf hg hh hle _ _ _ _

theorem scalarIncrementAverage_terminal_hessian_floor (l : List (ℝ × ℝ))
    (hm : ∀ p∈l,p.1∈Icc (0:ℝ) 1) (hs : l.Pairwise (fun p q => p.1≤q.1))
    {T A : ℝ} (hT : 0≤T) (hA : 0≤A) (hv : rawVariance l≤T) {x : ℝ} (hx : |x|≤A) :
    scalarSusceptibilityFloor T A≤ scalarIncrementAverage l scalarSpinTerminal
      (rootHessian 0 scalarSpinTerminal) x := by
  rw [scalarIncrementAverage_get]
  exact scalarHierarchyAverage_terminal_hessian_floor _ _ _
    (fun i => hm _ (List.get_mem _ _)) (mass_get_monotone hs) hT hA
    (by rw [sum_get_map l (fun p => p.2^2)]; exact hv) hx

theorem scalarIncrementChain_hessian_floor (l : List (ℝ × ℝ))
    (hm : ∀ p∈l,p.1∈Icc (0:ℝ) 1) (hs : l.Pairwise (fun p q => p.1≤q.1))
    {T A : ℝ} (hT : 0≤T) (hA : 0≤A) (hv : rawVariance l≤T) {x : ℝ} (hx : |x|≤A) :
    scalarSusceptibilityFloor T A≤rootHessian 0 (scalarIncrementChain l scalarSpinTerminal) x := by
  rw [scalarIncrementChain_get]
  exact scalarHierarchy_hessian_floor _ _ _
    (fun i => hm _ (List.get_mem _ _)) (mass_get_monotone hs) hT hA
    (by rw [sum_get_map l (fun p => p.2^2)]; exact hv) hx

theorem scalarIncrementAverage_joint_hessian_loss (l j k : List (ℝ × ℝ))
    (hl : ∀ p∈l,p.1∈Icc (0:ℝ) 1) (hjk : ∀ p∈j++k,p.1∈Icc (0:ℝ) 1)
    (hsl : l.Pairwise (fun p q => p.1≤q.1)) (hsjk : (j++k).Pairwise (fun p q => p.1≤q.1))
    {T a : ℝ} (hT : 0≤T) (ha : 0≤a) (hma : ∀ p∈j,a≤p.1)
    (hvl : rawVariance l≤T) (hvjk : rawVariance (j++k)≤T) :
    let F := scalarIncrementChain k scalarSpinTerminal
    let H := scalarIncrementChain j F
    let χ := rootHessian 0 H
    let K := scalarIncrementAverage j F (rootHessian 0 F)
    scalarIncrementAverage l H (fun x => χ x*K x) 0 ≤
      scalarIncrementAverage l H (fun x => (χ x)^2) 0-
        a*rawVariance j*(scalarSusceptibilityFloor T (1+2*T+4*T^2))^3/2 := by
  dsimp only
  let F := scalarIncrementChain k scalarSpinTerminal
  let H := scalarIncrementChain j F
  let χ := rootHessian 0 H
  let K := scalarIncrementAverage j F (rootHessian 0 F)
  let b := scalarSusceptibilityFloor T (1+2*T+4*T^2)
  have hj : ∀ p∈j,p.1∈Icc (0:ℝ) 1 := fun p hp => hjk p (List.mem_append_left _ hp)
  have hk : ∀ p∈k,p.1∈Icc (0:ℝ) 1 := fun p hp => hjk p (List.mem_append_right _ hp)
  have hF : BoundedDerivs F := scalarIncrementChain_regular _ scalarSpinTerminal_regular
  have hFc : ScalarSpinConvex F := scalarIncrementChain_spin_convex k hk
  have he : H=scalarIncrementChain (j++k) scalarSpinTerminal := (scalarIncrementChain_append _ _ _).symm
  have hH : BoundedDerivs H := scalarIncrementChain_regular _ hF
  have hHc : ScalarSpinConvex H := he ▸ scalarIncrementChain_spin_convex (j++k) hjk
  have hχ : BoundedScalar χ := hHc.hessian_bounded hH
  have hK : BoundedScalar K := scalarIncrementAverage_bounded _ hF (hFc.hessian_bounded hF)
  have hχ0 (x : ℝ) : 0≤χ x := (hHc x).1
  have hK0 (x : ℝ) : 0≤K x := scalarIncrementAverage_nonneg _ hF
    (hFc.hessian_bounded hF) (fun y => (hFc y).1) x
  have hb : 0<b := scalarSusceptibilityFloor_pos _ _
  have hχb (x : ℝ) (hx : |x|≤1+2*T+4*T^2) : b≤χ x := by
    dsimp [χ]; rw [he]
    exact scalarIncrementChain_hessian_floor _ hjk hsjk hT (by positivity) hvjk hx
  have hKb (x : ℝ) (hx : |x|≤1+2*T+4*T^2) : b≤K x := by
    have H₀ := scalarIncrementAverage_terminal_hessian_floor (j++k) hjk hsjk hT
      (by positivity) hvjk hx
    rw [scalarIncrementAverage_append] at H₀
    apply H₀.trans
    apply scalarIncrementAverage_mono j hF
      (scalarIncrementAverage_bounded k scalarSpinTerminal_regular
        (scalarSpinTerminal_spinConvex.hessian_bounded scalarSpinTerminal_regular))
      (hFc.hessian_bounded hF)
    intro y
    simpa only [scalarIncrementAverage_get,scalarIncrementChain_get,F] using
      (scalarHierarchy_cramer_data scalarSpinTerminal_regular scalarSpinTerminal_spinConvex
        k.length (fun i => (k.get i).1) (fun i => (k.get i).2)
        (fun i => hk _ (List.get_mem _ _)) y).2.1
  have hb3 : b^3/2≤ scalarIncrementAverage l H (fun x => χ x*(K x)^2) 0 := by
    rw [scalarIncrementAverage_get]
    apply scalarHierarchyAverage_compact_lower _ _ _
      (fun i => hl _ (List.get_mem _ _)) (mass_get_monotone hsl) hH hHc (hχ.mul hK.sq)
      hT (by rw [sum_get_map l (fun p => p.2^2)]; exact hvl) (by positivity)
      (fun x => mul_nonneg (hχ0 x) (sq_nonneg _))
    intro x hx
    have H₁ := hχb x hx
    have H₂ : b^2≤(K x)^2 := (sq_le_sq₀ hb.le (hK0 x)).mpr (hKb x hx)
    calc
      b^3=b*b^2 := by ring
      _ ≤ χ x*(K x)^2 := mul_le_mul H₁ H₂ (sq_nonneg _) (hχ0 x)
  have Hloss (x : ℝ) : K x+a*rawVariance j*(K x)^2≤χ x := by
    have G := scalarHierarchy_hessian_loss_cramer hF hFc j.length
      (fun i => (j.get i).1) (fun i => (j.get i).2)
      (fun i => hj _ (List.get_mem _ _)) ha (fun i => hma _ (List.get_mem _ _)) x
    rw [sum_get_map j (fun p => p.2^2)] at G
    simpa only [K,χ,H,scalarIncrementAverage_get,scalarIncrementChain_get,rawVariance] using G
  have HP := scalarIncrementAverage_mono l hH
    ((hχ.mul hK).add ((hχ.mul hK.sq).const_mul (a*rawVariance j))) hχ.sq
    (fun x => by nlinarith [mul_le_mul_of_nonneg_left (Hloss x) (hχ0 x)]) 0
  simp only [scalarIncrementAverage_get] at HP
  rw [scalarHierarchyAverage_add hH (hχ.mul hK) ((hχ.mul hK.sq).const_mul _),
    scalarHierarchyAverage_const_mul hH (hχ.mul hK.sq)] at HP
  simp only [← scalarIncrementAverage_get] at HP
  change scalarIncrementAverage l H (fun x => χ x*K x) 0+
    a*rawVariance j*scalarIncrementAverage l H (fun x => χ x*(K x)^2) 0≤
    scalarIncrementAverage l H (fun x => (χ x)^2) 0 at HP
  have Hmul := mul_le_mul_of_nonneg_left hb3 (mul_nonneg ha (rawVariance_nonneg j))
  dsimp only [b,χ,K,H,F] at HP Hmul
  nlinarith

end SK.Analytic

end
end

end OAI
