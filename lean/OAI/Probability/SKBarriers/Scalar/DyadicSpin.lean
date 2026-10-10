import Mathlib
import OAI.Probability.SKBarriers.Scalar.DyadicScalar
import OAI.Probability.SKBarriers.Scalar.ScalarSusceptibility

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem dyadicIntervals_pairwise {α : ℝ → ℝ} (hα : Monotone α)
    (n : ℕ) (s : ℝ) (t : ℝ≥0) :
    (dyadicIntervals α n s t).Pairwise (fun p q => p.1 ≤ q.1) := by
  induction n generalizing s t with
  | zero => exact List.pairwise_singleton _ _
  | succ n ih =>
    apply List.pairwise_append.mpr
    refine ⟨ih s (t/2),ih (s+(t:ℝ)/2) (t/2),?_⟩
    intro p hp q hq
    have H := (dyadicIntervals_mem_bounds hα n s (t/2) hp).2.1
    have H' := (dyadicIntervals_mem_bounds hα n (s+(t:ℝ)/2) (t/2) hq).1
    norm_num only [NNReal.coe_div,NNReal.coe_ofNat] at H
    exact H.trans H'

theorem scalarTimeChain_eq_hierarchy (β : ℝ) (l : List (ℝ × ℝ≥0)) (f : ℝ → ℝ) :
    scalarTimeChain β l f=scalarHierarchy l.length (fun i => (l.get i).1)
      (fun i => β*Real.sqrt ((l.get i).2:ℝ)) f := by
  have he : List.ofFn (fun i => ((l.get i).1,(l.get i).2))=l := by
    simpa only [Prod.eta] using List.ofFn_get l
  have H := scalarTimeChain_ofFn β l.length (fun i => (l.get i).1) (fun i => (l.get i).2) f
  rw [he] at H
  exact H

theorem scalarTimeChain_mass_monotone (l : List (ℝ × ℝ≥0))
    (h : l.Pairwise (fun p q => p.1 ≤ q.1)) : Monotone (fun i => (l.get i).1) := by
  intro i j hij
  rcases hij.eq_or_lt with he|he
  · exact he ▸ le_rfl
  · exact List.pairwise_iff_get.mp h i j he

theorem scalarTimeChain_spin_hasDerivAt (β : ℝ) (l : List (ℝ × ℝ≥0)) (x : ℝ) :
    HasDerivAt (scalarTimeChain β l scalarSpinTerminal)
      (rootGradient 0 (scalarTimeChain β l scalarSpinTerminal) x) x := by
  rw [scalarTimeChain_eq_hierarchy]
  exact scalarHierarchy_spin_hasDerivAt _ _ _ _

theorem scalarTimeChain_spin_gradient_hasDerivAt (β : ℝ) (l : List (ℝ × ℝ≥0)) (x : ℝ) :
    HasDerivAt (rootGradient 0 (scalarTimeChain β l scalarSpinTerminal))
      (rootHessian 0 (scalarTimeChain β l scalarSpinTerminal) x) x := by
  rw [scalarTimeChain_eq_hierarchy]
  exact scalarHierarchy_spin_gradient_hasDerivAt _ _ _ _

theorem scalarTimeChain_spin_gradient_lipschitz (β : ℝ) (l : List (ℝ × ℝ≥0))
    (hm : ∀ p ∈ l, p.1 ∈ Icc (0:ℝ) 1) :
    LipschitzWith 1 (rootGradient 0 (scalarTimeChain β l scalarSpinTerminal)) := by
  rw [scalarTimeChain_eq_hierarchy]
  exact scalarHierarchy_spin_gradient_lipschitz _ _ _ (fun i => hm _ (List.get_mem _ i))

theorem scalarTimeChain_spin_hessian_lipschitz (β : ℝ) (l : List (ℝ × ℝ≥0))
    (hm : ∀ p ∈ l, p.1 ∈ Icc (0:ℝ) 1) (hmono : l.Pairwise (fun p q => p.1 ≤ q.1)) :
    LipschitzWith susceptibilityLipschitzConstant
      (rootHessian 0 (scalarTimeChain β l scalarSpinTerminal)) := by
  rw [scalarTimeChain_eq_hierarchy]
  exact scalarHierarchy_spin_hessian_lipschitz _ _ _ (fun i => hm _ (List.get_mem _ i))
    (scalarTimeChain_mass_monotone l hmono)

theorem dyadicScalar_spin_bounds (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (n : ℕ) (s : ℝ) (t : ℝ≥0) (x : ℝ) :
    |rootGradient 0 (dyadicScalar β α n s t scalarSpinTerminal) x| ≤ 1 ∧
      0<rootHessian 0 (dyadicScalar β α n s t scalarSpinTerminal) x ∧
      rootHessian 0 (dyadicScalar β α n s t scalarSpinTerminal) x ≤
        1-(rootGradient 0 (dyadicScalar β α n s t scalarSpinTerminal) x)^2 := by
  unfold dyadicScalar
  rw [scalarTimeChain_eq_hierarchy]
  exact scalarHierarchy_spin_derivative_bounds _ _ _
    (fun i => dyadicIntervals_mass_bounds hα n s t (List.get_mem _ i)) x

theorem dyadicScalar_successive_geometric {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (hLip : LipschitzWith 1 f) (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (n : ℕ) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |dyadicScalar β α (n+1) s t f x-dyadicScalar β α n s t f x| ≤
      scalarTimeMassConstant β*(1/2:ℝ)^n := by
  have H := dyadicScalar_successive_bound hf hLip β hα hmono n s t ht x
  have hC := scalarTimeMassConstant_nonneg β
  have ht' : (t:ℝ) ≤ 1 := ht
  have ho : α (s+t)-α s ≤ 1 := by linarith [(hα (s+t)).2,(hα s).1]
  apply H.trans
  calc
    _ ≤ scalarTimeMassConstant β*(t:ℝ)/(2:ℝ)^(n+1) :=
      mul_le_of_le_one_right (by positivity) ho
    _ ≤ scalarTimeMassConstant β/(2:ℝ)^(n+1) :=
      div_le_div_of_nonneg_right (mul_le_of_le_one_right hC ht') (by positivity)
    _ = scalarTimeMassConstant β*(1/2:ℝ)^(n+1) := by rw [div_pow,one_pow]; ring
    _ ≤ scalarTimeMassConstant β*(1/2:ℝ)^n := by
      rw [pow_succ]
      nlinarith [mul_nonneg hC (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) n)]

end SK.Analytic

end
end

end OAI
