import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarSuffixSusceptibility
import OAI.Probability.SKBarriers.Hierarchy.AppendTimeGrid
import OAI.Probability.SKBarriers.Gaussian.LipschitzChainRepresentation

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarHierarchy_suffix_hessian_overlap_sum_of_suffix (a b : ℕ) (m v : Fin (a+b) → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone (fun i : Fin b => m (i.natAdd a))) (x : ℝ) :
    scalarHierarchyAverage a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
      (scalarHierarchy b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) scalarSpinTerminal)
      (rootHessian 0 (scalarHierarchy b (fun i => m (i.natAdd a))
        (fun i => v (i.natAdd a)) scalarSpinTerminal)) x=
      1-∑ j, hierarchyAtom b (fun i => m (i.natAdd a)) 1 j*
        scalarMomentSquare (a+b) m v scalarSpinTerminal scalarMagnetization (j.natAdd a) x := by
  let mb := fun i : Fin b => m (i.natAdd a)
  let vb := fun i : Fin b => v (i.natAdd a)
  have hf : BoundedDerivs (scalarHierarchy b mb vb scalarSpinTerminal) :=
    scalarHierarchy_regular b mb vb scalarSpinTerminal_regular
  have hg : BoundedScalar scalarMagnetization :=
    ⟨(Real.continuous_sinh.div Real.continuous_cosh (fun x => ne_of_gt (Real.cosh_pos x))),1,zero_le_one,scalarMagnetization_abs_le_one⟩
  have hM (j : Fin (b+1)) : BoundedScalar (scalarMomentSquare b mb vb scalarSpinTerminal scalarMagnetization j) :=
    scalarMomentSquare_bounded scalarSpinTerminal_regular hg b mb vb j
  have HE : rootHessian 0 (scalarHierarchy b mb vb scalarSpinTerminal)=
      fun y => 1-∑ j, hierarchyAtom b mb 1 j*scalarMomentSquare b mb vb scalarSpinTerminal scalarMagnetization j y := by
    funext y
    exact scalarHierarchy_spin_hessian_overlap_sum b mb vb (fun i => hm _) hmono y
  change scalarHierarchyAverage a _ _ (scalarHierarchy b mb vb scalarSpinTerminal) _ x=_
  rw [HE,scalarHierarchyAverage_sub hf (BoundedScalar.const 1)
    (BoundedScalar.finset_sum Finset.univ (fun j _ => (hM j).const_mul _)),
    scalarHierarchyAverage_const hf,scalarHierarchyAverage_sum Finset.univ hf
    (fun j _ => (hM j).const_mul _)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [scalarHierarchyAverage_const_mul hf (hM j)]
  congr 1
  exact congrFun (scalarMomentSquare_suffix_average a b m v scalarSpinTerminal scalarMagnetization j) x

def scalarCDFSusceptibilityAverage (β : ℝ) (α : ℝ → ℝ) (r : ℝ) : ℝ :=
  scalarCDFAverage β α 0 (Real.toNNReal r)
    (scalarCDFValue β α r (Real.toNNReal (1-r)))
    (scalarCDFHessian β α r (Real.toNNReal (1-r))) 0

theorem scalarCDFSusceptibilityAverage_eq_partition (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (a b : ℕ) (q : Fin (a+1) → ℝ) (p : Fin (b+1) → ℝ)
    (hq : Monotone q) (hp : Monotone p) (hq0 : q 0=0) (hp1 : p (Fin.last b)=1)
    (hr : q (Fin.last a)=p 0) (m : Fin a → ℝ) (l : Fin b → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hl : ∀ i, l i∈Icc (0:ℝ) 1) (hlm : Monotone l)
    (hmodelq : ∀ i : Fin a, ∀ z∈Ico (q i.castSucc) (q i.succ), α z=m i)
    (hmodelp : ∀ i : Fin b, ∀ z∈Ico (p i.castSucc) (p i.succ), α z=l i) :
    scalarCDFSusceptibilityAverage β α (p 0)=
      1-∑ j, hierarchyAtom b l 1 j*scalarCDFOverlap β α (p j) := by
  let r := p 0
  have hr0 : r∈Icc (0:ℝ) 1 := by
    constructor
    · change 0 ≤ p 0
      rw [← hr,← hq0]; exact hq (Fin.zero_le _)
    · rw [← hp1]; exact hp (Fin.le_last _)
  let t := Real.toNNReal r
  let s := Real.toNNReal (1-r)
  have ht : (t:ℝ)=r := Real.coe_toNNReal r hr0.1
  have hs : (s:ℝ)=1-r := Real.coe_toNNReal (1-r) (sub_nonneg.mpr hr0.2)
  have ht1 : t≤1 := by rw [← NNReal.coe_le_coe,ht,NNReal.coe_one]; exact hr0.2
  have hs1 : s≤1 := by rw [← NNReal.coe_le_coe,hs,NNReal.coe_one]; linarith [hr0.1]
  let f := scalarCDFValue β α r s
  let u := scalarCDFGradient β α r s
  let χ := scalarCDFHessian β α r s
  have hf : f=scalarHierarchy b l (timeGridCoefficients b β p) scalarSpinTerminal := by
    funext x
    exact scalarCDFOperator_eq_partition scalarSpinTerminal_regular scalarSpinTerminal_lipschitz
      β hα hαm b p hp l hl hmodelp s hs1 (by rw [hp1]; exact hs) x
  have hu : u=rootGradient 0 (scalarHierarchy b l (timeGridCoefficients b β p) scalarSpinTerminal) := by
    funext x
    have H := scalarCDFValue_hasDerivAt β hα hαm r s hs1 x
    change HasDerivAt f (u x) x at H
    rw [hf] at H
    exact H.unique (scalarHierarchy_spin_hasDerivAt _ _ _ x)
  have hχ : χ=rootHessian 0 (scalarHierarchy b l (timeGridCoefficients b β p) scalarSpinTerminal) := by
    funext x
    have H := scalarCDFGradient_hasDerivAt β hα hαm r s hs1 x
    change HasDerivAt u (χ x) x at H
    rw [hu] at H
    exact H.unique (scalarHierarchy_spin_gradient_hasDerivAt _ _ _ x)
  have H := scalarCDFAverage_eq_partition_lipschitz (scalarCDFValue_regular β hα hαm r s hs1)
    (scalarCDFValue_lipschitz β hα hαm r s hs1)
    (scalarCDFHessian_lipschitz β hα hαm r s hs1)
    (B:=1) (scalarCDFHessian_abs_le_one β hα hαm r s hs1)
    β hα hαm a q hq m hm hmodelq t ht1 (by rw [hr,hq0,sub_zero]; exact ht) 0
  rw [hq0] at H
  change scalarCDFAverage β α 0 t f χ 0=_ at H
  change scalarCDFAverage β α 0 t f χ 0=_
  rw [H]
  change scalarHierarchyAverage a m (timeGridCoefficients a β q) f χ 0=_
  rw [hf,hχ]
  have hml (i : Fin (a+b)) : Fin.append m l i∈Icc (0:ℝ) 1 := by
    refine Fin.addCases ?_ ?_ i
    · intro i; simpa only [Fin.append_left] using hm i
    · intro j; simpa only [Fin.append_right] using hl j
  have hmono : Monotone (fun i : Fin b => Fin.append m l (i.natAdd a)) := by
    simpa only [Fin.append_right] using hlm
  have HS := scalarHierarchy_suffix_hessian_overlap_sum_of_suffix a b (Fin.append m l)
    (Fin.append (timeGridCoefficients a β q) (timeGridCoefficients b β p)) hml hmono 0
  simp only [Fin.append_left,Fin.append_right] at HS
  rw [HS]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [scalarCDFOverlap_eq_two_partitions_index β hα hαm a b q p hq hp hq0 hp1 hr
    m l hm hl hmodelq hmodelp j]

end SK.Analytic

end
end

end OAI
