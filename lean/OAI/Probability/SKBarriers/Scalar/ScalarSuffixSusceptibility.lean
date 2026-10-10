import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarCDFLimit
import OAI.Probability.SKBarriers.Scalar.ScalarSplit
import OAI.Probability.SKBarriers.Scalar.ScalarSusceptibilitySum
import OAI.Probability.SKBarriers.Scalar.ScalarHierarchyAverageAlgebra

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarHierarchyAverage_const {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (n : ℕ) (m v : Fin n → ℝ) (c x : ℝ) :
    scalarHierarchyAverage n m v f (fun _ => c) x=c := by
  rw [scalarHierarchyAverage_integral hf (BoundedScalar.const c)]
  have : IsProbabilityMeasure (hierarchyPathLaw n m (fun z => f (x+coordinateLinear n v z)) 0) :=
    hierarchyPathLaw_probability n m _ ((hf.translate x).compCLM (coordinateLinear n v)) 0
  simp

theorem BoundedScalar.finset_sum {ι : Type*} (s : Finset ι) {g : ι → ℝ → ℝ}
    (hg : ∀ i∈s, BoundedScalar (g i)) : BoundedScalar (fun x => ∑ i∈s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using BoundedScalar.const 0
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (hg a (Finset.mem_insert_self a s)).add (ih (fun i hi => hg i (Finset.mem_insert_of_mem hi)))

theorem scalarHierarchyAverage_sum {ι : Type*} (s : Finset ι) {f : ℝ → ℝ}
    {g : ι → ℝ → ℝ} (hf : BoundedDerivs f) (hg : ∀ i∈s, BoundedScalar (g i))
    (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    scalarHierarchyAverage n m v f (fun y => ∑ i∈s, g i y) x=
      ∑ i∈s, scalarHierarchyAverage n m v f (g i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using scalarHierarchyAverage_const hf n m v 0 x
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [scalarHierarchyAverage_add hf (hg a (Finset.mem_insert_self a s))
      (BoundedScalar.finset_sum s (fun i hi => hg i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))]

theorem scalarMomentSquare_bounded {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (n : ℕ) (m v : Fin n → ℝ) (j : Fin (n+1)) :
    BoundedScalar (scalarMomentSquare n m v f g j) := by
  induction n generalizing f g with
  | zero => exact hg.sq
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [scalarMomentSquare,Fin.lastCases_last]
      exact scalarHierarchyAverage_bounded hf hg.sq (n+1) m v
    · simp only [scalarMomentSquare,Fin.lastCases_castSucc]
      exact ih (scalarStep_regular hf _ _) (hg.scalarStepAverage hf _ _) _ _ j

theorem scalarMomentSquare_last (n : ℕ) (m v : Fin n → ℝ) (f g : ℝ → ℝ) :
    scalarMomentSquare n m v f g (Fin.last n)=scalarHierarchyAverage n m v f (fun x => (g x)^2) := by
  cases n with
  | zero => rfl
  | succ n => simp only [scalarMomentSquare,Fin.lastCases_last]

theorem scalarMomentSquare_suffix_average (a b : ℕ) (m v : Fin (a+b) → ℝ)
    (f g : ℝ → ℝ) (j : Fin (b+1)) :
    scalarHierarchyAverage a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
      (scalarHierarchy b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f)
      (scalarMomentSquare b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f g j)=
      scalarMomentSquare (a+b) m v f g (j.natAdd a) := by
  induction b generalizing f g with
  | zero =>
    have hj : j=0 := by ext; omega
    subst j
    rw [show (0:Fin 1).natAdd a=Fin.last a by ext; simp]
    change scalarHierarchyAverage a m v f (fun x => (g x)^2)=scalarMomentSquare a m v f g (Fin.last a)
    exact (scalarMomentSquare_last a m v f g).symm
  | succ b ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [scalarMomentSquare_last,show (Fin.last (b+1)).natAdd a=Fin.last (a+(b+1)) by ext; simp,
        scalarMomentSquare_last]
      exact (scalarHierarchyAverage_split a (b+1) m v f (fun x => (g x)^2)).symm
    · simp only [scalarMomentSquare,Fin.lastCases_castSucc]
      have he : j.castSucc.natAdd a=(j.natAdd a).castSucc := by ext; rfl
      rw [he,Fin.lastCases_castSucc]
      exact ih (fun i => m i.castSucc) (fun i => v i.castSucc)
        (scalarStep (m (Fin.last (a+b))) (v (Fin.last (a+b))) f)
        (scalarStepAverage (m (Fin.last (a+b))) (v (Fin.last (a+b))) f g) j

theorem scalarHierarchy_suffix_hessian_overlap_sum (a b : ℕ) (m v : Fin (a+b) → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m) (x : ℝ) :
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
    exact scalarHierarchy_spin_hessian_overlap_sum b mb vb (fun i => hm _) (fun i j hij => hmono (Nat.add_le_add_left hij a)) y
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

end SK.Analytic

end
end

end OAI
