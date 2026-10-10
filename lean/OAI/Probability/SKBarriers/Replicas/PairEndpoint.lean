import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarCDFLimit
import OAI.Probability.SKBarriers.Replicas.PairFactor

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem splitPairMass_zero {k : ℕ} (a : ℕ) (m : Fin (k+1) → ℝ) (h : m 0=0) :
    splitPairMass a m 0=0 := by simp [splitPairMass,h]

theorem splitPairMass_mem {n : ℕ} (a : ℕ) (m : Fin n → ℝ)
    (h : ∀ i, m i∈Icc (0:ℝ) 1) (i : Fin n) : splitPairMass a m i∈Icc (0:ℝ) 1 := by
  have H := h i
  unfold splitPairMass
  split_ifs <;> constructor <;> linarith [H.1,H.2]

theorem splitPairMass_mono {n : ℕ} (a : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i) (h : Monotone m) : Monotone (splitPairMass a m) := by
  intro i j hij
  have H := h hij
  have H0 := hm j
  simp only [splitPairMass]
  split_ifs with hi hj hj
  · linarith
  · linarith
  · have hv : i.val ≤ j.val := hij
    omega
  · exact H

theorem splitPairBlock_pressure (n a b : ℕ) (hn : n=a+b) (m v : Fin n → ℝ) :
    vectorBlockHierarchy 2 n (splitPairMass a m) (splitPairVector a v)
      (fun p => scalarSpinTerminal p.1+scalarSpinTerminal p.2) (0:ℝ × ℝ)=
      2*scalarHierarchy n m v scalarSpinTerminal 0 := by
  subst n
  rw [splitPairHierarchy]
  exact pairSplit_pressure a b m v scalarSpinTerminal_regular 0

theorem splitPairBlock_observable (n a b : ℕ) (hn : n=a+b) (m v : Fin n → ℝ) :
    vectorBlockHierarchyAverage 2 n (splitPairMass a m) (splitPairVector a v)
      (fun p => scalarSpinTerminal p.1+scalarSpinTerminal p.2)
      (fun p => scalarMagnetization p.1*scalarMagnetization p.2) (0:ℝ × ℝ)=
      scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization ⟨a,by omega⟩ 0 := by
  subst n
  rw [splitPairHierarchyAverage]
  exact pairSplit_overlap a b m v scalarSpinTerminal_regular scalarMagnetization 0

theorem pairSiteValue (a b : ℕ) (β : ℝ) (m c : Fin (a+b+1) → ℝ) (hm : m 0=0) :
    vectorHierarchy ((a+b+1)*2)
      (siteBlockMass 2 (a+b) (zeroInitialAtoms (a+b) (splitPairMass a m)))
      (matrixSiteVector β (splitPairFactor a c) (fun (s : Config 2) i => spin (s i)))
      (siteValueTerminal (fun _ : Config 2 => 0)) 0=
      2*scalarHierarchy (a+b+1) m (fun i => β*c i) scalarSpinTerminal 0 := by
  rw [funext (siteBlockMass_zeroInitial (splitPairMass a m) (splitPairMass_zero a m hm))]
  simp only [splitPairFactor_vector]
  have H := congrFun (vectorHierarchy_pullback pairSpinMap ((a+b+1)*2)
    (fun j => splitPairMass a m (finProdFinEquiv.symm j).1)
    (fun j => splitPairVector a (fun i => β*c i) (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)
    (siteValueTerminal (fun _ : Config 2 => 0))) (0:ℝ × ℝ)
  simp only [Function.comp_apply,map_zero] at H
  rw [← H,pairSpin_terminal,vectorHierarchy_blocks]
  exact splitPairBlock_pressure _ a (b+1) (by omega) m _

theorem pairSiteObservable (a b : ℕ) (β : ℝ) (m c : Fin (a+b+1) → ℝ) (hm : m 0=0) :
    vectorHierarchyAverage ((a+b+1)*2)
      (siteBlockMass 2 (a+b) (zeroInitialAtoms (a+b) (splitPairMass a m)))
      (matrixSiteVector β (splitPairFactor a c) (fun (s : Config 2) i => spin (s i)))
      (siteValueTerminal (fun _ : Config 2 => 0))
      (affineMoment (fun _ : Config 2 => 0) (fun s => ContinuousLinearMap.proj s)
        (matrixSiteWeight pairMultiplier (fun (s : Config 2) i => spin (s i)))) 0=
      scalarMomentSquare (a+b+1) m (fun i => β*c i) scalarSpinTerminal scalarMagnetization ⟨a,by omega⟩ 0 := by
  rw [funext (siteBlockMass_zeroInitial (splitPairMass a m) (splitPairMass_zero a m hm))]
  simp only [splitPairFactor_vector,pairMultiplier_observable]
  have H := congrFun (vectorHierarchyAverage_pullback pairSpinMap ((a+b+1)*2)
    (fun j => splitPairMass a m (finProdFinEquiv.symm j).1)
    (fun j => splitPairVector a (fun i => β*c i) (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)
    (siteValueTerminal (fun _ : Config 2 => 0))
    (affineMoment (fun _ : Config 2 => 0) (fun s => ContinuousLinearMap.proj s) pairSpinObservable)) (0:ℝ × ℝ)
  simp only [Function.comp_apply,map_zero] at H
  rw [← H,pairSpin_terminal,pairSpin_thermal_observable,vectorHierarchyAverage_blocks]
  exact splitPairBlock_observable _ a (b+1) (by omega) m _

end SK.Analytic

end
end

end OAI
