import OAI.Analysis.MarkovType.WalkDisplacement
import OAI.Analysis.MarkovType.ChartPathProbability
import Mathlib.Data.List.OfFn

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

open FiniteWalkDrift

def rawChartEdgeLabel {n B : ℕ} (ν : FiniteLaw (Chart (walkLandmarks n) B))
    (e : UniformCouplingEdge (PositiveMassSupport ν) Letter) : C00 :=
  rawWalkLabel e.1.val e.2.1 e.2.2.val

def markedChartPath {n B : ℕ} (ν : FiniteLaw (Chart (walkLandmarks n) B))
    (ω : MarkedPath (ConcreteChartState ν) (ConcreteChartEdge ν) n)
    (i : Fin (n + 1)) : Chart (walkLandmarks n) B :=
  (markedState (concreteChartChain ν) ω i).val

theorem markedChartPath_source {n B : ℕ}
    (ν : FiniteLaw (Chart (walkLandmarks n) B))
    (ω : MarkedPath (ConcreteChartState ν) (ConcreteChartEdge ν) n)
    (hv : markedValid (concreteChartChain ν) ω) (i : Fin n) :
    markedChartPath ν ω i.castSucc = (ω.2 i).1.val := by
  exact congrArg Subtype.val (hv i).symm

theorem markedChartPath_target {n B : ℕ}
    (ν : FiniteLaw (Chart (walkLandmarks n) B))
    (ω : MarkedPath (ConcreteChartState ν) (ConcreteChartEdge ν) n) (i : Fin n) :
    markedChartPath ν ω i.succ = (ω.2 i).2.2.val := by
  change (markedState (concreteChartChain ν) ω i.succ).val = _
  rw [markedState_succ]
  rfl

def chartPathFromArray {n B k : ℕ} (v : Fin k → Letter)
    (C : Fin (k + 1) → Chart (walkLandmarks n) B)
    (i : Fin ((List.ofFn v).length + 1)) : Chart (walkLandmarks n) B :=
  C ⟨i.val, by simpa only [List.length_ofFn] using i.isLt⟩

theorem rawChartWalkSum_ofFn {n B k : ℕ} (v : Fin k → Letter)
    (C : Fin (k + 1) → Chart (walkLandmarks n) B) :
    rawChartWalkSum (List.ofFn v) (chartPathFromArray v C) =
      ∑ i : Fin k, rawWalkLabel (C i.castSucc) (v i) (C i.succ) := by
  classical
  let e : Fin k ≃ Fin (List.ofFn v).length := finCongr (List.length_ofFn.symm)
  let F : Fin (List.ofFn v).length → C00 := fun i =>
    rawWalkLabel (chartPathFromArray v C i.castSucc)
      ((List.ofFn v).get i) (chartPathFromArray v C i.succ)
  calc
    rawChartWalkSum (List.ofFn v) (chartPathFromArray v C) = ∑ i, F i := rfl
    _ = ∑ i : Fin k, F (e i) := (e.sum_comp F).symm
    _ = ∑ i : Fin k, rawWalkLabel (C i.castSucc) (v i) (C i.succ) := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [F]
      rw [List.get_ofFn]
      rfl

theorem chartPathFromArray_good {n B k : ℕ} (v : Fin k → Letter)
    (C : Fin (k + 1) → Chart (walkLandmarks n) B)
    (hg : ∀ i : Fin k,
      Chart.Good (letterOrderIso (v i)) (C i.castSucc) (C i.succ)) :
    ∀ i : Fin (List.ofFn v).length,
      Chart.Good (letterOrderIso ((List.ofFn v).get i))
        (chartPathFromArray v C i.castSucc) (chartPathFromArray v C i.succ) := by
  intro i
  rw [List.get_ofFn]
  exact hg ⟨i.val, by simpa only [List.length_ofFn] using i.isLt⟩

theorem markedChartPath_good {n B : ℕ}
    (ν : FiniteLaw (Chart (walkLandmarks n) B))
    (ω : MarkedPath (ConcreteChartState ν) (ConcreteChartEdge ν) n)
    (hv : markedValid (concreteChartChain ν) ω)
    (hg : ∀ i : Fin n, concreteChartGood (ω.2 i)) :
    ∀ i : Fin n, Chart.Good (letterOrderIso (concreteChartPathLetters ω i))
      (markedChartPath ν ω i.castSucc) (markedChartPath ν ω i.succ) := by
  intro i
  rw [markedChartPath_source ν ω hv i, markedChartPath_target ν ω i]
  exact hg i

theorem rawChartEdgeSum_eq_walkSum {n B : ℕ}
    (ν : FiniteLaw (Chart (walkLandmarks n) B))
    (ω : MarkedPath (ConcreteChartState ν) (ConcreteChartEdge ν) n)
    (hv : markedValid (concreteChartChain ν) ω) :
    rawChartWalkSum (List.ofFn (concreteChartPathLetters ω))
      (chartPathFromArray (concreteChartPathLetters ω) (markedChartPath ν ω)) =
      edgeSum (rawChartEdgeLabel ν) ω := by
  rw [rawChartWalkSum_ofFn]
  unfold edgeSum
  apply Finset.sum_congr rfl
  intro i _
  rw [markedChartPath_source ν ω hv i, markedChartPath_target ν ω i]
  rfl

theorem rawChartEdgeSum_reduced_displacement (N : OrderedNorm) {n B : ℕ}
    (hn : 0 < n) (ν : FiniteLaw (Chart (walkLandmarks n) B))
    (ω : MarkedPath (ConcreteChartState ν) (ConcreteChartEdge ν) n)
    (hv : markedValid (concreteChartChain ν) ω)
    (hne : reduceWord (List.ofFn (concreteChartPathLetters ω)) ≠ [])
    (hg : ∀ i : Fin n, concreteChartGood (ω.2 i)) :
    (reducedLength (List.ofFn (concreteChartPathLetters ω)) : ℝ) *
        N.alternatingNorm (walkWindowLength n) ≤
      6 * N (edgeSum (rawChartEdgeLabel ν) ω) := by
  have h := rawChartWalkSum_displacement N hn
    (List.ofFn (concreteChartPathLetters ω))
    (by simpa only [List.length_ofFn] using (le_refl n)) hne
    (chartPathFromArray (concreteChartPathLetters ω) (markedChartPath ν ω))
    (chartPathFromArray_good (concreteChartPathLetters ω) (markedChartPath ν ω)
      (markedChartPath_good ν ω hv hg))
  rw [rawChartEdgeSum_eq_walkSum ν ω hv] at h
  exact h

theorem rawChartEdgeSum_displacement (N : OrderedNorm) {n B : ℕ}
    (hn : 0 < n) (ν : FiniteLaw (Chart (walkLandmarks n) B))
    (ω : MarkedPath (ConcreteChartState ν) (ConcreteChartEdge ν) n)
    (hvalid : markedValid (concreteChartChain ν) ω)
    (hell : (n : ℝ) / 4 ≤
      (reducedLength (List.ofFn (concreteChartPathLetters ω)) : ℝ))
    (hgood : ∀ i : Fin n, concreteChartGood (ω.2 i)) :
    (n : ℝ) * N.alternatingNorm (walkWindowLength n) / 24 ≤
      N (edgeSum (rawChartEdgeLabel ν) ω) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hne : reduceWord (List.ofFn (concreteChartPathLetters ω)) ≠ [] := by
    intro hz
    have hzero : reducedLength (List.ofFn (concreteChartPathLetters ω)) = 0 := by
      simp only [reducedLength, hz, List.length_nil]
    rw [hzero, Nat.cast_zero] at hell
    linarith
  have hraw := rawChartEdgeSum_reduced_displacement N hn ν ω hvalid hne hgood
  have hmul := mul_le_mul_of_nonneg_right hell
    (N.alternatingNorm_nonneg (walkWindowLength n))
  nlinarith

end MarkovSuperreflexivity

end

end OAI
