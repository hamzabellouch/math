import OAI.Probability.DilutedSpin.ReservoirShapeLimit
import OAI.Probability.DilutedSpin.RootLogComparison

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower
open scoped NNReal BigOperators Topology
variable {p : ℕ}

noncomputable def reservoirLaw (M : Model p) (N L : ℕ) :=
  fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
    (markLaw (weights L) N) (reservoirRate M.alpha (p-1) N) (scoreRate N)
instance reservoirLaw_prob (M : Model p) (N L : ℕ) : IsProbabilityMeasure (reservoirLaw M N L) := by
  unfold reservoirLaw
  infer_instance

def physicalSpin (N L : ℕ) (y : FinitePath (Fin N → Spin) (L+1)) (i : Site N) : Spin :=
  readSpin (KernelTower.terminalState L y) i

noncomputable def reservoirTrialLaw (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) : Hierarchy (L+1) :=
  rootEncodingLaw
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (fun i : Labels L (Site N) => prior i.1.1) (gridExponents L) (physicalBase M C H N)
    (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
    (fun y i => spin (physicalSpin N L y i)) (measurable_physicalBase M C H N) (reservoirLaw M N L)

noncomputable def reservoirInsertion (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (a : ℕ) (F : (Fin a → Spin) → ℝ) : ℝ :=
  ∫ z, sameInsertionAverage
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (fun i : Labels L (Site N) => prior i.1.1) (gridExponents L) (physicalBase M C H N)
    (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
    (physicalSpin N L) a F z ∂reservoirLaw M N L

lemma grid_succ_eq (L : ℕ) : (fun j : Fin (L+1) => grid (L+1) 0 (L+1) j.succ) = gridExponents L := by
  funext j
  have hh := congr_fun (gridExponents_cons L) j.succ
  simpa only [Fin.cons_succ] using hh.symm

lemma reservoirInsertion_bound (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (a : ℕ) (F : (Fin a → Spin) → ℝ) {D : ℝ} (hF : ∀ s, |F s|≤D) :
    |reservoirInsertion M C H N L u a F|≤D := by
  apply abs_integral_le_bound
  intro z
  exact sameInsertionAverage_bound _ _ _ _ _ _ (gridExponents_pos L) a F hF z

 
lemma reservoirInsertion_comparison (M : Model p) (C H : ℝ) (N L : ℕ) (hN : 0<N)
    (u : Spec L×ℕ → ℝ) (a : ℕ) (F : (Fin a → Spin) → ℝ) {D : ℝ}
    (hD : 0≤D) (hF : ∀ s, |F s|≤D) (K : ℕ) :
    |reservoirInsertion M C H N L u a F-
      trialLog L (reservoirTrialLaw M C H N L u)
        (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog F)| ≤
      2*(∑' k : ℕ, |insertionRadius D|^(k+K+1)/(k+K+1))+
      ∑ k∈Finset.range K, |insertionRadius D|^(k+1)/(k+1)*((a:ℝ)*
        qExpect (grid (L+1) 0 (L+1)) (reservoirShapeDeviation M C H N L u) k (single (L+1))) := by
  let T := KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L
  let Q := fun i : Labels L (Site N) => prior i.1.1
  let base := physicalBase (L := L) M C H N
  let old := dictionaryFactor (observableAt direction N) (observableAt anchor N) u
  have hV := terminalInterior_rootTower hN Q (gridExponents L) base old
  have htrial := integral_independentInsertion_trialLog (reservoirLaw M N L) T Q
    (gridExponents L) base old (physicalSpin N L) (measurable_physicalBase M C H N) a F
    (gridExponents_pos L) (gridExponents_last L) hV
  change |reservoirInsertion M C H N L u a F - _|≤_
  rw [show trialLog L (reservoirTrialLaw M C H N L u)
      (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog F) = _ from htrial.symm]
  have hqpos (j : Fin (L+1)) : grid (L+1) 0 (L+1) j.succ≠0 := by
    have h := congr_fun (grid_succ_eq L) j
    rw [h]
    exact ne_of_gt (gridExponents_pos L j)
  have hv' : ∀ z i, TerminalInterior L (rootTower T Q
      (fun j => grid (L+1) 0 (L+1) j.succ) base old z)
      (fun y => rootVector (fun w j => spin (physicalSpin N L w j)) z y i) := by
    rw [grid_succ_eq]
    exact hV
  have hh := integral_root_log_comparison (reservoirLaw M N L) T Q
    (grid (L+1) 0 (L+1)) base old (physicalSpin N L) (measurable_physicalBase M C H N)
    (grid_strictMono (by omega)).monotone grid_nonneg hqpos
    (by simp [grid]) (grid_last (by omega)) hv' a F hD hF K
  simp only [grid_succ_eq] at hh
  exact hh
end DilutedSpinGlass.UniversalDictionary

end

end OAI
