import OAI.NumberTheory.Jacobsthal.Renewal.SourceSelectedCompactOccupation

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.FullHistoryPrimeOccupation

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling PersistentFailureFlag
open FiniteHistoryTransport ActualCoupledHistories SourceSelectedCompactOccupation
open PrimeCompactWeights PrimeFamilyOccupation ErdosPrimeInputs.PrimePrefixMass

variable {w ell S B : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem prime_coordinate (mesh : ℝ) (N k : ℕ) (hk : k ≤ N) :
    (sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N).map
      (fun h => (h ⟨k,by simpa using hk⟩).1.1) = pathLaw w ell S start k := by
  calc
    _ = ((sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N).map
        (fun h => h ⟨k,by simpa using hk⟩)).map (fun q => q.1.1) := by
      exact (Measure.map_map
        (f := fun h : Hist (FlagState (JointState w ell S start)) N => h ⟨k,Finset.mem_Iic.mpr hk⟩)
        (g := fun q : FlagState (JointState w ell S start) => q.1.1)
        (by fun_prop) (by fun_prop)).symm
    _ = _ := by rw [sourceHistoryLaw_coordinate hw hell hS0 hS hr hs hsS mesh N k hk,
      FlaggedSourceStart.sourceLaw_prime]

noncomputable def fullListReward (w B : ℝ) {ell S : ℝ} (start : Node)
    (F : List ℕ → ℝ) (N : ℕ) (h : Hist (FlagState (JointState w ell S start)) N) : ℝ≥0∞ :=
  ∑ j : Fin N, ENNReal.ofReal
    (scaledWeight w B start (h ⟨j,Finset.mem_Iic.mpr j.isLt.le⟩).1.1 *
      listReward F (h ⟨j,Finset.mem_Iic.mpr j.isLt.le⟩).1.1)

theorem fullListReward_measurable (F : List ℕ → ℝ) (N : ℕ) :
    Measurable (fullListReward w B (ell:=ell) (S:=S) start F N) := by
  unfold fullListReward
  apply Finset.measurable_sum
  intro j _
  exact (measurable_of_countable (fun z : ChainState w ell S start =>
    ENNReal.ofReal (scaledWeight w B start z*listReward F z))).comp
      ((measurable_fst.comp measurable_fst).comp (measurable_pi_apply _))

theorem fullListReward_integral (mesh : ℝ) (N : ℕ) (F : List ℕ → ℝ) :
    (∫⁻ h,fullListReward w B start F N h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N) =
      ∑ n ∈ range N, ∫⁻ z,ENNReal.ofReal (scaledWeight w B start z*listReward F z)
        ∂pathLaw w ell S start n := by
  unfold fullListReward
  rw [lintegral_finsetSum]
  · rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    have hm : Measurable (fun z : ChainState w ell S start =>
        ENNReal.ofReal (scaledWeight w B start z*listReward F z)) := measurable_of_countable _
    rw [← prime_coordinate hw hell hS0 hS hr hs hsS mesh N j j.isLt.le,
      lintegral_map hm (by exact (measurable_fst.comp measurable_fst).comp (measurable_pi_apply _))]
  · intro j _
    exact (measurable_of_countable (fun z : ChainState w ell S start =>
      ENNReal.ofReal (scaledWeight w B start z*listReward F z))).comp
        ((measurable_fst.comp measurable_fst).comp (measurable_pi_apply _))

theorem finite_family_full_history (hB : 0 < B) (hsize : start.gap ≤ (23/10:ℝ)*B)
    (mesh : ℝ) (F : List ℕ → ℝ) (hF : ∀ ps,allowed w ell S start ps → 0 ≤ F ps) :
    (∫⁻ h,fullListReward w B start F (LowStateHorizon.sourceHorizon S B) h
      ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh (LowStateHorizon.sourceHorizon S B)) =
      ENNReal.ofReal (B^2*(∑ ps ∈ retainedPrefixes w ell S start,prefixWeight ps*F ps)) := by
  rw [fullListReward_integral]
  exact finite_nonnegative_original_occupation hw hell hS0 hS hr hs hsS hB hsize F hF

end NumberTheoryLean.FullHistoryPrimeOccupation

end

end Erdos970

end OAI
