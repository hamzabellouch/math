import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkResidueJointAverage
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkResidueNormSumTests
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairedFrequencyAverageRingUnit

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkDiagramFrequencyAverage
open Construction Characters HistoryFrequencyResidues HistoryCRTIntegration
open HistoryBulkResidueNormSum HistoryPairedFrequencyAverage ResidueHaar

theorem norm_average_le_avg_norm {α : Type*} [Fintype α] (f : α→ℂ) :
    ‖average f‖ ≤ BinaryExposure.avg (fun a=>‖f a‖) := by
  rw [average,norm_mul]
  simp only [norm_inv,norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem norm_average_average_le {α β : Type*} [Fintype α] [Fintype β] (f : α→β→ℂ) :
    ‖average (fun a=>average (f a))‖ ≤
      BinaryExposure.avg (fun b=>BinaryExposure.avg (fun a=>‖f a b‖)) := by
  rw [HistoryBulkResidueCRT.average_swap f]
  apply (norm_average_le_avg_norm _).trans
  unfold BinaryExposure.avg
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro b hb
  exact norm_average_le_avg_norm (fun a=>f a b)

theorem canonical_unit_average_le (K : ℕ) {l m : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside) :
    let : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
    ‖average (fun z : UnitPair ((pairedFrequencyProduct h k)^(K+2))=>
      average (canonicalRTest (m:=m) K h k (z.1,z.2)))‖ ≤
      canonicalUnitBulkAverage K h k hs ks m := by
  let : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
  exact norm_average_average_le _

theorem canonical_mixed_average_le (K : ℕ) {l m : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside) :
    let : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
    ‖average (fun z : MixedPair ((pairedFrequencyProduct h k)^(K+2))=>
      average (canonicalRTest (m:=m) K h k (z.1,z.2)))‖ ≤
      canonicalRingUnitBulkAverage K h k hs ks m := by
  let : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
  exact norm_average_average_le _

theorem arrayEquiv_projections {ι : Type*} [Fintype ι] [DecidableEq ι]
    {D R : ℕ} (hc : D.Coprime R) (x : ι→(ZMod (D*R))ˣ) :
    (HistoryBulkResidueCRT.arrayEquiv hc x).1=(fun i=>ZMod.unitsMap (Nat.dvd_mul_right D R) (x i)) ∧
    (HistoryBulkResidueCRT.arrayEquiv hc x).2=(fun i=>ZMod.unitsMap (Nat.dvd_mul_left R D) (x i)) := by
  constructor
  · funext i
    apply Units.ext
    exact HistoryBulkResidueCRT.arrayEquiv_left_coe hc x i
  · funext i
    apply Units.ext
    exact HistoryBulkResidueCRT.arrayEquiv_right_coe hc x i

end Ostmann.Arithmetic.HistoryBulkDiagramFrequencyAverage

end

end OAI
