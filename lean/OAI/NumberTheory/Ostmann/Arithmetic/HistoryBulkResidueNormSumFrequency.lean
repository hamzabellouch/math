import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairedFrequencyAverageBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairedFrequencyAverageHaarBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkResidueNormSum
open Construction Characters FrequencyExposure HistoryFrequencyResidues
open HistorySignedResidueFactorization HistoryPairedFrequencyAverage HistoryPairedFrequencyAverageHaar

theorem leafIndicator_norm_le (K R : ℕ) (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) {l : ℕ} (h k : History l)
    (p : List Bool) (c : PairedContext R)
    (z : BinaryHaar.Leaves (ZMod (R^(K+2)))ˣ l) :
    ‖leafIndicator K R d f h k p c z‖ ≤ 1 := by
  classical
  unfold leafIndicator guardIndicator
  split_ifs <;> simp

def canonicalRTest (K : ℕ) {l m : ℕ} (h k : History l)
    (z : ZMod ((pairedFrequencyProduct h k)^(K+2)) × ZMod ((pairedFrequencyProduct h k)^(K+2)))
    (x : Fin (2^l)×Fin m → (ZMod ((pairedFrequencyProduct h k)^(K+2)))ˣ) : ℂ :=
  leafIndicator K (pairedFrequencyProduct h k) (frequencySchedule h k) (fixedFactorSchedule h k) h k []
    (l,initialResidueGiants K (pairedFrequencyProduct h k) z,
      initialResidueGiants K (pairedFrequencyProduct h k) z) (bulkLeaves m l x)

theorem canonicalRTest_norm_le (K : ℕ) {l m : ℕ} (h k : History l)
    (z : ZMod ((pairedFrequencyProduct h k)^(K+2)) × ZMod ((pairedFrequencyProduct h k)^(K+2)))
    (x : Fin (2^l)×Fin m → (ZMod ((pairedFrequencyProduct h k)^(K+2)))ˣ) :
    ‖canonicalRTest K h k z x‖ ≤ 1 := leafIndicator_norm_le _ _ _ _ _ _ _ _ _

def independentRTest (K : ℕ) {l m : ℕ} (h k : History l)
    (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (z : ZMod ((pairedFrequencyProduct h k)^(K+2)) × ZMod ((pairedFrequencyProduct h k)^(K+2)))
    (x : Fin (2^l)×Fin m → (ZMod ((pairedFrequencyProduct h k)^(K+2)))ˣ) : ℂ :=
  let R := pairedFrequencyProduct h k
  let hF := fun s (hs : s∈h.frequencies) =>
    FrequencyPrecision.frequency_dvd_product (List.mem_append_left k.frequencies hs)
  let kF := fun s (hs : s∈k.frequencies) =>
    FrequencyPrecision.frequency_dvd_product (List.mem_append_right h.frequencies hs)
  leafIndicator K R (frequencyScheduleAux R h h hF hF) (fixedFactorSchedule h h) h h []
    (l,initialResidueGiants K R z,initialResidueGiants K R z) (bulkLeaves m l x) *
  leafIndicator K R (frequencyScheduleAux R k k kF kF) (fixedFactorSchedule k k) k k []
    (l,initialResidueGiants K R z,initialResidueGiants K R z) (bulkLeaves m l (fun i => x (σ i)))

theorem independentRTest_norm_le (K : ℕ) {l m : ℕ} (h k : History l)
    (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (z : ZMod ((pairedFrequencyProduct h k)^(K+2)) × ZMod ((pairedFrequencyProduct h k)^(K+2)))
    (x : Fin (2^l)×Fin m → (ZMod ((pairedFrequencyProduct h k)^(K+2)))ˣ) :
    ‖independentRTest K h k σ z x‖ ≤ 1 := by
  unfold independentRTest
  rw [norm_mul]
  exact (mul_le_mul (leafIndicator_norm_le _ _ _ _ _ _ _ _ _)
    (leafIndicator_norm_le _ _ _ _ _ _ _ _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

end Ostmann.Arithmetic.HistoryBulkResidueNormSum

end

end OAI
