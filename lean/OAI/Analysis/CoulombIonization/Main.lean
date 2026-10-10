import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.FullSpectral
import OAI.Analysis.CoulombIonization.Ionization.ActualTFCoefficient
import OAI.Analysis.CoulombIonization.Localization.SpinPartialOccupationKineticLintegral
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierForgottenInvariantBarrier
import OAI.Analysis.CoulombIonization.FieldAnalysis.UnshiftedField
import OAI.Analysis.CoulombIonization.Localization.UnshiftedEnsemble
import OAI.Analysis.CoulombIonization.Ionization.PricedSubsequence

namespace OAI

open Filter
open scoped Topology
noncomputable section
namespace CoulombAtom
open CoulombAnalysis

theorem actual_quantum_jointLimit : JointLimit actualTFCoefficient := by
  classical
  intro m Z hm hmtop hratio
  have hmp (j) : 0 < (m j:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hm j).1)
  have hZ (j) : 1 ≤ Z j := (hm j).1.trans (hm j).2.le
  have hmr : Tendsto (fun j => (m j:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hmtop
  let N (j : ℕ) (t : ℝ) : ℕ := if ht : 0 < t then
    Classical.choose (quantum_exists_priceMinimizes (Nat.cast_nonneg (Z j))
      (mul_pos ht (Real.rpow_pos_of_pos (hmp j) (4/3:ℝ)))) else 0
  have hN (j : ℕ) (t : ℝ) (ht : 0 < t) :
      PriceMinimizes (energy (Z j)) (t*(m j:ℝ)^(4/3:ℝ)) (N j t) := by
    dsimp only [N]
    rw [dite_eq_left ht]
    exact Classical.choose_spec (quantum_exists_priceMinimizes (Nat.cast_nonneg (Z j))
      (mul_pos ht (Real.rpow_pos_of_pos (hmp j) (4/3:ℝ))))
  have hd (t : ℝ) (ht : 0 < t) : Tendsto (fun j => scaledDeficit (Z j) (N j t) (m j))
      atTop (𝓝 (limitDeficit tfResidualCharge t)) := by
    have hh := actual_priced_deficit_limit Z (fun j => N j t)
      (fun j => fixedSectorScale t (m j)) hZ (fun j => fixedSectorScale_pos ht (hmp j))
      (fixedSectorScale_tendsto hmr) (fixedSectorScale_joint ht hmp hratio)
      (fun j => by rw [fixedSectorScale_price ht (hmp j)]; exact hN j t ht)
    have hscaled := hh.const_mul (t^(3/4:ℝ))
    simpa only [fixedSectorScale_deficit ht (hmp _),scaledDeficit,limitDeficit,mul_comm] using hscaled
  have hfixed := fixed_sector_limit_of_priced_deficit tfResidualCharge_pos
    (fun j => ⟨(hm j).1,(hm j).2.le⟩)
    (fun j => quantum_energy_antitone (Nat.cast_nonneg (Z j))) hN hd
  exact hfixed

theorem generalized_ionization : MainStatement :=
  ⟨actualTFCoefficient,actualTFCoefficient_pos,tf_actual_characterization,
    actual_quantum_jointLimit,iteratedLimits_of_jointLimit actual_quantum_jointLimit⟩

end CoulombAtom

end

end OAI
