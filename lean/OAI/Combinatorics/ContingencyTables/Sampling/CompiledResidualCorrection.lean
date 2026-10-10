import OAI.Combinatorics.ContingencyTables.Sampling.AllSamplingMachine
import OAI.Combinatorics.ContingencyTables.Transport.FiniteCorrectionLaw

namespace OAI

/-! # Exact residual correction for the compiled public draw -/

namespace ContingencyTables.SmallGraphProfiles
open ResidualMixture FirstSuccess CompletionCounts ProfilePrograms Algorithms
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "D" => correctionPrecision r c
local notation "q" => largeTailCount r (d^20)*largeTailCount c (d^20)

lemma correctionPrecision_pos : 1≤D := by
  have hd : 1≤d := by unfold dimensionAllowance; omega
  have hb : 1 ≤ smallBinaryLength r c := hd.trans (smallBinaryLength_parameters r c).2.1
  exact Nat.mul_le_mul (one_le_pow₀ hd) (one_le_pow₀ hb)

/-- The residual uses the compiled sampler's finite output law. -/
theorem scheduled_residual_correction
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q) (4*d^8)))
    (htotal : (∑ i,r i)=∑ j,c j) :
    let _ : Nonempty (Table r c) := ⟨GreedyFeasibleTable.table r c htotal⟩
    ∃ residual : RationalLaw (Table r c),∀ X,
      (1-1/(2:ℚ)^D)*
        (mapLaw (uniformLaw (α := Fin (finiteSamplerBits r c (2*D)) → Bool))
          (scheduledTableDraw r c htotal (2*D))).mass X+
        (1/(2:ℚ)^D)*residual.mass X=uniformMass (α := Table r c) := by
  let : Nonempty (Table r c) := ⟨GreedyFeasibleTable.table r c htotal⟩
  have hD := correctionPrecision_pos r c
  apply residual_from_variation
  · positivity
  · exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  · exact correction_card_mass r c
  · have hpow : (1/(2:ℚ)^D)^2=1/(2:ℚ)^(2*D) := by
      rw [div_pow,one_pow,←pow_mul,Nat.mul_comm D 2]
    rw [hpow]
    apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] using
      scheduledTableDraw_accuracy r c hPL hCheeger htotal (2*D) (by omega)

/-- Consequently the same exact mixture identity holds for every
sufficiently long execution of the physical finite-transition machine. -/
theorem public_residual_correction
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q) (4*d^8)))
    (htotal : (∑ i,r i)=∑ j,c j) (t : ℕ)
    (ht : allSamplingMachineTime (encodeSamplingInput r c (2*D))≤t) :
    ∃ residual : RationalLaw (Table r c),∀ X : Table r c,
      (1-1/(2:ℝ)^D)*tableMass allSamplingMachine (encodeSamplingInput r c (2*D)) t X.val+
        (1/(2:ℝ)^D)*(residual.mass X:ℝ)=(Fintype.card (Table r c):ℝ)⁻¹ := by
  obtain ⟨residual,hr⟩ := scheduled_residual_correction r c hPL hCheeger htotal
  refine ⟨residual,fun X => ?_⟩
  rw [allSamplingMachine_mass r c htotal (2*D) t ht]
  have h := congrArg (fun z : ℚ => (z:ℝ)) (hr X)
  simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_sub,Rat.cast_div,Rat.cast_one,
    Rat.cast_pow,Rat.cast_ofNat,Rat.cast_inv,uniformMass,Rat.cast_natCast,one_div] using h

end
end ContingencyTables.SmallGraphProfiles

end OAI
