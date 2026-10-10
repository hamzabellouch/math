import OAI.Combinatorics.ContingencyTables.Transport.RealKernelApproximation
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperFiniteSampler
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperCorrectionBudget

namespace OAI

/-! # Exact residual correction of the initialized finite sampler -/

namespace ContingencyTables.FirstSuccess
open ResidualMixture
open scoped BigOperators Classical

lemma variation_point_le {X : Type*} [Fintype X] (p q : RationalLaw X) (x : X) :
    |p.mass x-q.mass x| ≤ variation p q := by
  classical
  have hm : (∑ y,(p.mass y:ℝ))=∑ y,(q.mass y:ℝ) := by
    exact_mod_cast p.total.trans q.total.symm
  have h := RealKernelApproximation.distance_event
    (fun y => (p.mass y:ℝ)) (fun y => (q.mass y:ℝ)) hm {x}
  simp only [Finset.sum_singleton] at h
  have hd : RealKernelApproximation.distance (fun y => (p.mass y:ℝ))
      (fun y => (q.mass y:ℝ))=(variation p q:ℝ) := by
    simp only [RealKernelApproximation.distance,variation,Rat.cast_div,Rat.cast_sum,
      Rat.cast_abs,Rat.cast_sub,Rat.cast_ofNat]
  rw [hd] at h
  exact_mod_cast h

/-- Total variation at most the square of the rare-branch probability
implies the exact pointwise domination required by residual correction. -/
theorem residual_from_variation {X : Type*} [Fintype X] [Nonempty X]
    (p : RationalLaw X) (delta : ℚ) (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hcard : (Fintype.card X:ℚ)*delta ≤ 1)
    (herror : variation p (uniformLaw (α := X)) ≤ delta^2) :
    ∃ q : RationalLaw X,∀ x,(1-delta)*p.mass x+delta*q.mass x=uniformMass (α := X) := by
  apply exact_correction p hd hd1 hcard
  intro x
  have h := variation_point_le p (uniformLaw (α := X)) x
  have hu : (uniformLaw (α := X)).mass x=uniformMass (α := X) := rfl
  rw [hu] at h
  linarith [(abs_le.mp (h.trans herror)).2]

end ContingencyTables.FirstSuccess

namespace ContingencyTables.SmallGraphProfiles
open ResidualMixture FirstSuccess FairBits CompletionCounts
open scoped BigOperators Classical

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)
variable (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
variable (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
variable {q : ℕ}
variable (e : ({i : LargeRows r ((dimensionAllowance (I := I) (J := J))^20) // i≠i₀} ×
  {j : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20) // j≠j₀}) ≃ Fin q)
local notation "d" => dimensionAllowance (I := I) (J := J)
local notation "D" => correctionPrecision r c

/-- The rare correction law for the actual initialized finite experiment.
This establishes its exact probability identity; tabulation and execution
of this law are separate implementation obligations. -/
theorem initialized_residual_correction (htotal : (∑ i,r i)=∑ j,c j)
    (a : GridBoundary.Grid (I := Fin q) (4*d^8))
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q) (4*d^8))) :
    let _ : Nonempty (Table r c) := ⟨GreedyFeasibleTable.reindexed r c htotal⟩
    let p := mapLaw (uniformLaw (α := Fin (finiteSamplerBits r c (2*D)) → Bool))
      (initializedFiniteDraw r c i₀ j₀ e (2*D) htotal a)
    ∃ residual : RationalLaw (Table r c),∀ x,
      (1-1/(2:ℚ)^D)*p.mass x+(1/(2:ℚ)^D)*residual.mass x=uniformMass (α := Table r c) := by
  let : Nonempty (Table r c) := ⟨GreedyFeasibleTable.reindexed r c htotal⟩
  have hd : 1 ≤ d := by unfold dimensionAllowance; omega
  have hb : 1 ≤ smallBinaryLength r c := hd.trans (smallBinaryLength_parameters r c).2.1
  have hD : 1 ≤ D := Nat.mul_le_mul (one_le_pow₀ hd) (one_le_pow₀ hb)
  apply residual_from_variation
  · exact one_div_pos.mpr (pow_pos (by norm_num) _)
  · exact (div_le_one (pow_pos (by norm_num) _)).mpr (one_le_pow₀ (by norm_num))
  · exact correction_card_mass r c
  · have h := initializedFiniteDraw_variation r c i₀ j₀ e (2*D) (by omega) htotal a hPL hCheeger
    have he : (1/(2:ℚ)^D)^2=1/(2:ℚ)^(2*D) := by
      rw [div_pow,one_pow,←pow_mul,Nat.mul_comm D 2]
    rw [he]
    apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_one,Rat.cast_ofNat] using h

end
end ContingencyTables.SmallGraphProfiles

end OAI
