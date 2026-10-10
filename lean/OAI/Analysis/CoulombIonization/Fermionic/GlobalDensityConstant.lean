import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.Density
import OAI.Analysis.CoulombIonization.Variational.Space

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
open MeasureTheory Set Metric
open scoped ENNReal
namespace CoulombAtom

namespace Pauli
open CoulombDensity

def globalDensityConstant : ℝ :=
  192 + (8192/3:ℝ)*(8*Real.pi*(3/8192:ℝ)^(-3/2:ℝ)+3) + 8192/3

lemma globalDensityConstant_pos : 0 < globalDensityConstant := by
  unfold globalDensityConstant
  positivity

lemma density_nuclear_energy {N : ℕ} (ψ : FormVector (N+1)) (hψ : FormAdmissible ψ) (Z : ℝ) :
    (∫ x, density ψ hψ.1 x*(Z/‖x‖)) =
      Z*(∑ s : Spins (N+1), ∑ i : Fin (N+1),
        ∫ x : Configuration (N+1), ‖ψ.value s x‖^2/‖x i‖) := by
  calc
    _ = ∫ x, Z*(density ψ hψ.1 x/‖x‖) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by ring)
    _ = _ := by rw [integral_const_mul,(density_coulomb_integral ψ hψ).2]

theorem global_density_of_energy_le {N : ℕ} {Z δ : ℝ}
    (hZ : 1 ≤ Z) (hδ : 0 ≤ δ) (hN : (N+1:ℝ) ≤ 3*Z)
    (ψ : FormVector (N+1)) (hψ : FormAdmissible ψ) (he : formEnergy Z ψ ≤ δ) :
    (∫ x, density ψ hψ.1 x^(5/3:ℝ)) ≤ globalDensityConstant * (Z^(7/3:ℝ)+δ) := by
  let D := ∫ x, density ψ hψ.1 x^(5/3:ℝ)
  let G := ∑ s : Spins (N+1), ∑ i : Fin (N+1), ∑ a : Fin 3,
    ∫ x : Configuration (N+1), ‖ψ.gradient s i a x‖^2
  let A := ∑ s : Spins (N+1), ∑ i : Fin (N+1),
    ∫ x : Configuration (N+1), ‖ψ.value s x‖^2/‖x i‖
  let B := 8*Real.pi*(3/8192:ℝ)^(-3/2:ℝ)+3
  have hDp : 0 ≤ D := integral_nonneg (fun _ => Real.rpow_nonneg (density_nonneg _ _ _) _)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hZp : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hpow : Z ≤ Z^(7/3:ℝ) := by
    calc
      _ = Z^(1:ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)
  have hp : 0 ≤ Z^(7/3:ℝ) := Real.rpow_nonneg hZp.le _
  have hlt : D ≤ 32*(N+1:ℝ)+(2048/3:ℝ)*G := density_power_bound ψ hψ
  have ha : Z*A ≤ (3/8192:ℝ)*D + B*Z^(7/3:ℝ) := by
    have h := nuclear_density_scaled (density ψ hψ.1) (density_nonneg ψ hψ.1)
      (density_integrable ψ hψ.1) (density_power_integrable ψ hψ) hZp
      (by norm_num : (0:ℝ) < 3/8192) (by rw [density_mass ψ hψ]; exact hN)
    rwa [density_nuclear_energy ψ hψ Z] at h
  have hr : 0 ≤ (∑ s : Spins (N+1), ∑ i : Fin (N+1), ∑ j : Fin (N+1),
      if i < j then (∫ x : Configuration (N+1), ‖ψ.value s x‖^2/‖x i-x j‖) else 0) := by
    apply Finset.sum_nonneg
    intro s _
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    split_ifs <;> positivity
  have hkin : (1/2:ℝ)*G - Z*A ≤ δ := by
    dsimp [formEnergy] at he
    dsimp [G,A]
    linarith
  have hbase : D ≤ (192+(8192/3:ℝ)*B)*Z^(7/3:ℝ)+(8192/3:ℝ)*δ := by
    nlinarith
  have hc : globalDensityConstant = 192+(8192/3:ℝ)*B+8192/3 := rfl
  rw [hc]
  nlinarith
end Pauli
end CoulombAtom

end

end OAI
