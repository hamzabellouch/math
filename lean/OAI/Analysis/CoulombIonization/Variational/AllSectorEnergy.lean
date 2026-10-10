import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.GlobalDensityConstant

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

def allSectorEnergy (Z : ℝ) : ℝ := sInf (Set.range (energy Z))

lemma allSectorEnergy_nonpos (Z : ℝ) : allSectorEnergy Z ≤ 0 := by
  by_cases hb : BddBelow (Set.range (energy Z))
  · exact (csInf_le hb (Set.mem_range_self 0)).trans_eq (by simp [energy])
  · simp only [allSectorEnergy,Real.sInf_of_not_bddBelow hb,le_refl]

namespace Pauli

def spatialDensity : {N : ℕ} → (ψ : FormVector N) →
    (∀ s, MemLp (ψ.value s) 2) → Space → ℝ
  | 0, _, _ => 0
  | _+1, ψ, hψ => density ψ hψ

theorem global_density_unshifted {N : ℕ} {Z δ : ℝ}
    (hZ : 1 ≤ Z) (hδ : 0 ≤ δ) (hN : (N:ℝ) ≤ 3*Z)
    (ψ : FormVector N) (hψ : FormAdmissible ψ)
    (he : formEnergy Z ψ ≤ allSectorEnergy Z + δ) :
    (∫ x, spatialDensity ψ hψ.1 x^(5/3:ℝ)) ≤
      globalDensityConstant*(Z^(7/3:ℝ)+δ) := by
  cases N with
  | zero =>
    simp only [spatialDensity,Pi.zero_apply,Real.zero_rpow (by norm_num : (5/3:ℝ) ≠ 0),integral_zero]
    exact mul_nonneg globalDensityConstant_pos.le
      (add_nonneg (Real.rpow_nonneg (le_trans zero_le_one hZ) _) hδ)
  | succ N =>
    exact global_density_of_energy_le hZ hδ (by exact_mod_cast hN) ψ hψ
      (he.trans (by linarith [allSectorEnergy_nonpos Z]))
end Pauli
end CoulombAtom

end

end OAI
