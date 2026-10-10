import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceConfigurationsFinite
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceRoleBoundsGeometry

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HigherBiasSourceRoleBounds
open Construction Preliminaries HigherBiasSource

theorem configuration_list_sum_error {k : ℕ} (cfg : SourceConfiguration k)
    (T : Fin (k+1) → ℝ) {c : ℝ}
    (hlist : ∀ j, |((cfg.2 j).sum:ℝ)-T j| ≤ 6/c) :
    |(∑ j, ((cfg.2 j).sum:ℝ))-(∑ j,T j)| ≤ (k+1:ℕ)*(6/c) := by
  rw [←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ j, |((cfg.2 j).sum:ℝ)-T j|) ≤ ∑ _j : Fin (k+1), 6/c :=
      Finset.sum_le_sum (fun j _ => hlist j)
    _ = _ := by simp

theorem configuration_target_error {k : ℕ} (cfg : SourceConfiguration k)
    (J : ℤ) (T : Fin (k+1) → ℝ) {c target : ℝ}
    (hlist : ∀ j, |((cfg.2 j).sum:ℝ)-T j| ≤ 6/c)
    (htarget : 2*((J:ℝ)+(∑ i,(cfg.1 i:ℝ))+(∑ j,T j))=target) :
    |2*((J:ℝ)+(∑ i,(cfg.1 i:ℝ))+(∑ j,((cfg.2 j).sum:ℝ)))-target| ≤
      2*(k+1:ℕ)*(6/c) := by
  rw [←htarget]
  have he : 2*((J:ℝ)+(∑ i,(cfg.1 i:ℝ))+(∑ j,((cfg.2 j).sum:ℝ)))-
      2*((J:ℝ)+(∑ i,(cfg.1 i:ℝ))+(∑ j,T j)) =
      2*((∑ j,((cfg.2 j).sum:ℝ))-(∑ j,T j)) := by ring
  rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  exact (mul_le_mul_of_nonneg_left (configuration_list_sum_error cfg T hlist)
    (by norm_num)).trans_eq (by ring)

theorem halfRole_target_of_index_error {Q m nc : ℕ} (bulk top : Finset (PrimeUpTo Q))
    (E : Fin nc → Finset (PrimeUpTo Q)) (indices : Fin nc → ℤ)
    (hE : ∀ i, 0 < primeShellMass
      (halfRoleShells bulk top m (fun j => boundedRawLogCell (E j) (indices j)) i))
    (w : Fin ((m+1)+nc) → PrimeUpTo Q)
    (hw : (characterTuplePrior
      (halfRoleShells bulk top m (fun j => boundedRawLogCell (E j) (indices j))) hE).mass w ≠ 0)
    (J : ℤ) (hJ : HigherBiasSourceWord.binIndicator J (originalWord w) ≠ 0)
    {logX Δ₀ D : ℝ} (hD : |2*((J:ℝ)+∑ i,(indices i:ℝ))-(logX+Δ₀)| ≤ D) :
    logX+Δ₀-(D+2*((nc:ℝ)+1)) ≤ 2*Real.log (characterTupleProduct w:ℝ) ∧
      2*Real.log (characterTupleProduct w:ℝ) ≤ logX+Δ₀+(D+2*((nc:ℝ)+1)) := by
  have h := doubled_halfRole_log_target bulk top E indices hE w hw J hJ hD
  obtain ⟨hl,hu⟩ := abs_le.mp h
  constructor <;> linarith

end Ostmann.Characters.HigherBiasSourceRoleBounds

end

end OAI
