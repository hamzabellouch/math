import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceConfigurationRoles
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceRoleBoundsTargets

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HigherBiasSourceRoleBounds
open Construction Preliminaries HigherBiasSource HigherBiasSourceWord

theorem configCellIndices_target_error {k : ℕ} (cfg : SourceConfiguration k)
    (J : ℤ) (T : Fin (k+1) → ℝ) {c target : ℝ}
    (hlist : ∀ j, |((cfg.2 j).sum:ℝ)-T j| ≤ 6/c)
    (htarget : 2*((J:ℝ)+(∑ i,(cfg.1 i:ℝ))+(∑ j,T j))=target) :
    |2*((J:ℝ)+∑ i,(configCellIndices cfg i:ℝ))-target| ≤ 2*(k+1:ℕ)*(6/c) := by
  rw [configCellIndices_sum]
  simpa only [add_assoc] using configuration_target_error cfg J T hlist htarget

def configurationProductWidth (k : ℕ) (c : ℝ) : ℝ :=
  2*(k+1:ℕ)*(6/c)+2*(4*((k:ℝ)+1)*Real.exp (2*(k:ℝ)/10000)+1)

theorem configuration_paired_product_window {Q m k : ℕ}
    (bulk top : Finset (PrimeUpTo Q)) (cfg : SourceConfiguration k)
    (E : Fin (configCellCount cfg) → Finset (PrimeUpTo Q))
    (hE : ∀ i, 0 < primeShellMass (halfRoleShells bulk top m
      (fun j => boundedRawLogCell (E j) (configCellIndices cfg j)) i))
    (w v : Fin ((m+1)+configCellCount cfg) → PrimeUpTo Q)
    (hw : (characterTuplePrior (halfRoleShells bulk top m
      (fun j => boundedRawLogCell (E j) (configCellIndices cfg j))) hE).mass w ≠ 0)
    (hv : (characterTuplePrior (halfRoleShells bulk top m
      (fun j => boundedRawLogCell (E j) (configCellIndices cfg j))) hE).mass v ≠ 0)
    (J : ℤ) (hJw : binIndicator J (originalWord w) ≠ 0)
    (hJv : binIndicator J (originalWord v) ≠ 0)
    (T : Fin (k+1) → ℝ) {c X Δ₀ : ℝ}
    (hlist : ∀ j, |((cfg.2 j).sum:ℝ)-T j| ≤ 6/c)
    (htarget : 2*((J:ℝ)+(∑ i,(cfg.1 i:ℝ))+(∑ j,T j))=Real.log X+Δ₀)
    (hlength : ∀ j, ((cfg.2 j).length:ℝ) ≤ 2*Real.exp (2*(k:ℝ)/10000)) :
    |Real.log ((characterTupleProduct w*characterTupleProduct v:ℕ):ℝ)-
      (Real.log X+Δ₀)| ≤ configurationProductWidth k c := by
  have h := paired_halfRole_log_target bulk top E (configCellIndices cfg) hE w v
    hw hv J hJw hJv (configCellIndices_target_error cfg J T hlist htarget)
  apply h.trans
  have hn := configCellCount_le cfg hlength
  unfold configurationProductWidth
  linarith

theorem configuration_paired_product_endpoints {Q m k : ℕ}
    (bulk top : Finset (PrimeUpTo Q)) (cfg : SourceConfiguration k)
    (E : Fin (configCellCount cfg) → Finset (PrimeUpTo Q))
    (hE : ∀ i, 0 < primeShellMass (halfRoleShells bulk top m
      (fun j => boundedRawLogCell (E j) (configCellIndices cfg j)) i))
    (w v : Fin ((m+1)+configCellCount cfg) → PrimeUpTo Q)
    (hw : (characterTuplePrior (halfRoleShells bulk top m
      (fun j => boundedRawLogCell (E j) (configCellIndices cfg j))) hE).mass w ≠ 0)
    (hv : (characterTuplePrior (halfRoleShells bulk top m
      (fun j => boundedRawLogCell (E j) (configCellIndices cfg j))) hE).mass v ≠ 0)
    (J : ℤ) (hJw : binIndicator J (originalWord w) ≠ 0)
    (hJv : binIndicator J (originalWord v) ≠ 0)
    (T : Fin (k+1) → ℝ) {c X Δ₀ : ℝ}
    (hlist : ∀ j, |((cfg.2 j).sum:ℝ)-T j| ≤ 6/c)
    (htarget : 2*((J:ℝ)+(∑ i,(cfg.1 i:ℝ))+(∑ j,T j))=Real.log X+Δ₀)
    (hlength : ∀ j, ((cfg.2 j).length:ℝ) ≤ 2*Real.exp (2*(k:ℝ)/10000)) :
    Real.log X+Δ₀-configurationProductWidth k c ≤
      Real.log ((characterTupleProduct w*characterTupleProduct v:ℕ):ℝ) ∧
    Real.log ((characterTupleProduct w*characterTupleProduct v:ℕ):ℝ) ≤
      Real.log X+Δ₀+configurationProductWidth k c := by
  have h := configuration_paired_product_window bulk top cfg E hE w v hw hv J hJw hJv
    T hlist htarget hlength
  obtain ⟨hl,hu⟩ := abs_le.mp h
  constructor <;> linarith

end Ostmann.Characters.HigherBiasSourceRoleBounds

end

end OAI
