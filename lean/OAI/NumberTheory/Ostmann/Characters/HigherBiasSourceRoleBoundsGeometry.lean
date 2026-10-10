import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceRoleBoundsNormalization

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HigherBiasSourceRoleBounds
open Construction Preliminaries HigherBiasSourceWord HigherBiasSource

def originalWord {Q m nc : ℕ} (w : Fin ((m+1)+nc) → PrimeUpTo Q) :
    Fin (m+1) → PrimeUpTo Q := fun i => w (Fin.castAdd nc i)

def cellWord {Q m nc : ℕ} (w : Fin ((m+1)+nc) → PrimeUpTo Q) :
    Fin nc → PrimeUpTo Q := fun i => w (Fin.natAdd (m+1) i)

theorem log_characterTupleProduct {Q b : ℕ} (w : Fin b → PrimeUpTo Q) :
    Real.log (characterTupleProduct w : ℝ) = ∑ i, Real.log ((w i).val : ℝ) := by
  rw [characterTupleProduct, Nat.cast_prod, Real.log_prod]
  intro i hi
  exact_mod_cast (primeUpTo_prime (w i)).ne_zero

theorem halfRole_log_split {Q m nc : ℕ} (w : Fin ((m+1)+nc) → PrimeUpTo Q) :
    Real.log (characterTupleProduct w : ℝ) =
      wordLog (originalWord w) + ∑ i, Real.log ((cellWord w i).val : ℝ) := by
  rw [log_characterTupleProduct, Fin.sum_univ_add]
  rfl

theorem wordLog_mem_bin {Q m : ℕ} (J : ℤ) (w : Fin (m+1) → PrimeUpTo Q)
    (hw : binIndicator J w ≠ 0) :
    (J:ℝ) ≤ wordLog w ∧ wordLog w < (J:ℝ)+1 := by
  have he : ⌊wordLog w⌋ = J := by
    by_contra h
    exact hw (ite_eq_right h)
  constructor
  · simpa only [he] using Int.floor_le (wordLog w)
  · simpa only [he] using Int.lt_floor_add_one (wordLog w)

theorem tuple_support_of_mass_ne_zero {Q b : ℕ} (E : Fin b → Finset (PrimeUpTo Q))
    (hE : ∀ i, 0 < primeShellMass (E i)) (w : Fin b → PrimeUpTo Q)
    (hw : (characterTuplePrior E hE).mass w ≠ 0) : ∀ i, w i ∈ E i := by
  by_contra h
  exact hw (characterTuplePrior_mass_eq_zero E hE w h)

theorem halfRole_cell_log_bounds {Q m nc : ℕ} (bulk top : Finset (PrimeUpTo Q))
    (E : Fin nc → Finset (PrimeUpTo Q)) (indices : Fin nc → ℤ)
    (hE : ∀ i, 0 < primeShellMass
      (halfRoleShells bulk top m (fun j => boundedRawLogCell (E j) (indices j)) i))
    (w : Fin ((m+1)+nc) → PrimeUpTo Q)
    (hw : (characterTuplePrior
      (halfRoleShells bulk top m (fun j => boundedRawLogCell (E j) (indices j))) hE).mass w ≠ 0) :
    ∀ i, (indices i:ℝ) ≤ Real.log ((cellWord w i).val:ℝ) ∧
      Real.log ((cellWord w i).val:ℝ) < (indices i:ℝ)+1 := by
  intro i
  have h := tuple_support_of_mass_ne_zero _ hE w hw (Fin.natAdd (m+1) i)
  simp only [halfRoleShells, Fin.append_right, boundedRawLogCell, Finset.mem_filter] at h
  exact h.2

theorem halfRole_log_bounds {Q m nc : ℕ} (bulk top : Finset (PrimeUpTo Q))
    (E : Fin nc → Finset (PrimeUpTo Q)) (indices : Fin nc → ℤ)
    (hE : ∀ i, 0 < primeShellMass
      (halfRoleShells bulk top m (fun j => boundedRawLogCell (E j) (indices j)) i))
    (w : Fin ((m+1)+nc) → PrimeUpTo Q)
    (hw : (characterTuplePrior
      (halfRoleShells bulk top m (fun j => boundedRawLogCell (E j) (indices j))) hE).mass w ≠ 0)
    (J : ℤ) (hJ : binIndicator J (originalWord w) ≠ 0) :
    (J:ℝ)+(∑ i, (indices i:ℝ)) ≤ Real.log (characterTupleProduct w:ℝ) ∧
      Real.log (characterTupleProduct w:ℝ) ≤
        (J:ℝ)+(∑ i, (indices i:ℝ))+(nc:ℝ)+1 := by
  have hword := wordLog_mem_bin J (originalWord w) hJ
  have hcell := halfRole_cell_log_bounds bulk top E indices hE w hw
  rw [halfRole_log_split]
  constructor
  · exact add_le_add hword.1 (Finset.sum_le_sum (fun i _ => (hcell i).1))
  · have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hcell i).2.le)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
    linarith

theorem doubled_halfRole_log_target {Q m nc : ℕ} (bulk top : Finset (PrimeUpTo Q))
    (E : Fin nc → Finset (PrimeUpTo Q)) (indices : Fin nc → ℤ)
    (hE : ∀ i, 0 < primeShellMass
      (halfRoleShells bulk top m (fun j => boundedRawLogCell (E j) (indices j)) i))
    (w : Fin ((m+1)+nc) → PrimeUpTo Q)
    (hw : (characterTuplePrior
      (halfRoleShells bulk top m (fun j => boundedRawLogCell (E j) (indices j))) hE).mass w ≠ 0)
    (J : ℤ) (hJ : binIndicator J (originalWord w) ≠ 0)
    {target D : ℝ} (hD : |2*((J:ℝ)+∑ i,(indices i:ℝ))-target| ≤ D) :
    |2*Real.log (characterTupleProduct w:ℝ)-target| ≤ D+2*((nc:ℝ)+1) := by
  obtain ⟨hl,hu⟩ := halfRole_log_bounds bulk top E indices hE w hw J hJ
  obtain ⟨hd₁,hd₂⟩ := abs_le.mp hD
  apply abs_le.mpr
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) nc]

theorem paired_halfRole_log_target {Q m nc : ℕ} (bulk top : Finset (PrimeUpTo Q))
    (E : Fin nc → Finset (PrimeUpTo Q)) (indices : Fin nc → ℤ)
    (hE : ∀ i, 0 < primeShellMass
      (halfRoleShells bulk top m (fun j => boundedRawLogCell (E j) (indices j)) i))
    (w v : Fin ((m+1)+nc) → PrimeUpTo Q)
    (hw : (characterTuplePrior
      (halfRoleShells bulk top m (fun j => boundedRawLogCell (E j) (indices j))) hE).mass w ≠ 0)
    (hv : (characterTuplePrior
      (halfRoleShells bulk top m (fun j => boundedRawLogCell (E j) (indices j))) hE).mass v ≠ 0)
    (J : ℤ) (hJw : binIndicator J (originalWord w) ≠ 0)
    (hJv : binIndicator J (originalWord v) ≠ 0)
    {target D : ℝ} (hD : |2*((J:ℝ)+∑ i,(indices i:ℝ))-target| ≤ D) :
    |Real.log ((characterTupleProduct w * characterTupleProduct v:ℕ):ℝ)-target| ≤
      D+2*((nc:ℝ)+1) := by
  rw [Nat.cast_mul, Real.log_mul
    (by exact_mod_cast (characterTupleProduct_pos w).ne')
    (by exact_mod_cast (characterTupleProduct_pos v).ne')]
  obtain ⟨hlw,huw⟩ := halfRole_log_bounds bulk top E indices hE w hw J hJw
  obtain ⟨hlv,huv⟩ := halfRole_log_bounds bulk top E indices hE v hv J hJv
  obtain ⟨hd₁,hd₂⟩ := abs_le.mp hD
  apply abs_le.mpr
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) nc]

end Ostmann.Characters.HigherBiasSourceRoleBounds

end

end OAI
