import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceHalfMean

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open Construction Preliminaries HigherBiasSourceWord HigherBiasSourceRoleBounds
open scoped BigOperators

lemma characterTuplePrior_mass_pos_of_membership {Q b : ℕ}
    (E : Fin b → Finset (PrimeUpTo Q)) (hE : ∀ i,0 < primeShellMass (E i))
    (w : Fin b → PrimeUpTo Q) (hw : ∀ i,w i∈E i) :
    0 < (characterTuplePrior E hE).mass w := by
  classical
  change 0 < ∏ i,(primeShellPrior (E i) (hE i)).mass (w i)
  apply Finset.prod_pos
  intro i hi
  rw [primeShellPrior_mass,ite_eq_left (hw i)]
  have hp : (0:ℝ)<(w i).val := by exact_mod_cast (primeUpTo_prime (w i)).pos
  exact div_pos (inv_pos.mpr hp) (hE i)

lemma characterTupleProduct_split {Q b : ℕ} (w : Fin (b+b) → PrimeUpTo Q) :
    characterTupleProduct w = characterTupleProduct (characterTupleSplit b w).1 *
      characterTupleProduct (characterTupleSplit b w).2 := by
  unfold characterTupleProduct
  rw [Fin.prod_univ_add]
  rfl

theorem source_doubled_product_window {Q m k : ℕ}
    (bulk top E : Finset (PrimeUpTo Q)) (cfg : SourceConfiguration k)
    (hE : ∀ i,0 < primeShellMass (halfRoleShells bulk top m
      (fun j=>boundedRawLogCell E (configCellIndices cfg j)) i))
    (J : ℤ) (T : Fin (k+1)→ℝ) {c X Δ₀ : ℝ} (hX : 0 < X)
    (hlist : ∀ j,|((cfg.2 j).sum:ℝ)-T j| ≤ 6/c)
    (htarget : 2*((J:ℝ)+(∑ i,(cfg.1 i:ℝ))+(∑ j,T j))=Real.log X+Δ₀)
    (hlength : ∀ j,((cfg.2 j).length:ℝ) ≤ 2*Real.exp (2*(k:ℝ)/10000))
    (w : Fin (((m+1)+configCellCount cfg)+((m+1)+configCellCount cfg))→PrimeUpTo Q)
    (hw : ∀ i,w i∈characterDoubleShell (halfRoleShells bulk top m
      (fun j=>boundedRawLogCell E (configCellIndices cfg j))) i)
    (hmask : characterDoubleMask (sourceHalfMask J) w≠0) :
    X*Real.exp (Δ₀-configurationProductWidth k c) ≤ (characterTupleProduct w:ℝ) ∧
      (characterTupleProduct w:ℝ) ≤ X*Real.exp (Δ₀+configurationProductWidth k c) := by
  let b := (m+1)+configCellCount cfg
  let E0 := halfRoleShells bulk top m (fun j=>boundedRawLogCell E (configCellIndices cfg j))
  let v := (characterTupleSplit b w).1
  let t := (characterTupleSplit b w).2
  have hv : ∀ i,v i∈E0 i := by
    intro i
    simpa only [b,v,E0,characterTupleSplit,Equiv.coe_fn_mk,characterDoubleShell,Fin.append_left] using hw (Fin.castAdd b i)
  have ht : ∀ i,t i∈E0 i := by
    intro i
    simpa only [b,t,E0,characterTupleSplit,Equiv.coe_fn_mk,characterDoubleShell,Fin.append_right] using hw (Fin.natAdd b i)
  have hvp := (characterTuplePrior_mass_pos_of_membership E0 hE v hv).ne'
  have htp := (characterTuplePrior_mass_pos_of_membership E0 hE t ht).ne'
  have hmv : binIndicator J (originalWord v)≠0 :=
    (mul_ne_zero_iff.mp hmask).1
  have hmt : binIndicator J (originalWord t)≠0 :=
    (mul_ne_zero_iff.mp hmask).2
  have hh := configuration_paired_product_endpoints bulk top cfg (fun _=>E) hE v t
    hvp htp J hmv hmt T hlist htarget hlength
  have he : characterTupleProduct w=characterTupleProduct v*characterTupleProduct t := characterTupleProduct_split w
  rw [← he] at hh
  have hp : (0:ℝ)<characterTupleProduct w := by exact_mod_cast characterTupleProduct_pos w
  constructor
  · have hl := Real.exp_le_exp.mpr hh.1
    rw [Real.exp_log hp] at hl
    simpa only [show Real.log X+Δ₀-configurationProductWidth k c =
      Real.log X+(Δ₀-configurationProductWidth k c) by ring,
      Real.exp_add,Real.exp_log hX] using hl
  · have hu := Real.exp_le_exp.mpr hh.2
    rw [Real.exp_log hp] at hu
    simpa only [add_assoc,Real.exp_add,Real.exp_log hX] using hu

end Ostmann.Characters.HigherBiasSource

end

end OAI
