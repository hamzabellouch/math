import OAI.Analysis.Mahler.WedgeAssociativity
import OAI.Analysis.Mahler.WedgeCalculus

namespace OAI

open scoped BigOperators

namespace Mahler
variable {T J ι κ ν : Type*} [AddCommGroup T] [Module ℝ T] [Fintype J]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ν] [DecidableEq ν]

lemma wedge_reindex (basis : Module.Basis J ℝ T)
    {ι' κ' : Type*} [Fintype ι'] [DecidableEq ι'] [Fintype κ'] [DecidableEq κ']
    (e : ι ≃ ι') (f : κ ≃ κ')
    (a : T [⋀^ι]→ₗ[ℝ] ℂ) (b : T [⋀^κ]→ₗ[ℝ] ℂ) :
    (wedge a b).domDomCongr (Equiv.sumCongr e f) =
      wedge (a.domDomCongr e) (b.domDomCongr f) := by
  rw [alternating_basis_expansion_normalized basis a,
    alternating_basis_expansion_normalized basis b]
  simp only [domDomCongr_sum, AlternatingMap.domDomCongr_smul,
    wedge_sum_left, wedge_sum_right, wedge_smul_left, wedge_smul_right,
    wedge_covectorVolume, Finset.smul_sum, smul_smul, covectorVolume_domDomCongr]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  congr 2
  funext i
  cases i <;> rfl

/-- The swap of two two-slot blocks has positive sign. -/
lemma two_block_swap_sign : Equiv.Perm.sign (Equiv.sumComm (Fin 2) (Fin 2)) = 1 := by
  decide

lemma wedge_two_comm (basis : Module.Basis J ℝ T)
    (a b : T [⋀^Fin 2]→ₗ[ℝ] ℂ) : wedge a b = wedge b a := by
  have h := wedge_swap basis a b
  rw [AlternatingMap.domDomCongr_perm, two_block_swap_sign, one_smul] at h
  exact h

/-- Two degree-two factors commute in their original nested slot order. -/
lemma wedge_two_left_comm (basis : Module.Basis J ℝ T)
    (a b : T [⋀^Fin 2]→ₗ[ℝ] ℂ) (c : T [⋀^ν]→ₗ[ℝ] ℂ) :
    wedge a (wedge b c) = wedge b (wedge a c) := by
  rw [← wedge_assoc basis, ← wedge_assoc basis, wedge_two_comm basis a b]

lemma wedge_add_left (a a' : T [⋀^ι]→ₗ[ℝ] ℂ) (b : T [⋀^κ]→ₗ[ℝ] ℂ) :
    wedge (a+a') b = wedge a b + wedge a' b := by
  simp only [wedge, ← AlternatingMap.domCoprod'_apply, TensorProduct.add_tmul,
    map_add, LinearMap.compAlternatingMap_add]

lemma wedge_add_right (a : T [⋀^ι]→ₗ[ℝ] ℂ) (b b' : T [⋀^κ]→ₗ[ℝ] ℂ) :
    wedge a (b+b') = wedge a b + wedge a b' := by
  simp only [wedge, ← AlternatingMap.domCoprod'_apply, TensorProduct.tmul_add,
    map_add, LinearMap.compAlternatingMap_add]

/-- The k+1 genuine variation placements are equal, with no suppressed signs
or reassociations. This is the multiplicity in homogeneous transgression. -/
theorem wedgePowerVariation_succ (basis : Module.Basis J ℝ T)
    (a da : T [⋀^Fin 2]→ₗ[ℝ] ℂ) (k : ℕ) :
    wedgePowerVariation a da (k+1) =
      ((k+1 : ℕ) : ℂ) • wedge da (wedgePower a k) := by
  induction k with
  | zero =>
    have hz : wedge a (0 : T [⋀^WedgePowerSlots 0]→ₗ[ℝ] ℂ) = 0 := by
      have h := wedge_smul_right 0 a (0 : T [⋀^WedgePowerSlots 0]→ₗ[ℝ] ℂ)
      simpa only [zero_smul] using h
    have hzero : wedgePowerVariation a da (0+1) = wedge da (wedgePower a 0) := by
      change wedge da (wedgePower a 0) + wedge a 0 = wedge da (wedgePower a 0)
      rw [hz, add_zero]
    rw [hzero]
    simp only [Nat.cast_one, zero_add, one_smul]
    rfl
  | succ k ih =>
    have hc : wedge a (wedge da (wedgePower a k)) =
        wedge da (wedge a (wedgePower a k)) :=
      wedge_two_left_comm basis a da (wedgePower a k)
    have hdec : (inferInstance : DecidableEq (Fin 2 ⊕ WedgePowerSlots k)) =
        wedgePowerSlotsDecidableEq (k+1) := Subsingleton.elim _ _
    have hfin : (inferInstance : Fintype (Fin 2 ⊕ WedgePowerSlots k)) =
        wedgePowerSlotsFintype (k+1) := Subsingleton.elim _ _
    let B : T [⋀^WedgePowerSlots (k+1)]→ₗ[ℝ] ℂ := wedge da (wedgePower a k)
    have hc' : wedge a B =
        wedge da (wedgePower a (k+1)) := by
      dsimp only [B, wedgePower]
      rw [← hdec]
      exact hc
    change wedge da (wedgePower a (k+1)) + wedge a (wedgePowerVariation a da (k+1)) =
      ((k+1+1 : ℕ) : ℂ) • wedge da (wedgePower a (k+1))
    calc
      _ = wedge da (wedgePower a (k+1)) +
          ((k+1 : ℕ) : ℂ) • wedge a B := by
        exact congrArg (fun D : T [⋀^Fin 2 ⊕ WedgePowerSlots (k+1)]→ₗ[ℝ] ℂ =>
          wedge da (wedgePower a (k+1)) + D)
          ((congrArg (fun C : T [⋀^WedgePowerSlots (k+1)]→ₗ[ℝ] ℂ => wedge a C) ih).trans
            (wedge_smul_right _ a B))
      _ = wedge da (wedgePower a (k+1)) +
          ((k+1 : ℕ) : ℂ) • wedge da (wedgePower a (k+1)) := by
        exact congrArg (fun B : T [⋀^Fin 2 ⊕ WedgePowerSlots (k+1)]→ₗ[ℝ] ℂ =>
          wedge da (wedgePower a (k+1)) + ((k+1 : ℕ) : ℂ) • B) hc'
      _ = _ := by
        simp only [Nat.cast_add, Nat.cast_one]
        module

end Mahler

end OAI
