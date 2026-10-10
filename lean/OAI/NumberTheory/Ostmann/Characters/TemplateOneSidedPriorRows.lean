import OAI.NumberTheory.Ostmann.Characters.OneSidedScaleGapMajorant
import OAI.NumberTheory.Ostmann.Characters.PrimeDyadicCoverSource

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedPrior
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def rowValue (Q N : ℕ) (x : Fin Q × Fin N) : ℕ := Q*x.2.val+x.1.val

@[simp] theorem rowValue_mod {Q N : ℕ} (x : Fin Q × Fin N) :
    rowValue Q N x % Q=x.1.val := by
  simp [rowValue,Nat.add_mod,Nat.mod_eq_of_lt x.1.isLt]

@[simp] theorem rowValue_div {Q N : ℕ} (hQ : 0<Q) (x : Fin Q × Fin N) :
    rowValue Q N x / Q=x.2.val := by
  simp only [rowValue,Nat.mul_add_div hQ,Nat.div_eq_of_lt x.1.isLt,Nat.add_zero]

theorem rowValue_injective {Q N : ℕ} (hQ : 0<Q) :
    Function.Injective (rowValue Q N) := by
  intro x y h
  apply Prod.ext
  · apply Fin.ext
    simpa only [rowValue_mod] using congrArg (fun n=>n%Q) h
  · apply Fin.ext
    simpa only [rowValue_div hQ] using congrArg (fun n=>n/Q) h

theorem sum_rows_eq {A : Type*} [AddCommMonoid A] (Q b : ℕ) (hQ : 0<Q)
    (S : Finset ℕ) (hS : ∀p∈S,p≤2*b) (f : ℕ→A) :
    (∑ x : Fin Q × Fin (2*b+1),if rowValue Q (2*b+1) x∈S then
      f (rowValue Q (2*b+1) x) else 0)=∑p∈S,f p := by
  rw [←Finset.sum_filter]
  apply Finset.sum_bij (fun x _=>rowValue Q (2*b+1) x)
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x hx y hy hxy
    exact rowValue_injective hQ hxy
  · intro p hp
    have hpbound := hS p hp
    let x : Fin Q × Fin (2*b+1) :=
      (⟨p%Q,Nat.mod_lt _ hQ⟩,⟨p/Q,lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩)
    have hx : rowValue Q (2*b+1) x=p := by
      exact Nat.div_add_mod p Q
    exact ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx ▸ hp⟩,hx⟩
  · intro x hx
    rfl

def rowMass (Q b : ℕ) (S : Finset ℕ) (Z : ℝ) (x : Fin Q × Fin (2*b+1)) : ℝ :=
  if rowValue Q (2*b+1) x∈S then (rowValue Q (2*b+1) x:ℝ)⁻¹/Z else 0

theorem rowMass_nonneg (Q b : ℕ) (S : Finset ℕ) {Z : ℝ} (hZ : 0<Z)
    (x : Fin Q × Fin (2*b+1)) : 0≤rowMass Q b S Z x := by
  unfold rowMass
  split_ifs <;> positivity

theorem sum_rowMass (Q b : ℕ) (hQ : 0<Q) (S : Finset ℕ)
    (hS : ∀p∈S,p≤2*b) (Z : ℝ) :
    (∑x,rowMass Q b S Z x)=∑p∈S,(p:ℝ)⁻¹/Z := by
  exact sum_rows_eq Q b hQ S hS (fun p=>(p:ℝ)⁻¹/Z)

theorem rowMass_majorant (Q b : ℕ) (S : Finset ℕ) {Z : ℝ} (hZ : 0<Z)
    (hb : 0<b) (hS : ∀p∈S,b≤p ∧ p≤2*b) (x : Fin Q × Fin (2*b+1)) :
    rowMass Q b S Z x ≤ longProgressionMajorant (1/Z) b Q x.1.val x.2.val := by
  unfold rowMass
  split_ifs with hx
  · have hh := hS _ hx
    have hhR : (b:ℝ)≤(rowValue Q (2*b+1) x:ℝ) ∧
        (rowValue Q (2*b+1) x:ℝ)≤2*(b:ℝ) := by exact_mod_cast hh
    change _ ≤ if (b:ℝ)≤(rowValue Q (2*b+1) x:ℝ) ∧
      (rowValue Q (2*b+1) x:ℝ)≤2*(b:ℝ) then _ else _
    rw [ite_eq_left hhR]
    exact le_of_eq (by dsimp only [rowValue]; field_simp)
  · exact longProgressionMajorant_nonneg (by positivity) (by exact_mod_cast hb) _ _ _

theorem rowLength_le {b : ℕ} (hb : 0<b) : ((2*b+1:ℕ):ℝ)≤3*(b:ℝ) := by
  have hh : 1≤b := hb
  exact_mod_cast (show 2*b+1≤3*b by omega)

end Ostmann.Characters.TemplateOneSidedPrior

end

end OAI
