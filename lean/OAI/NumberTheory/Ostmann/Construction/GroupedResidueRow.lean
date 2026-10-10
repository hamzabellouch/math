import OAI.NumberTheory.Ostmann.Construction.GroupedPivotPhase
import OAI.NumberTheory.Ostmann.Characters.PivotKeyReduction

namespace OAI

/-! # The entire outgoing pivot phase factors through the composite residue key -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def groupedResidueRow {K : Type*} [Fintype K] (P : K → ℕ)
    [∀ k, NeZero (P k)] (χ : ∀ k, DirichletCharacter ℂ (P k))
    (κ : K → ℂ) (t : ∀ k, ZMod (P k)) (Y : ℕ) (ε : K → ℤ)
    (u : Fin (∏ k, P k)) : ℂ :=
  pivotTupleRow P χ κ t (fun k => (tupleCofactor P k : ZMod (P k)))
    (fun k => (Y : ZMod (P k))) (fun k => (u.val : ZMod (P k))) ε

theorem groupedResidueRow_norm_le_one {K : Type*} [Fintype K] (P : K → ℕ)
    [∀ k, NeZero (P k)] (χ : ∀ k, DirichletCharacter ℂ (P k))
    (κ : K → ℂ) (hκ : ∀ k, ‖κ k‖ ≤ 1) (t : ∀ k, ZMod (P k))
    (Y : ℕ) (ε : K → ℤ) (u : Fin (∏ k, P k)) :
    ‖groupedResidueRow P χ κ t Y ε u‖ ≤ 1 :=
  pivotTupleRow_norm_le_one P χ κ hκ t _ _ _ ε

/-- A local outgoing factor is exactly the bounded residue row. The hypotheses
are the literal cofactor and unit conditions of the supported prime tuple. -/
theorem grouped_outgoing_local {p : ℕ} [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (κ : ℂ) (t : ZMod p)
    (D H Y M : ℕ) (hM : 0 < M) (v ε : ℤ)
    (hpM : p ∣ M) (hHM : H.Coprime M)
    (hD : (D : ZMod p) ≠ 0) (hY : (Y : ZMod p) ≠ 0)
    (hv : (v : ZMod p) ≠ 0) :
    ZMod.stdAddChar (t * (((D * H * Y : ℕ) : ZMod p)⁻¹ * (v : ZMod p))) *
      (κ * χ (v : ZMod p) ^ (-ε)) * χ ((D * H * Y : ℕ) : ZMod p) ^ ε =
    pivotLocalRow χ κ t (D : ZMod p) (Y : ZMod p)
      ((positiveIntegerPivotKey M hM H v).val : ZMod p) ε := by
  let u : ZMod p := (positiveIntegerPivotKey M hM H v).val
  have hrel : (v : ZMod p) = u * (H : ZMod p) :=
    (positiveIntegerPivotKey_mul_at_divisor M hM H v hpM hHM).symm
  have hH : (H : ZMod p) ≠ 0 := by
    have hc := hHM.of_dvd_right hpM
    exact isUnit_iff_ne_zero.mp ((ZMod.isUnit_iff_coprime H p).mpr hc)
  have hu : u ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hrel
    exact hv hrel
  have hh := pivotLocalRow_eq χ κ t (D : ZMod p) (Y : ZMod p) (H : ZMod p)
    (v : ZMod p) u ε hD hY hH hu hrel
  have hC : ((D * H * Y : ℕ) : ZMod p) = (D : ZMod p) * (Y : ZMod p) * (H : ZMod p) := by
    push_cast
    ring
  rw [hC]
  have hA : ((D : ZMod p) * (Y : ZMod p) * (H : ZMod p))⁻¹ * v =
      (v : ZMod p) / ((D : ZMod p) * (Y : ZMod p) * (H : ZMod p)) := by
    rw [div_eq_mul_inv, mul_comm]
  rw [hA]
  calc
    _ = ZMod.stdAddChar (t * ((v : ZMod p) / ((D : ZMod p) * (Y : ZMod p) * (H : ZMod p)))) * κ *
        (χ (v : ZMod p) ^ (-ε) * χ ((D : ZMod p) * (Y : ZMod p) * (H : ZMod p)) ^ ε) := by ring
    _ = _ := hh

end Ostmann

end OAI
