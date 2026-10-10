import OAI.NumberTheory.Ostmann.Construction.AdaptivePivotCoefficients
import OAI.NumberTheory.Ostmann.Arithmetic.CompensatedPivotPrecision

namespace OAI

/-! # Adaptive coefficients with the actual compensation-divided pivots -/

namespace Ostmann

open scoped Classical

def SampledPivotHistory.compensatedValid {n Q : ℕ} (a : SampledPivotHistory n Q)
    (D : PivotDependencyScheme (2 ^ n - 1)) (U : Fin (2 ^ n - 1) → ℤ) : Prop :=
  D.compensatedEquations U a.leftProduct a.rightProduct a.pivots ∧
    ∀ j, IsCoprime (D.leftCoefficient a.pivots j) (D.frequencies j).root ∧
      IsCoprime (D.rightCoefficient a.pivots j) (D.frequencies j).root

/-- Choose any valid completion of the exposed prefix. The precision theorem
below proves that the required reduced coefficients do not depend on it. -/
noncomputable def compensatedAdaptiveCoefficients (n Q : ℕ)
    (D : PivotDependencyScheme (2 ^ n - 1)) (U : Fin (2 ^ n - 1) → ℤ)
    (total : (ZMod Q)ˣ) (past : List (ZMod Q)ˣ) : ZMod Q × ZMod Q :=
  if hj : past.length < 2 ^ n - 1 then
    if h : ∃ a : SampledPivotHistory n Q, a.compensatedValid D U ∧ a.matches total past then
      let a := Classical.choose h
      (D.leftCoefficient a.pivots ⟨past.length, hj⟩,
        D.rightCoefficient a.pivots ⟨past.length, hj⟩)
    else (0, 0)
  else (0, 0)

theorem compensatedAdaptiveCoefficients_witness (n Q : ℕ)
    (D : PivotDependencyScheme (2 ^ n - 1)) (U : Fin (2 ^ n - 1) → ℤ)
    (total : (ZMod Q)ˣ) (past : List (ZMod Q)ˣ)
    (hj : past.length < 2 ^ n - 1)
    (hex : ∃ a : SampledPivotHistory n Q, a.compensatedValid D U ∧ a.matches total past) :
    ∃ a : SampledPivotHistory n Q, a.compensatedValid D U ∧ a.matches total past ∧
      compensatedAdaptiveCoefficients n Q D U total past =
        ((D.leftCoefficient a.pivots ⟨past.length, hj⟩ : ZMod Q),
          (D.rightCoefficient a.pivots ⟨past.length, hj⟩ : ZMod Q)) := by
  refine ⟨Classical.choose hex, (Classical.choose_spec hex).1, (Classical.choose_spec hex).2, ?_⟩
  simp only [compensatedAdaptiveCoefficients, dite_eq_left hj, dite_eq_left hex]

/-- The chosen completion gives the actual coefficients modulo the current
root frequency, even though its integer pivots may differ. -/
theorem compensatedAdaptiveCoefficients_reduce (n R k : ℕ)
    (D : PivotDependencyScheme (2 ^ n - 1)) (U : Fin (2 ^ n - 1) → ℤ)
    (hU : ∀ i, IsCoprime (U i) (R : ℤ))
    (hdepth : ∀ i, D.depth i ≤ k) (hs : ∀ i, (D.frequencies i).root ≠ 0)
    (hsR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (a : SampledPivotHistory n (R ^ (k + 2))) (ha : a.compensatedValid D U)
    (total : (ZMod (R ^ (k + 2)))ˣ) (past : List (ZMod (R ^ (k + 2)))ˣ)
    (hm : a.matches total past) (hj : past.length < 2 ^ n - 1) :
    let j : Fin (2 ^ n - 1) := ⟨past.length, hj⟩
    let hd : (D.frequencies j).root.natAbs ∣ R ^ (k + 2) :=
      (hsR j).trans (dvd_pow_self R (by omega))
    ZMod.castHom hd (ZMod (D.frequencies j).root.natAbs)
        (compensatedAdaptiveCoefficients n (R ^ (k + 2)) D U total past).1 =
        D.leftCoefficient a.pivots j ∧
      ZMod.castHom hd (ZMod (D.frequencies j).root.natAbs)
        (compensatedAdaptiveCoefficients n (R ^ (k + 2)) D U total past).2 =
        D.rightCoefficient a.pivots j := by
  dsimp only
  obtain ⟨b, hb, hbm, hcoeff⟩ := compensatedAdaptiveCoefficients_witness n (R ^ (k + 2)) D U total past hj
    ⟨a, ha, hm⟩
  have hprod (i : Fin (2 ^ n - 1)) (hi : i.val < past.length) :=
    b.prefix_products a total past hbm hm (Nat.le_of_lt hj) i hi
  have hL (i : Fin (2 ^ n - 1)) (hi : i.val < past.length) :
      b.leftProduct i ≡ a.leftProduct i [ZMOD (R : ℤ) ^ (k + 2)] := by
    have h := (ZMod.intCast_eq_intCast_iff _ _ _).mp (hprod i hi).1
    simpa only [Nat.cast_pow] using h
  have hR (i : Fin (2 ^ n - 1)) (hi : i.val < past.length) :
      b.rightProduct i ≡ a.rightProduct i [ZMOD (R : ℤ) ^ (k + 2)] := by
    have h := (ZMod.intCast_eq_intCast_iff _ _ _).mp (hprod i hi).2
    simpa only [Nat.cast_pow] using h
  have h := D.compensated_coefficients_prefix_precision R k U hU ⟨past.length, hj⟩ hdepth hs hsR
    b.leftProduct b.rightProduct b.pivots a.leftProduct a.rightProduct a.pivots hb.1 ha.1 hL hR
  rw [hcoeff]
  simp only [map_intCast]
  exact ⟨(ZMod.intCast_eq_intCast_iff _ _ _).mpr h.1,
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr h.2⟩

end Ostmann

end OAI
