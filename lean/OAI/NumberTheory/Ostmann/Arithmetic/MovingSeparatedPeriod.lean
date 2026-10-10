import OAI.NumberTheory.Ostmann.Arithmetic.MovingSeparatedCoefficient

namespace OAI

/-! # Periodicity after the arithmetic factors have been separated -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPrimeLineSupport_modEq {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (x y a b M : ℤ)
    (hprime : ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, (value i : ℤ) ∣ M)
    (hx : x ≡ a [ZMOD M]) (hy : y ≡ b [ZMOD M]) :
    movingPrimeLineSupport value T x y ↔ movingPrimeLineSupport value T a b := by
  apply forall₂_congr
  intro o ho
  apply forall₂_congr
  intro i hi
  have hL : (x : ZMod (value i)) = (a : ZMod (value i)) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr (hx.of_dvd (by exact_mod_cast hprime o ho i hi))
  have hR : (y : ZMod (value i)) = (b : ZMod (value i)) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr (hy.of_dvd (by exact_mod_cast hprime o ho i hi))
  dsimp only
  rw [hL, hR]

theorem movingSeparatedSupport_modEq {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n) (nodes : List MovingFormulaNode)
    (R : ℤ) (hf : T.Frequencies (· ≠ 0)) (hR : T.frequencyProduct ∣ R)
    (x y a b M : ℤ) (hfrequency : R ^ (n + 1) ∣ M)
    (hsquare : ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ M)
    (hx : x ≡ a [ZMOD M]) (hy : y ≡ b [ZMOD M]) :
    movingSeparatedSupport value outside T nodes R x y ↔
      movingSeparatedSupport value outside T nodes R a b := by
  have hp : ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, (value i : ℤ) ∣ M := by
    intro o ho i hi
    exact (dvd_pow_self (value i : ℤ) (by decide : 2 ≠ 0)).trans (hsquare o ho i hi)
  unfold movingSeparatedSupport
  rw [movingSquareLineSupport_modEq value T x y a b M hsquare hx hy,
    movingFrequencyGate_modEq value R T hf hR x y a b (hx.of_dvd hfrequency) (hy.of_dvd hfrequency),
    movingPrimeLineSupport_modEq value T x y a b M hp hx hy]

theorem movingSeparatedResidueCoefficient_modEq {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : MovingSlotData σ n) (nodes : List MovingFormulaNode)
    (R : ℤ) (hf : T.Frequencies (· ≠ 0)) (hR : T.frequencyProduct ∣ R)
    (x y a b M : ℤ) (hfrequency : R ^ (n + 1) ∣ M)
    (hsquare : ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ M)
    (hspectator : ∀ i ∈ S, (q i : ℤ) ∣ M)
    (hx : x ≡ a [ZMOD M]) (hy : y ≡ b [ZMOD M]) :
    movingSeparatedResidueCoefficient q value outside F E g D S T nodes R x y =
      movingSeparatedResidueCoefficient q value outside F E g D S T nodes R a b := by
  have hs := movingSeparatedSupport_modEq value outside T nodes R hf hR x y a b M hfrequency hsquare hx hy
  have hprod : (∏ i ∈ S, movingModularSpectator value (q i) (g i) (D i) T x y) =
      ∏ i ∈ S, movingModularSpectator value (q i) (g i) (D i) T a b := by
    apply Finset.prod_congr rfl
    intro i hi
    have hL : (x : ZMod (q i)) = (a : ZMod (q i)) :=
      (ZMod.intCast_eq_intCast_iff _ _ _).mpr (hx.of_dvd (by exact_mod_cast hspectator i hi))
    have hR : (y : ZMod (q i)) = (b : ZMod (q i)) :=
      (ZMod.intCast_eq_intCast_iff _ _ _).mpr (hy.of_dvd (by exact_mod_cast hspectator i hi))
    rw [hL, hR]
  simp only [movingSeparatedResidueCoefficient, hs, hprod]

end Ostmann

end OAI
