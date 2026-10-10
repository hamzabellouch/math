import OAI.NumberTheory.Ostmann.Arithmetic.CRTLineAverage
import OAI.NumberTheory.Ostmann.Arithmetic.InternalLineProbability

namespace OAI

/-! # Integrating all repeated internal-prime line systems by CRT -/

namespace Ostmann

open scoped BigOperators Classical

private theorem indicator_probability {X : Type*} [Fintype X] (P : X → Prop) :
    (Fintype.card X : ℝ)⁻¹ * (∑ x, if P x then (1 : ℝ) else 0) =
      (Fintype.card {x : X // P x} : ℝ) / Fintype.card X := by
  rw [Fintype.card_subtype]
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact mul_comm _ _

theorem crt_unit_lineSystems_probability {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (J : I → Type*) (a b : ∀ i, J i → ZMod (p i)) (j₀ : ∀ i, J i)
    (hrow : ∀ i, a i (j₀ i) ≠ 0 ∨ b i (j₀ i) ≠ 0) :
    (Fintype.card ((ZMod (∏ i, p i))ˣ × (ZMod (∏ i, p i))ˣ) : ℝ)⁻¹ *
      (∑ z, ∏ i, if ∀ j, a i j * (crtUnitPairEquiv p hc z i).1 +
        b i j * (crtUnitPairEquiv p hc z i).2 = 0 then (1 : ℝ) else 0) =
      ∏ i, if unitLineFeasible (a i) (b i) (j₀ i) then
        (Fintype.card (ZMod (p i))ˣ : ℝ)⁻¹ else 0 := by
  rw [crt_unit_pair_average p hc
    (fun i z => if ∀ j, a i j * z.1 + b i j * z.2 = 0 then (1 : ℝ) else 0)]
  apply Finset.prod_congr rfl
  intro i _
  rw [indicator_probability]
  exact unit_lineSystem_probability (a i) (b i) (j₀ i) (hrow i)

theorem crt_external_lineSystems_probability {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (J : I → Type*) (a b : ∀ i, J i → ZMod (p i)) (j₀ : ∀ i, J i)
    (hrow : ∀ i, a i (j₀ i) ≠ 0 ∨ b i (j₀ i) ≠ 0) :
    (Fintype.card (ZMod (∏ i, p i) × (ZMod (∏ i, p i))ˣ) : ℝ)⁻¹ *
      (∑ z, ∏ i, if ∀ j, a i j * (crtExternalPairEquiv p hc z i).1 +
        b i j * (crtExternalPairEquiv p hc z i).2 = 0 then (1 : ℝ) else 0) =
      ∏ i, if externalLineFeasible (a i) (b i) (j₀ i) then (p i : ℝ)⁻¹ else 0 := by
  rw [crt_external_pair_average p hc
    (fun i z => if ∀ j, a i j * z.1 + b i j * z.2 = 0 then (1 : ℝ) else 0)]
  apply Finset.prod_congr rfl
  intro i _
  rw [indicator_probability]
  exact external_lineSystem_probability (a i) (b i) (j₀ i) (hrow i)

end Ostmann

end OAI
