import OAI.NumberTheory.Ostmann.Characters.QuartetTotalMoment
import OAI.NumberTheory.Ostmann.Characters.QuartetSymmetry

namespace OAI

/-! # Square-pullback majorants for the two moving leaves in different pairs -/

namespace Ostmann

open scoped BigOperators

noncomputable local instance crossPairFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

theorem quartetParameterMoment_mean_le_fourier {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (ν : MulChar (ZMod p) ℂ) :
    (∑ y : (ZMod p)ˣ, quartetParameterMoment g h left right ν y) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤
        ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) *
          quartetFourierEnergy (pairAutocorrelation g) (pairAutocorrelation h) left right ν := by
  have hparse : (p : ℝ)⁻¹ *
      (∑ y : ZMod p, quartetParameterMoment g h left right ν y) =
        quartetFourierEnergy (pairAutocorrelation g) (pairAutocorrelation h) left right ν :=
    quartetParameterValue_parseval g h left right ν
  have hsum : (∑ y : (ZMod p)ˣ, quartetParameterMoment g h left right ν y) ≤
      ∑ y : ZMod p, quartetParameterMoment g h left right ν y := by
    apply Finset.sum_le_sum_of_injOn (fun y : (ZMod p)ˣ => (y : ZMod p))
      Units.val_injective.injOn (Finset.subset_univ _)
    · intro _ _
      exact le_rfl
    · intro y _ _
      exact quartetParameterMoment_nonneg g h left right ν y
  apply (div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)).trans_eq
  rw [← hparse]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  field_simp

noncomputable def crossPairMajorant {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) : ℝ :=
  squareCharacterMass (fun ν => quartetParameterMoment g h left right ν y) ρ

theorem crossPairMajorant_nonneg {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) :
    0 ≤ crossPairMajorant g h left right ρ y :=
  squareCharacterMass_nonneg _ (fun ν => quartetParameterMoment_nonneg g h left right ν y) ρ

theorem crossPairMajorant_mean_eq {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (ρ : MulChar (ZMod p) ℂ) :
    (∑ y : (ZMod p)ˣ, crossPairMajorant g h left right ρ y) /
      (Fintype.card (ZMod p)ˣ : ℝ) =
        squareCharacterMass (fun ν =>
          (∑ y : (ZMod p)ˣ, quartetParameterMoment g h left right ν y) /
            (Fintype.card (ZMod p)ˣ : ℝ)) ρ := by
  unfold crossPairMajorant squareCharacterMass
  rw [Finset.sum_comm, Finset.sum_div]

theorem crossPairMajorant_mean_le {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsmall : ∀ ν : MulChar (ZMod p) ℂ,
      quartetFourierEnergy (pairAutocorrelation g) (pairAutocorrelation h) left right ν ≤ δ)
    (ρ : MulChar (ZMod p) ℂ) :
    (∑ y : (ZMod p)ˣ, crossPairMajorant g h left right ρ y) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤
        2 * (((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) * δ) := by
  rw [crossPairMajorant_mean_eq]
  apply squareCharacterMass_le_twice _ _ (by positivity)
  intro ν
  exact (quartetParameterMoment_mean_le_fourier g h left right ν).trans
    (mul_le_mul_of_nonneg_left (hsmall ν) (by positivity))

theorem crossPairMajorant_total_mean_le {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (hg : g 0 = 0) (hh : h 0 = 0)
    (heg : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (heh : (∑ x : ZMod p, ‖h x‖ ^ 2) ≤ (p : ℝ)) (left right : Bool) :
    (∑ ρ : MulChar (ZMod p) ℂ, (∑ y : (ZMod p)ˣ,
      crossPairMajorant g h left right ρ y) / (Fintype.card (ZMod p)ˣ : ℝ)) ≤
        ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 := by
  simp_rw [crossPairMajorant_mean_eq]
  rw [sum_squareCharacterMass]
  exact quartetParameterMoment_total_mean_le g h hg hh heg heh left right

end Ostmann

end OAI
