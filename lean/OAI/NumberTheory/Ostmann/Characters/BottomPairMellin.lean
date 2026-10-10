import OAI.NumberTheory.Ostmann.Characters.MellinParseval
import OAI.NumberTheory.Ostmann.Preliminaries.Autocorrelation
import OAI.NumberTheory.Ostmann.Tree.BottomPairCoordinates

namespace OAI

/-!
# The bottom-pair Mellin coefficient is an autocorrelation

This is equation `tree-P-definition`. The difference parameter is a unit;
the exceptional ratio `t = 1` is assigned value zero. The function being
correlated is twisted by the conjugate multiplicative character.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

private theorem sum_units_of_zero {p : ℕ} [Fact p.Prime]
    (F : ZMod p → ℂ) (hF : F 0 = 0) :
    (∑ u : (ZMod p)ˣ, F u) = ∑ x : ZMod p, F x := by
  classical
  have hsum := Fintype.sum_subtype_add_sum_subtype (fun x : ZMod p => x ≠ 0) F
  have hz : (∑ x : {x : ZMod p // ¬x ≠ 0}, F x) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    have hx : x.val = 0 := not_ne_iff.mp x.property
    simpa only [hx] using hF
  rw [hz, add_zero] at hsum
  calc
    (∑ u : (ZMod p)ˣ, F u) = ∑ x : {x : ZMod p // x ≠ 0}, F x :=
      (unitsEquivNeZero (G₀ := ZMod p)).bijective.sum_comp (fun x => F x.val)
    _ = _ := hsum

/-- The fractional-linear involution exchanges the two exceptional points
with themselves, making it a permutation of the entire finite field. -/
noncomputable def ratioInvolution {p : ℕ} [Fact p.Prime] (t : ZMod p) : ZMod p :=
  if t = 1 then 1 else t / (t - 1)

theorem ratioInvolution_involutive {p : ℕ} [Fact p.Prime] :
    Function.Involutive (ratioInvolution (p := p)) := by
  intro t
  by_cases ht : t = 1
  · simp [ratioInvolution, ht]
  · have hden : t - 1 ≠ 0 := sub_ne_zero.mpr ht
    have hquot : t / (t - 1) ≠ 1 := by
      intro h
      have heq := (div_eq_one_iff_eq hden).mp h
      have : (1 : ZMod p) = 0 := by linear_combination heq
      exact one_ne_zero this
    simp only [ratioInvolution, ht, ite_false, hquot]
    field_simp
    ring

/-- Bottom-pair value with difference `d` and ratio `t`, zero at the singular ratio. -/
noncomputable def bottomPairValue {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d t : (ZMod p)ˣ) : ℂ :=
  if t = 1 then 0 else
    g ((d : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1)) *
      conj (g ((d : ZMod p) / ((t : ZMod p) - 1)))

/-- The multiplicative twist appearing in the autocorrelation formula. -/
noncomputable def characterTwist {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (x : ZMod p) : ℂ :=
  g x * conj (χ x)

private theorem twisted_pair_identity {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ)
    (d : (ZMod p)ˣ) (t : ZMod p) (ht : t ≠ 1) :
    characterTwist g χ ((d : ZMod p) * t / (t - 1)) *
        conj (characterTwist g χ ((d : ZMod p) * t / (t - 1) - d)) =
      g ((d : ZMod p) * t / (t - 1)) * conj (g ((d : ZMod p) / (t - 1))) *
        conj (χ t) := by
  let x : ZMod p := (d : ZMod p) * t / (t - 1)
  let z : ZMod p := (d : ZMod p) / (t - 1)
  have hz : z ≠ 0 := div_ne_zero (Units.ne_zero d) (sub_ne_zero.mpr ht)
  have hdiff : x - d = z := by
    dsimp [x, z]
    have hh := pair_coordinate_difference (d : ZMod p) t ht
    linear_combination hh
  have hx : x = t * z := by dsimp [x, z]; ring
  have hchar : χ x = χ t * χ z := by rw [hx, map_mul]
  have hnorm : ‖χ z‖ = 1 := norm_mulChar_unit χ (Units.mk0 z hz)
  change (g x * conj (χ x)) * conj (g (x - d) * conj (χ (x - d))) =
    g x * conj (g z) * conj (χ t)
  rw [hdiff]
  calc
    _ = (g x * conj (g z) * conj (χ t)) * (conj (χ z) * χ z) := by
      rw [hchar]
      simp only [map_mul, starRingEnd_apply, star_star]
      ring
    _ = _ := by rw [Complex.conj_mul', hnorm]; norm_num

/-- Reindex the unnormalized bottom-pair Mellin sum as a full-field correlation. -/
theorem bottomPair_mellin_sum {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d : (ZMod p)ˣ) (χ : MulChar (ZMod p) ℂ) :
    (∑ t : (ZMod p)ˣ, bottomPairValue g d t * conj (χ t)) =
      ∑ x : ZMod p, characterTwist g χ x * conj (characterTwist g χ (x - d)) := by
  classical
  let H : ZMod p → ℂ := fun t => if t = 1 then 0 else
    g ((d : ZMod p) * t / (t - 1)) *
      conj (g ((d : ZMod p) / (t - 1))) * conj (χ t)
  have hH0 : H 0 = 0 := by simp [H, MulChar.map_zero]
  have hunit : ∀ t : (ZMod p)ˣ, bottomPairValue g d t * conj (χ t) = H t := by
    intro t
    by_cases ht : t = 1
    · subst t
      simp [bottomPairValue, H]
    · have htval : (t : ZMod p) ≠ 1 := fun h => ht (Units.ext h)
      simp only [bottomPairValue, ht, ite_false, H, htval]
  let e : ZMod p ≃ ZMod p :=
    (Function.Involutive.toPerm _ ratioInvolution_involutive).trans
      (Equiv.mulLeft₀ (d : ZMod p) (Units.ne_zero d))
  have he : ∀ t : ZMod p, H t =
      characterTwist g χ (e t) * conj (characterTwist g χ (e t - d)) := by
    intro t
    change H t = characterTwist g χ ((d : ZMod p) * ratioInvolution t) *
      conj (characterTwist g χ ((d : ZMod p) * ratioInvolution t - d))
    by_cases ht : t = 1
    · subst t
      simp [H, ratioInvolution, characterTwist, MulChar.map_zero]
    · simpa only [H, ht, ite_false, ratioInvolution, ← mul_div_assoc] using
        (twisted_pair_identity g χ d t ht).symm
  simp_rw [hunit]
  rw [sum_units_of_zero H hH0]
  simp_rw [he]
  exact e.bijective.sum_comp (fun x => characterTwist g χ x * conj (characterTwist g χ (x - d)))

/-- Equation `tree-P-definition`, with the paper's two probability normalizations. -/
theorem bottomPair_mellin_autocorrelation {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d : (ZMod p)ˣ) (χ : MulChar (ZMod p) ℂ) :
    mellinCoefficient (bottomPairValue g d) χ =
      (p : ℂ) / (Fintype.card (ZMod p)ˣ : ℂ) *
        additiveAutocorrelation (characterTwist g χ) (d : ZMod p) := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hu : (Fintype.card (ZMod p)ˣ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [mellinCoefficient, bottomPair_mellin_sum, additiveAutocorrelation]
  field_simp

end Ostmann

end OAI
