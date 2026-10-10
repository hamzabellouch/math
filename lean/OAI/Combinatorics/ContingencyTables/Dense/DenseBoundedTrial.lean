import OAI.Combinatorics.ContingencyTables.Dense.DenseRationalKernel
import OAI.Combinatorics.ContingencyTables.Transport.BoundedOffsetLaw
import OAI.Combinatorics.ContingencyTables.Transport.RationalReindex

namespace OAI

/-! # The finite dense trial with bounded independent offset draws -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical
open ResidualMixture FirstSuccess FairBits

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def offsetCoordinateEquiv (e : I × J ≃ Fin q) (w : I × J → ℕ) :
    (∀ j : Fin q, Fin (w (e.symm j))) ≃ Offset w :=
  (Equiv.piCongrLeft' (fun p => Fin (w p)) e).symm

def boundedOffsetLaw (e : I × J ≃ Fin q) (w : I × J → ℕ)
    (hw : ∀ p, 0 < w p) (h d : ℕ) : RationalLaw (Offset w) :=
  equivLaw (offsetCoordinateEquiv e w)
    (piLaw (fun j => scaledLaw (w (e.symm j)) (offsetBitLength (w (e.symm j)) h d) (hw _)))

def uniformOffsetLaw (e : I × J ≃ Fin q) (w : I × J → ℕ)
    (hw : ∀ p, 0 < w p) : RationalLaw (Offset w) :=
  equivLaw (offsetCoordinateEquiv e w) (piLaw (fun j => uniformIntLaw (w (e.symm j)) (hw _)))

theorem uniformOffsetLaw_mass (e : I × J ≃ Fin q) (w : I × J → ℕ)
    (hw : ∀ p, 0 < w p) (o : Offset w) :
    (uniformOffsetLaw e w hw).mass o = 1 / Fintype.card (Offset w) := by
  have hc := Fintype.card_congr (offsetCoordinateEquiv e w)
  simp only [Fintype.card_pi, Fintype.card_fin] at hc
  change (∏ j : Fin q, (1 : ℚ) / w (e.symm j)) = _
  rw [Finset.prod_div_distrib, Finset.prod_const_one, ← Nat.cast_prod, hc]
  simp [Offset]

theorem boundedOffsetLaw_variation (e : I × J ≃ Fin q) (w : I × J → ℕ)
    (hw : ∀ p, 0 < w p) (h d : ℕ) (hq : q ≤ d) :
    variation (boundedOffsetLaw e w hw h d) (uniformOffsetLaw e w hw) ≤
      (d : ℚ) / (2 : ℚ) ^ (4 * (h + d)) := by
  rw [boundedOffsetLaw, uniformOffsetLaw, variation_equiv]
  exact dense_offset_product_variation q h d (fun j => w (e.symm j)) (fun j => hw _) hq

def boundedTrialLaw (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q) (h : ℕ)
    (a : Grid (I := Fin q) (4 * d ^ 8)) : RationalLaw (DenseTrial R P d q) :=
  productLaw (rationalWalkLaw R P d hd hfree e (d ^ 50 * (h + 1) ^ 2) a)
    (boundedOffsetLaw e (integerWidth R P d) (integerWidth_pos R P d hd hR hP) h d)

theorem stationaryTrialLaw_eq (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) :
    productLaw (rationalStationaryLaw R P d hd e)
      (uniformOffsetLaw e (integerWidth R P d) (integerWidth_pos R P d hd hR hP)) =
        rationalTrialLaw R P d hd hR hP e := by
  apply RationalLaw.ext
  funext t
  change (rationalStationaryLaw R P d hd e).mass t.1 *
    (uniformOffsetLaw e (integerWidth R P d) (integerWidth_pos R P d hd hR hP)).mass t.2 = _
  rw [uniformOffsetLaw_mass]
  change (rationalBinWeight R P d e t.1 / ∑ b, rationalBinWeight R P d e b) *
    (1 / Fintype.card (Offset (integerWidth R P d))) = rationalTrialMass R P d e t
  unfold rationalTrialMass
  ring

theorem inverse_two_pow_cast (n : ℕ) :
    ((1 / (2 : ℚ) ^ n : ℚ) : ℝ) = (2 : ℝ) ^ (-(n : ℝ)) := by
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat]
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  exact one_div _

/-- A complete finite dense trial has bin-mixing error plus the bounded
offset error, with the manuscript's actual walk and offset schedules. -/
theorem boundedTrialLaw_variation (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin q) (4 * d ^ 8)))
    (h : ℕ) (a : Grid (I := Fin q) (4 * d ^ 8)) :
    (variation (boundedTrialLaw R P d hd hR hP hfree e h a)
      (rationalTrialLaw R P d hd hR hP e) : ℝ) ≤
        (1 + (d : ℝ)) * (2 : ℝ) ^ (-(4 * ((h : ℝ) + d))) := by
  have hq : q ≤ d := by
    have hc := Fintype.card_congr e
    rw [Fintype.card_fin] at hc
    omega
  have ho := boundedOffsetLaw_variation e (integerWidth R P d)
    (integerWidth_pos R P d hd hR hP) h d hq
  have hoc : (variation (boundedOffsetLaw e (integerWidth R P d)
      (integerWidth_pos R P d hd hR hP) h d)
      (uniformOffsetLaw e (integerWidth R P d) (integerWidth_pos R P d hd hR hP)) : ℝ) ≤
        ((d : ℚ) / (2 : ℚ) ^ (4 * (h + d)) : ℚ) := by exact_mod_cast ho
  have he : (((d : ℚ) / (2 : ℚ) ^ (4 * (h + d)) : ℚ) : ℝ) =
      (d : ℝ) * (2 : ℝ) ^ (-(4 * ((h : ℝ) + d))) := by
    rw [div_eq_mul_one_div, Rat.cast_mul, Rat.cast_natCast, inverse_two_pow_cast]
    congr 2
    push_cast
    ring
  rw [he] at hoc
  rw [← stationaryTrialLaw_eq R P d hd hR hP e]
  unfold boundedTrialLaw
  have hv := variation_product (rationalWalkLaw R P d hd hfree e (d ^ 50 * (h + 1) ^ 2) a)
    (rationalStationaryLaw R P d hd e)
    (boundedOffsetLaw e (integerWidth R P d) (integerWidth_pos R P d hd hR hP) h d)
    (uniformOffsetLaw e (integerWidth R P d) (integerWidth_pos R P d hd hR hP))
  have hvc : (variation
      (productLaw (rationalWalkLaw R P d hd hfree e (d ^ 50 * (h + 1) ^ 2) a)
        (boundedOffsetLaw e (integerWidth R P d) (integerWidth_pos R P d hd hR hP) h d))
      (productLaw (rationalStationaryLaw R P d hd e)
        (uniformOffsetLaw e (integerWidth R P d) (integerWidth_pos R P d hd hR hP))) : ℝ) ≤
      (variation (rationalWalkLaw R P d hd hfree e (d ^ 50 * (h + 1) ^ 2) a)
        (rationalStationaryLaw R P d hd e) : ℝ) +
      (variation (boundedOffsetLaw e (integerWidth R P d) (integerWidth_pos R P d hd hR hP) h d)
        (uniformOffsetLaw e (integerWidth R P d) (integerWidth_pos R P d hd hR hP)) : ℝ) := by
    exact_mod_cast hv
  have hm := rationalWalkLaw_variation R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal
    e hPL hCheeger h a
  exact hvc.trans (by nlinarith)

end

end ContingencyTables.GridBoundary

end OAI
