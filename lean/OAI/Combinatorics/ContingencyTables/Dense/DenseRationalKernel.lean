import OAI.Combinatorics.ContingencyTables.Dense.DenseRationalTrial
import OAI.Combinatorics.ContingencyTables.Dense.DenseMixing

namespace OAI

/-! # Rational transition and walk laws for the actual dense bin chain -/

namespace ContingencyTables.GridBoundary

open CommonBasesFPRAS ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def rationalProposal (d : ℕ) : ℚ := 1 / (2 : ℚ) ^ Nat.clog 2 (8 * d)

def rationalMove (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a b : Grid (I := Fin q) (4 * d ^ 8)) : ℚ :=
  if Neighbor a b then rationalProposal d * min 1 (rationalBinWeight R P d e b / rationalBinWeight R P d e a)
    else 0

def rationalTransition (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a b : Grid (I := Fin q) (4 * d ^ 8)) : ℚ :=
  rationalMove R P d e a b + if a = b then 1 - ∑ c, rationalMove R P d e a c else 0

theorem rationalMove_cast (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a b : Grid (I := Fin q) (4 * d ^ 8)) :
    (rationalMove R P d e a b : ℝ) =
      MetropolisChain.move (denseBinWeight R P d e) Neighbor (binProposal d) a b := by
  unfold rationalMove MetropolisChain.move
  split_ifs
  · simp only [Rat.cast_mul, Rat.cast_min, Rat.cast_one, Rat.cast_div,
      rationalBinWeight_cast, rationalProposal, binProposal, Rat.cast_pow, Rat.cast_ofNat]
  · exact Rat.cast_zero

theorem rationalTransition_cast (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    (a b : Grid (I := Fin q) (4 * d ^ 8)) :
    (rationalTransition R P d e a b : ℝ) =
      (denseBinChain R P d hd hfree e (denseGridSize_pos d hd)).P a b := by
  unfold rationalTransition
  dsimp only [denseBinChain, gridChain, MetropolisChain.chain, FiniteChain.ofMoves]
  by_cases hab : a = b <;>
    simp only [hab, ite_true, ite_false, Rat.cast_add, Rat.cast_sub, Rat.cast_sum,
      Rat.cast_one, Rat.cast_zero, rationalMove_cast]

def rationalTransitionLaw (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    (a : Grid (I := Fin q) (4 * d ^ 8)) : RationalLaw (Grid (I := Fin q) (4 * d ^ 8)) where
  mass := rationalTransition R P d e a
  nonnegative := fun b => by
    have h := (denseBinChain R P d hd hfree e (denseGridSize_pos d hd)).nonnegative a b
    rw [← rationalTransition_cast R P d hd hfree e] at h
    exact_mod_cast h
  total := by
    apply Rat.cast_injective (α := ℝ)
    simp only [Rat.cast_sum, rationalTransition_cast R P d hd hfree e, Rat.cast_one]
    exact (denseBinChain R P d hd hfree e (denseGridSize_pos d hd)).stochastic a

def rationalWalk (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) : ℕ → Grid (I := Fin q) (4 * d ^ 8) → Grid (I := Fin q) (4 * d ^ 8) → ℚ
  | 0, a, b => if a = b then 1 else 0
  | n + 1, a, b => ∑ c, rationalWalk R P d e n a c * rationalTransition R P d e c b

theorem rationalWalk_cast (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    (n : ℕ) (a b : Grid (I := Fin q) (4 * d ^ 8)) :
    (rationalWalk R P d e n a b : ℝ) =
      ((denseBinChain R P d hd hfree e (denseGridSize_pos d hd)).kernel.power n).P a b := by
  induction n generalizing a b with
  | zero => simp only [rationalWalk, FiniteKernel.power, FiniteKernel.identity]
            split_ifs <;> norm_num
  | succ n ih =>
    simp only [rationalWalk, Rat.cast_sum, Rat.cast_mul, ih, rationalTransition_cast R P d hd hfree e,
      FiniteKernel.power, FiniteKernel.comp, FiniteChain.kernel]

def rationalWalkLaw (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    (n : ℕ) (a : Grid (I := Fin q) (4 * d ^ 8)) : RationalLaw (Grid (I := Fin q) (4 * d ^ 8)) where
  mass := rationalWalk R P d e n a
  nonnegative := fun b => by
    have h := ((denseBinChain R P d hd hfree e (denseGridSize_pos d hd)).kernel.power n).nonnegative a b
    rw [← rationalWalk_cast R P d hd hfree e] at h
    exact_mod_cast h
  total := by
    apply Rat.cast_injective (α := ℝ)
    simp only [Rat.cast_sum, rationalWalk_cast R P d hd hfree e, Rat.cast_one]
    exact (denseBinChain R P d hd hfree e (denseGridSize_pos d hd)).kernel_power_stochastic n a

def rationalStationaryLaw (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (e : I × J ≃ Fin q) : RationalLaw (Grid (I := Fin q) (4 * d ^ 8)) := by
  let : Nonempty (Grid (I := Fin q) (4 * d ^ 8)) :=
    ⟨fun _ => ⟨0, by have h := denseGridSize_pos d hd; constructor <;> omega⟩⟩
  let w := rationalBinWeight R P d e
  have hw : ∀ a : Grid (I := Fin q) (4 * d ^ 8), 0 < w a := fun a => by
    unfold w rationalBinWeight
    positivity
  have hZ : 0 < ∑ a, w a := Finset.sum_pos (fun a _ => hw a) Finset.univ_nonempty
  exact ⟨fun a => w a / ∑ b, w b, fun a => (div_pos (hw a) hZ).le,
    by rw [← Finset.sum_div]; exact div_self (ne_of_gt hZ)⟩

theorem rationalStationaryLaw_cast (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    (a : Grid (I := Fin q) (4 * d ^ 8)) :
    ((rationalStationaryLaw R P d hd e).mass a : ℝ) =
      (denseBinChain R P d hd hfree e (denseGridSize_pos d hd)).π a := by
  change ((rationalBinWeight R P d e a / ∑ b, rationalBinWeight R P d e b : ℚ) : ℝ) = _
  simp only [Rat.cast_div, Rat.cast_sum, rationalBinWeight_cast]
  rfl

/-- The exact rational finite-walk law satisfies the dense sampler's mixing
bound. The hypotheses are precisely the two published geometric inputs. -/
theorem rationalWalkLaw_variation (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin q) (4 * d ^ 8)))
    (h : ℕ) (a : Grid (I := Fin q) (4 * d ^ 8)) :
    (variation (rationalWalkLaw R P d hd hfree e (d ^ 50 * (h + 1) ^ 2) a)
      (rationalStationaryLaw R P d hd e) : ℝ) ≤
        (2 : ℝ) ^ (-(4 * ((h : ℝ) + d))) := by
  let C := denseBinChain R P d hd hfree e (denseGridSize_pos d hd)
  let δ := (2 : ℝ) ^ (-(4 * ((h : ℝ) + d)))
  let n := d ^ 50 * (h + 1) ^ 2
  have hpoint (b : Grid (I := Fin q) (4 * d ^ 8)) :
      |(C.kernel.power n).P a b - C.π b| ≤ C.π b * δ := by
    have hm := denseBinChain_relative_mixing R P d hd hR hP hRmax hPmax
      hdimR hdimP hfree htotal e hPL hCheeger h a b
    change |C.iterate n (C.pointDensity b) a - 1| ≤ δ at hm
    rw [← C.kernel_power_density] at hm
    calc
      _ = C.π b * |(C.kernel.power n).P a b / C.π b - 1| := by
        calc
          _ = |C.π b * ((C.kernel.power n).P a b / C.π b - 1)| := by
            congr 1
            field_simp [ne_of_gt (C.positive b)]
          _ = _ := by rw [abs_mul, abs_of_pos (C.positive b)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (C.positive b).le
  have hsum := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hpoint b)
  rw [← Finset.sum_mul, C.normalized, one_mul] at hsum
  unfold variation
  simp only [Rat.cast_div, Rat.cast_sum, Rat.cast_abs, Rat.cast_sub, Rat.cast_ofNat,
    rationalWalkLaw, rationalWalk_cast R P d hd hfree e, rationalStationaryLaw_cast R P d hd hfree e]
  change (∑ b, |(C.kernel.power n).P a b - C.π b|) / 2 ≤ δ
  have hδ : 0 ≤ δ := (Real.rpow_pos_of_pos (by norm_num) _).le
  linarith

end

end ContingencyTables.GridBoundary

end OAI
