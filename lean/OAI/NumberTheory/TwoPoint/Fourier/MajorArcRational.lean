import OAI.NumberTheory.TwoPoint.Fourier.MajorArcResidues
import OAI.NumberTheory.TwoPoint.Bounds.ProgressionFourier

namespace OAI

/-! Resolving a rational additive phase into its residue classes before
the multiplicative character expansion. Only a factor equal to the modulus
is lost; no Gauss-sum estimate is needed for the application. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma major_arc_rational_character (q : ℕ) [NeZero q] (r : ℤ) (n : ℕ) :
    additiveCharacter ((r : ℝ) / q) n =
      ZMod.stdAddChar ((r : ZMod q) * (n : ZMod q)) := by
  rw [← Int.cast_natCast n, ← Int.cast_mul, ZMod.stdAddChar_coe]
  unfold additiveCharacter
  congr 1
  push_cast
  ring

lemma major_arc_residue_partition (S : Finset ℕ) (a : ℕ → ℂ)
    (q : ℕ) [NeZero q] (r : ℤ) :
    (∑ n ∈ S, a n * additiveCharacter ((r : ℝ) / q) n) =
      ∑ b : ZMod q, ZMod.stdAddChar ((r : ZMod q) * b) *
        ∑ n ∈ S, if n % q = b.val then a n else 0 := by
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  rw [sum_eq_single (n : ZMod q)]
  · simp [ZMod.val_natCast, major_arc_rational_character, mul_comm]
  · intro b _ hbn
    have hne : n % q ≠ b.val := by
      intro he
      apply hbn
      apply ZMod.val_injective
      simpa only [ZMod.val_natCast] using he.symm
    simp [hne]
  · simp

lemma major_arc_rational_sum_norm (S : Finset ℕ) (a : ℕ → ℂ)
    (q : ℕ) [NeZero q] (r : ℤ) :
    ‖∑ n ∈ S, a n * additiveCharacter ((r : ℝ) / q) n‖ ≤
      ∑ b : ZMod q, ‖∑ n ∈ S, if n % q = b.val then a n else 0‖ := by
  rw [major_arc_residue_partition]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro b _
  simp only [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul, le_refl]

/-- A common bound for the reduced, twisted intervals controls the
rational frequency with the exact modulus loss. -/
theorem major_arc_typical_rational_bound {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ)
    (hF : ∀ a b, 0 < a → 0 < b → F (a * b) = F a * F b)
    (hFb : OneBounded F) (q X H : ℕ) [NeZero q] (r : ℤ) (K : ℝ)
    (havoid : ∀ b : ZMod q, mrtPrimeAvoids (J.biUnion P) (b.val.gcd q))
    (hK : ∀ (b : ZMod q) (χ : DirichletCharacter ℂ (q / b.val.gcd q)),
      (b.val.gcd q : ℝ) * shortExponentialIntegral
        (mrtTypicalCoefficient J P (twistByCharacter F χ))
        (X / b.val.gcd q + 1) (H / b.val.gcd q + 1) 0 + X ≤ K) :
    shortExponentialIntegral (mrtTypicalCoefficient J P F) X H ((r : ℝ) / q) ≤
      (q : ℝ) * K := by
  rw [shortExponentialIntegral_eq_sum]
  calc
    _ ≤ ∑ v ∈ range X, ∑ b : ZMod q,
        ‖∑ n ∈ Icc (v + 1) (v + H),
          if n % q = b.val then mrtTypicalCoefficient J P F n else 0‖ := by
      apply sum_le_sum
      intro v _
      rw [shortExponentialSum_at_nat]
      exact major_arc_rational_sum_norm _ _ q r
    _ = ∑ b : ZMod q, ∑ v ∈ range X,
        ‖∑ n ∈ Icc (v + 1) (v + H),
          if n % q = b.val then mrtTypicalCoefficient J P F n else 0‖ := sum_comm
    _ ≤ ∑ _b : ZMod q, K := by
      apply sum_le_sum
      intro b _
      have hres := major_arc_typical_residue_average J P hP F hF hFb q b.val X H
        (NeZero.pos q) (havoid b)
      rw [Nat.mod_eq_of_lt b.val_lt] at hres
      apply hres.trans
      have hd := Nat.gcd_pos_of_pos_right b.val (NeZero.pos q)
      have hq' : 0 < q / b.val.gcd q := Nat.div_pos
        (Nat.le_of_dvd (NeZero.pos q) (Nat.gcd_dvd_right b.val q)) hd
      let : NeZero (q / b.val.gcd q) := ⟨hq'.ne'⟩
      have hφ := (Nat.totient_pos.mpr hq')
      have hc : Fintype.card (DirichletCharacter ℂ (q / b.val.gcd q)) =
          (q / b.val.gcd q).totient := by
        rw [← Nat.card_eq_fintype_card,
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
      calc
        _ ≤ ((q / b.val.gcd q).totient : ℝ)⁻¹ *
            ∑ _χ : DirichletCharacter ℂ (q / b.val.gcd q), K :=
          mul_le_mul_of_nonneg_left (sum_le_sum (fun χ _ => hK b χ)) (by positivity)
        _ = K := by simp [hc, ne_of_gt hφ]
    _ = _ := by simp [ZMod.card]

end TwoPointCorrelations

end OAI
