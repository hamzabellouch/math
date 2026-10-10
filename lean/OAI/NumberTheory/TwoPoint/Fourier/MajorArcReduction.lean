import OAI.NumberTheory.TwoPoint.Fourier.MajorArcRational
import OAI.NumberTheory.TwoPoint.Fourier.MajorArcPerturbation

namespace OAI

/-! The full major-arc reduction to the short means supplied by MRT's
Dirichlet-polynomial argument. All residues, divided scales, shorter lengths,
and rounding errors remain explicit. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma major_arc_character_distance (F : ℕ → ℂ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) (N : ℕ) :
    squaredDistance (twistByCharacter F χ) (mrtArchimedeanTwist t) N =
      squaredDistance F (characterTwist (conjugateCharacter χ) t) N := by
  unfold squaredDistance
  apply sum_congr rfl
  intro p _
  simp only [twistByCharacter, mrtArchimedeanTwist, characterTwist,
    conjugateCharacter_apply, map_mul, Complex.conj_conj, mul_assoc]

lemma MRTDistanceLowerBound.major_arc_character {F : ℕ → ℂ} {X H : ℕ} {M : ℝ}
    (hd : MRTDistanceLowerBound F X H M) (q : ℕ) (hq : 0 < q)
    (hqmax : (q : ℝ) ≤ mrtModulusCutoff X H)
    (χ : DirichletCharacter ℂ q) (t : ℝ) (ht : |t| ≤ (X : ℝ)) :
    M ≤ squaredDistance (twistByCharacter F χ) (mrtArchimedeanTwist t) X := by
  rw [major_arc_character_distance]
  exact hd q hq hqmax (conjugateCharacter χ) t ht

theorem major_arc_reduction {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ)
    (hF : ∀ a b, 0 < a → 0 < b → F (a * b) = F a * F b)
    (hFb : OneBounded F) (q X H : ℕ) [NeZero q] (hH : 0 < H)
    (r : ℤ) (β W K : ℝ) (hK : 0 ≤ K)
    (hβ : |β| ≤ W / ((H : ℝ) * q))
    (havoid : ∀ b : ZMod q, mrtPrimeAvoids (J.biUnion P) (b.val.gcd q))
    (hshort : ∀ (h : ℕ), 1 ≤ h → h ≤ H →
      ∀ (b : ZMod q) (χ : DirichletCharacter ℂ (q / b.val.gcd q)),
        (b.val.gcd q : ℝ) * shortExponentialIntegral
          (mrtTypicalCoefficient J P (twistByCharacter F χ))
          (X / b.val.gcd q + 1) (h / b.val.gcd q + 1) 0 + X ≤ K) :
    shortExponentialIntegral (mrtTypicalCoefficient J P F) X H
      ((r : ℝ) / q + β) ≤ ((q : ℝ) + 2 * Real.pi * W) * K := by
  have hprefix (h : ℕ) (hh : 1 ≤ h) (hhH : h ≤ H) :
      shortExponentialIntegral (mrtTypicalCoefficient J P F) X h ((r : ℝ) / q) ≤
        (q : ℝ) * K :=
    major_arc_typical_rational_bound J P hP F hF hFb q X h r K havoid (hshort h hh hhH)
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hqr : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hb : |β| * ((H : ℝ) * q) ≤ W :=
    (le_div_iff₀ (mul_pos hHr hqr)).mp hβ
  calc
    _ ≤ (1 + 2 * Real.pi * |β| * H) * ((q : ℝ) * K) :=
      major_arc_integral_perturbation_uniform _ X H hH _ β _
        (mul_nonneg hqr.le hK) hprefix
    _ = (q : ℝ) * K + (2 * Real.pi * K) * (|β| * ((H : ℝ) * q)) := by ring
    _ ≤ (q : ℝ) * K + (2 * Real.pi * K) * W :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hb (by positivity))
    _ = _ := by ring

end TwoPointCorrelations

end OAI
