import Mathlib.Algebra.BigOperators.Field
import OAI.Computability.PerfectCompleteness.Foundations.DualQuotientRowsLemmas

namespace OAI


namespace PerfectCompleteness.OutputCharacters

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness.SmallBias
open PerfectCompleteness.SmallBiasSlice

noncomputable section

variable {Ω I J : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

omit [DecidableEq I] in
theorem sliceNumerator_const_mul (μ : FiniteDistribution Ω)
    (A : Ω → I → Bool) (t : I → Bool) (c : ℝ) (g : Ω → ℝ) :
    sliceNumerator μ A t (fun x => c * g x) = c * sliceNumerator μ A t g := by
  unfold sliceNumerator
  calc
    _ = μ.expectation (fun x => c * (if A x = t then g x else 0)) := by
      congr 1
      funext x
      by_cases hx : A x = t <;> simp [hx]
    _ = _ := expectation_const_mul μ c _

omit [DecidableEq I] in
theorem abs_sliceNumerator_le_mass (μ : FiniteDistribution Ω)
    (A : Ω → I → Bool) (t : I → Bool) (g : Ω → ℝ)
    (hg : ∀ x, |g x| ≤ 1) :
    |sliceNumerator μ A t g| ≤ sliceMass μ A t := by
  classical
  apply abs_le.mpr
  constructor
  · have h := expectation_mono μ
        (a := fun x => -(if A x = t then (1 : ℝ) else 0))
        (b := fun x => if A x = t then g x else 0) (by
          intro x
          by_cases hx : A x = t
          · simpa only [ite_eq_left hx] using (abs_le.mp (hg x)).1
          · simp only [ite_eq_right hx, neg_zero, le_refl])
    simpa only [expectation_neg, sliceMass, sliceNumerator] using h
  · change μ.expectation (fun x => if A x = t then g x else 0) ≤
        μ.expectation (fun x => if A x = t then (1 : ℝ) else 0)
    apply expectation_mono μ
    intro x
    by_cases hx : A x = t
    · simpa only [ite_eq_left hx] using (abs_le.mp (hg x)).2
    · simp only [ite_eq_right hx, le_refl]

def sliceCorrelation (μ : FiniteDistribution Ω) (A : Ω → I → Bool)
    (t : I → Bool) (g : Ω → ℝ) : ℝ :=
  sliceNumerator μ A t g / sliceMass μ A t

def conditionalEquality (μ : FiniteDistribution Ω) (A : Ω → I → Bool)
    (t : I → Bool) (G T : Ω → J → Bool) : ℝ :=
  sliceCorrelation μ A t (fun x => if G x = T x then 1 else 0)

omit [DecidableEq I] in
theorem abs_sliceCorrelation_le_one (μ : FiniteDistribution Ω)
    (A : Ω → I → Bool) (t : I → Bool) (g : Ω → ℝ)
    (hmass : 0 < sliceMass μ A t) (hg : ∀ x, |g x| ≤ 1) :
    |sliceCorrelation μ A t g| ≤ 1 := by
  unfold sliceCorrelation
  rw [abs_div, abs_of_pos hmass]
  exact (div_le_one hmass).2 (abs_sliceNumerator_le_mass μ A t g hg)

omit [DecidableEq I] in
theorem sliced_output_kernel (μ : FiniteDistribution Ω)
    (A : Ω → I → Bool) (t : I → Bool) (G T : Ω → J → Bool) :
    (∑ s : J → Bool, sliceNumerator μ A t
      (fun x => maskChar s (G x) * maskChar s (T x))) =
      (Fintype.card (J → Bool) : ℝ) * sliceNumerator μ A t
        (fun x => if G x = T x then (1 : ℝ) else 0) := by
  classical
  have hpoint : ∀ x,
      (∑ s : J → Bool, if A x = t then
        maskChar s (G x) * maskChar s (T x) else 0) =
      (Fintype.card (J → Bool) : ℝ) *
        (if A x = t then (if G x = T x then (1 : ℝ) else 0) else 0) := by
    intro x
    by_cases hx : A x = t
    · simp only [ite_eq_left hx]
      rw [maskChar_kernel]
      by_cases heq : G x = T x <;> simp [heq]
    · simp [hx]
  calc
    _ = μ.expectation (fun x => ∑ s : J → Bool, if A x = t then
        maskChar s (G x) * maskChar s (T x) else 0) :=
      (expectation_sum μ (fun s x => if A x = t then
        maskChar s (G x) * maskChar s (T x) else 0)).symm
    _ = μ.expectation (fun x => (Fintype.card (J → Bool) : ℝ) *
        (if A x = t then (if G x = T x then (1 : ℝ) else 0) else 0)) := by
      simp only [hpoint]
    _ = _ := expectation_const_mul μ _ _

omit [DecidableEq I] in
theorem sum_output_correlations (μ : FiniteDistribution Ω)
    (A : Ω → I → Bool) (t : I → Bool) (G T : Ω → J → Bool) :
    (∑ s : J → Bool, sliceCorrelation μ A t
      (fun x => maskChar s (G x) * maskChar s (T x))) =
      (Fintype.card (J → Bool) : ℝ) * conditionalEquality μ A t G T := by
  simp only [sliceCorrelation, conditionalEquality]
  rw [← Finset.sum_div, sliced_output_kernel]
  ring

theorem exists_large_outside {K : Type*} [Fintype K] [Nonempty K]
    (bad : Finset K) (c : K → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (hc : ∀ j, |c j| ≤ 1)
    (hbad : (bad.card : ℝ) < (Fintype.card K : ℝ) * rho / 8)
    (htotal : (Fintype.card K : ℝ) * rho ≤ ∑ j, c j) :
    ∃ j, j ∉ bad ∧ rho / 2 ≤ |c j| := by
  classical
  by_contra h
  have hsmall : ∀ j, j ∉ bad → |c j| < rho / 2 := by
    intro j hj
    exact lt_of_not_ge (fun hh => h ⟨j, hj, hh⟩)
  have hterm : ∀ j, c j ≤ (if j ∈ bad then (1 : ℝ) else 0) + rho / 2 := by
    intro j
    by_cases hj : j ∈ bad
    · have hb := (abs_le.mp (hc j)).2
      simp only [ite_eq_left hj]
      linarith
    · have hs := (le_abs_self (c j)).trans (hsmall j hj).le
      simpa only [ite_eq_right hj, zero_add] using hs
  have hsum := Finset.sum_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset K)) => hterm j)
  have hsum' : (∑ j, c j) ≤
      (bad.card : ℝ) + (Fintype.card K : ℝ) * (rho / 2) := by
    simpa [Finset.sum_add_distrib] using hsum
  have hN : (0 : ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  have hNrho : 0 < (Fintype.card K : ℝ) * rho := mul_pos hN hrho
  nlinarith

omit [DecidableEq I] in
theorem equality_implies_nonbad_correlation (μ : FiniteDistribution Ω)
    (A : Ω → I → Bool) (t : I → Bool) (G T : Ω → J → Bool)
    (bad : Finset (J → Bool)) (rho : ℝ) (hrho : 0 < rho)
    (hmass : 0 < sliceMass μ A t)
    (hbad : (bad.card : ℝ) / (Fintype.card (J → Bool) : ℝ) < rho / 8)
    (hequality : rho ≤ conditionalEquality μ A t G T) :
    ∃ s : J → Bool, s ∉ bad ∧ rho / 2 ≤
      |sliceCorrelation μ A t (fun x => maskChar s (G x) * maskChar s (T x))| := by
  have hN : (0 : ℝ) < Fintype.card (J → Bool) := Nat.cast_pos.mpr Fintype.card_pos
  apply exists_large_outside bad _ rho hrho
  · intro s
    apply abs_sliceCorrelation_le_one μ A t _ hmass
    intro x
    simp only [abs_mul, abs_maskChar, one_mul, le_refl]
  · have h := (div_lt_iff₀ hN).1 hbad
    nlinarith
  · rw [sum_output_correlations]
    exact mul_le_mul_of_nonneg_left hequality hN.le

omit [DecidableEq I] [DecidableEq J] in
theorem abs_conditional_sign_transport (μ : FiniteDistribution Ω)
    (A : Ω → I → Bool) (t : I → Bool)
    (G T : Ω → J → Bool) (s : J → Bool)
    (φ : Ω → ℝ) (sign : ℝ) (hsign : |sign| = 1)
    (hT : ∀ x, maskChar s (T x) = sign * φ x) :
    |sliceCorrelation μ A t (fun x => maskChar s (G x) * maskChar s (T x))| =
      |sliceCorrelation μ A t (fun x => maskChar s (G x) * φ x)| := by
  have hfun : (fun x => maskChar s (G x) * maskChar s (T x)) =
      (fun x => sign * (maskChar s (G x) * φ x)) := by
    funext x
    rw [hT]
    ring
  unfold sliceCorrelation
  rw [hfun, sliceNumerator_const_mul]
  simp only [abs_div, abs_mul, hsign, one_mul]


variable {F : Type*} [AddCommMonoid F] [Fintype F]

theorem equality_implies_affine_heavy_witness (μ : FiniteDistribution Ω)
    (χ : F → Ω → ℝ) (hzero : ∀ x, χ 0 x = 1)
    (hadd : ∀ a b x, χ (a + b) x = χ a x * χ b x)
    (rows : I → F) (A : Ω → I → Bool)
    (hrows : ∀ i x, χ (rows i) x = bitSign (A x i))
    (hindependent : Function.Injective (rowCombination rows))
    (t : I → Bool) (G T : Ω → J → Bool)
    (base : (J → Bool) → F) (sign : (J → Bool) → ℝ)
    (hsign : ∀ s, |sign s| = 1)
    (htarget : ∀ s x, maskChar s (T x) = sign s * χ (base s) x)
    (bad : Finset (J → Bool)) (rho h0 biasBound : ℝ)
    (hrho : 0 < rho) (hh0 : 0 < h0)
    (hsize : h0 ≤ 1 / (Fintype.card (I → Bool) : ℝ))
    (hb : 0 ≤ biasBound) (hbsmall : biasBound ≤ h0 / 2)
    (hbias : ∀ a : F, a ≠ 0 → |μ.expectation (χ a)| ≤ biasBound)
    (hbad : (bad.card : ℝ) / (Fintype.card (J → Bool) : ℝ) < rho / 8)
    (hequality : rho ≤ conditionalEquality μ A t G T) :
    ∃ s : J → Bool, s ∉ bad ∧ ∃ mask : I → Bool,
      base s + rowCombination rows mask ∈
        heavySet μ χ (fun x => maskChar s (G x)) (rho * h0 / 4) := by
  have hmaskbias : ∀ mask : I → Bool, mask ≠ (fun _ => false) →
      |μ.expectation (fun x => maskChar mask (A x))| ≤ biasBound := by
    intro mask hmask
    have hne : rowCombination rows mask ≠ 0 := by
      intro hz
      apply hmask
      apply hindependent
      simpa using hz
    have h := hbias (rowCombination rows mask) hne
    change |μ.expectation (fun x => χ (rowCombination rows mask) x)| ≤ biasBound at h
    simpa only [character_rowCombination χ hzero hadd rows A hrows] using h
  have hmass : 0 < sliceMass μ A t := by
    have h := sliceMass_lower μ A t biasBound hb hmaskbias
    linarith
  obtain ⟨s, hsbad, hcorr⟩ :=
    equality_implies_nonbad_correlation μ A t G T bad rho hrho hmass hbad hequality
  rw [abs_conditional_sign_transport μ A t G T s (χ (base s)) (sign s)
    (hsign s) (htarget s)] at hcorr
  refine ⟨s, hsbad, ?_⟩
  exact affine_coset_heavy_witness μ χ hzero hadd rows A hrows hindependent t
    (fun x => maskChar s (G x)) (base s) rho h0 biasBound hrho hh0 hsize hb hbsmall
    hbias hcorr


end

end PerfectCompleteness.OutputCharacters

end OAI
