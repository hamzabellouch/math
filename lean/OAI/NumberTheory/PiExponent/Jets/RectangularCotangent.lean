import Mathlib
import Mathlib.RingTheory.MvPowerSeries.Derivative
import OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity

namespace OAI

noncomputable section

namespace PiExponentApprox.TransverseMultiplicity

open MvPowerSeries

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

abbrev RectangularRing (n : σ → ℕ) :=
  MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n

omit [Fintype σ] [DecidableEq σ] in
theorem rectangularPositive (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i) : ∀ i, 0 < n i :=
  fun i => lt_of_lt_of_le (by norm_num) (hn i)

def rectangularAugmentationIdeal (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i) :
    Ideal (RectangularRing (K := K) n) :=
  RingHom.ker (rectangularAugmentation (K := K) n (rectangularPositive n hn))

def unitRectIndex (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i) (i : σ) : RectIndex n :=
  ⟨Finsupp.single i 1, by
    intro j
    by_cases h : j = i
    · subst j
      simpa using (show 1 < n i by have := hn i; omega)
    · simpa [Finsupp.single_eq_of_ne h] using rectangularPositive n hn j⟩

def rectangularFirstCoefficients (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i) :
    RectangularRing (K := K) n →ₗ[K] (σ → K) where
  toFun f i := rectangularQuotientCoefficients (K := K) n f (unitRectIndex n hn i)
  map_add' f g := by ext i; exact congrFun (map_add (rectangularQuotientCoefficients (K := K) n) f g) _
  map_smul' a f := by ext i; exact congrFun (map_smul (rectangularQuotientCoefficients (K := K) n) a f) _

omit [Fintype σ] in
@[simp] theorem rectangularFirstCoefficients_mk (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (f : MvPowerSeries σ K) (i : σ) :
    rectangularFirstCoefficients (K := K) n hn (Ideal.Quotient.mk (rectangularIdeal (K := K) n) f) i =
      coeff (Finsupp.single i 1) f := rfl

omit [Fintype σ] [DecidableEq σ] in

theorem firstCoeff_mul (f g : MvPowerSeries σ K) (i : σ) :
    coeff (Finsupp.single i 1) (f * g) =
      constantCoeff f * coeff (Finsupp.single i 1) g +
        constantCoeff g * coeff (Finsupp.single i 1) f := by
  have hh := congrArg (constantCoeff : MvPowerSeries σ K →+* K)
    ((MvPowerSeries.pderiv i).leibniz f g)
  simpa only [smul_eq_mul, map_add, map_mul,
    ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add,
    Finsupp.zero_apply, Nat.cast_zero, zero_add, mul_one] using hh

theorem rectangular_reconstruct (n : σ → ℕ) (f : RectangularRing (K := K) n) :
    f = ∑ d : RectIndex n,
      Ideal.Quotient.mk (rectangularIdeal (K := K) n)
        (monomial d.val (rectangularQuotientCoefficients (K := K) n f d)) := by
  apply (rectangularQuotientCoefficients_bijective (K := K) n).1
  rw [map_sum]
  funext e
  simp only [Finset.sum_apply, rectangularQuotientCoefficients_mk]
  change rectangularQuotientCoefficients (K := K) n f e =
    ∑ d : RectIndex n, coeff e.val
      (monomial d.val (rectangularQuotientCoefficients (K := K) n f d))
  symm
  rw [Finset.sum_eq_single e]
  · simp only [coeff_monomial_same]
  · intro d _ hde
    have hne : e.val ≠ d.val := by
      intro he
      exact hde (Subtype.ext he.symm)
    simp only [coeff_monomial, ite_eq_right hne]
  · intro h
    exact (h (Finset.mem_univ e)).elim

theorem rectangular_monomial_mem_square (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (d : σ →₀ ℕ) (a : K) (hd : d ≠ 0)
    (hunit : ∀ i, d ≠ Finsupp.single i 1) :
    Ideal.Quotient.mk (rectangularIdeal (K := K) n) (monomial d a) ∈
      (rectangularAugmentationIdeal (K := K) n hn) ^ 2 := by
  have hex : ∃ i, d i ≠ 0 := by
    by_contra! hh
    exact hd (by ext i; exact hh i)
  obtain ⟨i, hi⟩ := hex
  let e : σ →₀ ℕ := d - Finsupp.single i 1
  have he : e + Finsupp.single i 1 = d := Finsupp.sub_add_single_one_cancel hi
  have he0 : e ≠ 0 := by
    intro h
    apply hunit i
    simpa [h] using he.symm
  have hleft : Ideal.Quotient.mk (rectangularIdeal (K := K) n) (monomial (Finsupp.single i 1) (1 : K)) ∈
      rectangularAugmentationIdeal (K := K) n hn := by
    change constantCoeff (monomial (Finsupp.single i 1) (1 : K)) = 0
    have hsingle : (0 : σ →₀ ℕ) ≠ Finsupp.single i 1 := by
      intro h
      have hh := congrArg (fun d : σ →₀ ℕ => d i) h
      simp at hh
    simp [← coeff_zero_eq_constantCoeff, coeff_monomial, hsingle]
  have hright : Ideal.Quotient.mk (rectangularIdeal (K := K) n) (monomial e a) ∈
      rectangularAugmentationIdeal (K := K) n hn := by
    change constantCoeff (monomial e a) = 0
    simp [← coeff_zero_eq_constantCoeff, coeff_monomial, Ne.symm he0]
  rw [pow_two]
  have hh := Ideal.mul_mem_mul hleft hright
  convert hh using 1
  rw [← map_mul, monomial_mul_monomial, one_mul, add_comm, he]

theorem rectangular_mem_square_of_first_zero (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (f : RectangularRing (K := K) n)
    (hf : f ∈ rectangularAugmentationIdeal (K := K) n hn)
    (hfirst : rectangularFirstCoefficients (K := K) n hn f = 0) :
    f ∈ (rectangularAugmentationIdeal (K := K) n hn) ^ 2 := by
  rw [rectangular_reconstruct n f]
  apply Ideal.sum_mem
  intro d hd
  by_cases hd0 : d.val = 0
  · have hc : rectangularQuotientCoefficients (K := K) n f d = 0 := by
      obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective f
      change coeff d.val F = 0
      rw [hd0]
      exact hf
    simp [hc]
  · by_cases hu : ∃ i, d.val = Finsupp.single i 1
    · obtain ⟨i, hi⟩ := hu
      have hc : rectangularQuotientCoefficients (K := K) n f d = 0 := by
        have hh := congrFun hfirst i
        change rectangularQuotientCoefficients (K := K) n f (unitRectIndex n hn i) = 0 at hh
        have he : d = unitRectIndex n hn i := Subtype.ext hi
        simpa only [he] using hh
      simp [hc]
    · exact rectangular_monomial_mem_square n hn d.val _ hd0 (by simpa using hu)

def rectangularIdealFirstCoefficients (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i) :
    rectangularAugmentationIdeal (K := K) n hn →ₗ[K] (σ → K) :=
  (rectangularFirstCoefficients (K := K) n hn).comp
    ((rectangularAugmentationIdeal (K := K) n hn).subtype.restrictScalars K)

omit [Fintype σ] in
theorem rectangularIdealFirstCoefficients_mul (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (f g : rectangularAugmentationIdeal (K := K) n hn) :
    rectangularIdealFirstCoefficients (K := K) n hn (f * g) = 0 := by
  obtain ⟨F, hF⟩ := Ideal.Quotient.mk_surjective f.val
  obtain ⟨G, hG⟩ := Ideal.Quotient.mk_surjective g.val
  have hFc : constantCoeff F = 0 := by
    have hf := f.property
    change rectangularAugmentation (K := K) n (rectangularPositive n hn) f.val = 0 at hf
    simpa only [← hF, rectangularAugmentation_mk] using hf
  have hGc : constantCoeff G = 0 := by
    have hg := g.property
    change rectangularAugmentation (K := K) n (rectangularPositive n hn) g.val = 0 at hg
    simpa only [← hG, rectangularAugmentation_mk] using hg
  ext i
  change rectangularFirstCoefficients (K := K) n hn (f.val * g.val) i = 0
  rw [← hF, ← hG, ← map_mul, rectangularFirstCoefficients_mk, firstCoeff_mul, hFc, hGc]
  simp

def rectangularCotangentFirstCoefficients (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i) :
    (rectangularAugmentationIdeal (K := K) n hn).Cotangent →ₗ[K] (σ → K) :=
  Ideal.Cotangent.lift (rectangularIdealFirstCoefficients (K := K) n hn)
    (rectangularIdealFirstCoefficients_mul n hn)

omit [Fintype σ] in
@[simp] theorem rectangularCotangentFirstCoefficients_toCotangent
    (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (f : rectangularAugmentationIdeal (K := K) n hn) :
    rectangularCotangentFirstCoefficients (K := K) n hn
      ((rectangularAugmentationIdeal (K := K) n hn).toCotangent f) =
        rectangularFirstCoefficients (K := K) n hn f.val := rfl

theorem rectangularCotangentFirstCoefficients_injective
    (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i) :
    Function.Injective (rectangularCotangentFirstCoefficients (K := K) n hn) := by
  have hz : ∀ z, rectangularCotangentFirstCoefficients (K := K) n hn z = 0 → z = 0 := by
    intro z hz
    obtain ⟨f, rfl⟩ := (rectangularAugmentationIdeal (K := K) n hn).toCotangent_surjective z
    apply ((rectangularAugmentationIdeal (K := K) n hn).toCotangent_eq_zero f).mpr
    exact rectangular_mem_square_of_first_zero n hn f.val f.property hz
  intro x y h
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, h, sub_self]

end PiExponentApprox.TransverseMultiplicity

end

end OAI
