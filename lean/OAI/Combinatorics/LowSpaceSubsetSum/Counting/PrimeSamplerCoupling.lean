import OAI.Combinatorics.LowSpaceSubsetSum.Counting.FiniteProductSamplerCoupling
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.NestedPrimes

namespace OAI

/-! # Bounded fresh-prime calls for the nested three-factor sampler -/

noncomputable section

namespace LowSpaceSubsetSum

attribute [local instance] Classical.propDecidable

private instance factorNonempty (ell : ℕ) : Nonempty ↥(factorRange ell) :=
  (factorRange_nonempty ell).to_subtype

def factorOneEquiv {ell : ℕ} (h : ell < 4) : Unit ≃ ↥(factorRange ell) where
  toFun _ := ⟨1, by simp [factorRange, h]⟩
  invFun _ := ()
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    have hp : p.val = 1 := by simpa [factorRange, h] using p.property
    exact hp.symm

def factorPrimeEquiv {ell : ℕ} (h : 4 ≤ ell) : ↥(primeRange ell) ≃ ↥(factorRange ell) where
  toFun p := ⟨p.val, by simp [factorRange, show ¬ell < 4 by omega, p.property]⟩
  invFun p := ⟨p.val, by simpa [factorRange, show ¬ell < 4 by omega] using p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def factorCoupling (n ell : ℕ) : SamplerCoupling ↥(factorRange ell) :=
  if h : ell < 4 then (SamplerCoupling.pure ()).map (factorOneEquiv h)
  else (primeCoupling (by omega : 4 ≤ ell) n).map (factorPrimeEquiv (by omega))

theorem factorCoupling_uniform (n ell : ℕ) :
    (factorCoupling n ell).idealLaw = FiniteLaw.uniform := by
  by_cases h : ell < 4
  · rw [factorCoupling, dite_eq_left h, SamplerCoupling.map_idealLaw,
      SamplerCoupling.pure_uniform]
    exact FiniteLaw.map_equiv_uniform (factorOneEquiv h)
  · rw [factorCoupling, dite_eq_right h, SamplerCoupling.map_idealLaw,
      primeCoupling_uniform]
    let : Nonempty ↥(primeRange ell) := (primeRange_nonempty (by omega : 4 ≤ ell)).to_subtype
    exact FiniteLaw.map_equiv_uniform (factorPrimeEquiv (by omega : 4 ≤ ell))

theorem factorCoupling_failure {n ell : ℕ} (hell : ell ≤ n) :
    (factorCoupling n ell).failure ≤ Real.exp (-((n : ℝ) ^ 2 / 4)) := by
  by_cases h : ell < 4
  · rw [factorCoupling, dite_eq_left h, SamplerCoupling.map_failure,
      SamplerCoupling.pure_failure]
    positivity
  · rw [factorCoupling, dite_eq_right h, SamplerCoupling.map_failure]
    exact primeCoupling_failure (by omega) hell

def tripleFactorEquiv (a b c : ℕ) :
    ((↥(factorRange a) × ↥(factorRange b)) × ↥(factorRange c)) ≃
      ↥(tripleRange a b c) where
  toFun z := ⟨((z.1.1.val, z.1.2.val), z.2.val),
    Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨z.1.1.property, z.1.2.property⟩,
      z.2.property⟩⟩
  invFun z := ((⟨z.val.1.1, (Finset.mem_product.mp (Finset.mem_product.mp z.property).1).1⟩,
    ⟨z.val.1.2, (Finset.mem_product.mp (Finset.mem_product.mp z.property).1).2⟩),
    ⟨z.val.2, (Finset.mem_product.mp z.property).2⟩)
  left_inv _ := rfl
  right_inv _ := rfl

def triplePrimeCoupling (n a b c : ℕ) : SamplerCoupling ↥(tripleRange a b c) :=
  (((factorCoupling n a).prod (factorCoupling n b)).prod (factorCoupling n c)).map
    (tripleFactorEquiv a b c)

theorem triplePrimeCoupling_uniform (n a b c : ℕ) :
    (triplePrimeCoupling n a b c).idealLaw =
      @FiniteLaw.uniform _ inferInstance (tripleRange_nonempty a b c).to_subtype := by
  let : Nonempty ↥(tripleRange a b c) := (tripleRange_nonempty a b c).to_subtype
  rw [triplePrimeCoupling, SamplerCoupling.map_idealLaw,
    SamplerCoupling.prod_uniform _ _
      (SamplerCoupling.prod_uniform _ _ (factorCoupling_uniform n a)
        (factorCoupling_uniform n b)) (factorCoupling_uniform n c)]
  exact FiniteLaw.map_equiv_uniform (tripleFactorEquiv a b c)

theorem triplePrimeCoupling_failure {n a b c : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (hc : c ≤ n) :
    (triplePrimeCoupling n a b c).failure ≤ 3 * Real.exp (-((n : ℝ) ^ 2 / 4)) := by
  rw [triplePrimeCoupling, SamplerCoupling.map_failure]
  have h1 := SamplerCoupling.prod_failure_le
    ((factorCoupling n a).prod (factorCoupling n b)) (factorCoupling n c)
  have h2 := SamplerCoupling.prod_failure_le (factorCoupling n a) (factorCoupling n b)
  have h3 := factorCoupling_failure ha
  have h4 := factorCoupling_failure hb
  have h5 := factorCoupling_failure hc
  linarith

end LowSpaceSubsetSum

end

end OAI
