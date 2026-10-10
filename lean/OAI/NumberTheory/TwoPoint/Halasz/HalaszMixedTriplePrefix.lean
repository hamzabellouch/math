import OAI.NumberTheory.TwoPoint.Halasz.HalaszMixedBounds
import OAI.NumberTheory.TwoPoint.Halasz.HalaszBoundedTriple

namespace OAI

/-! The mixed double convolution is the finite prefix of the
prime-prime-typical smooth series used by Perron inversion. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical LSeries.notation

lemma halasz_mixed_smooth_prefix (G B : ℕ → ℂ) (N M : ℕ) (hMN : M ≤ N)
    {R : ℝ} (hL : 0 ≤ R) (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime)
    (hcover : ∀ q : ℕ, q.Prime → q ≤ M → (q ∈ Q ↔ R < (q:ℝ))) :
    (∑ n ∈ Icc 1 M,
      (halaszFiniteCoefficient Q (fun q => (Real.log (q:ℝ):ℂ)*G q) ⍟
        halaszSmoothFunction B N) n) = halaszMixedPrimeConvolution G B M R M := by
  have hband : mrtPrimeBand R M = (Icc 1 M).filter (fun q => q∈Q) := by
    ext q
    constructor
    · intro hq
      have hp := mrtPrimeBand_prime hq
      have hb := mrtPrimeBand_bounds hL (Nat.cast_nonneg M) hq
      have hqM : q ≤ M := by exact_mod_cast hb.2
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.pos,hqM⟩,(hcover q hp hqM).mpr hb.1⟩
    · intro hq
      obtain ⟨hqM,hqQ⟩ := mem_filter.mp hq
      have hp := hQ q hqQ
      have hlarge := (hcover q hp (mem_Icc.mp hqM).2).mp hqQ
      apply mem_sdiff.mpr
      constructor
      · apply mem_filter.mpr
        exact ⟨by simpa only [Nat.floor_natCast,mem_Iic] using (mem_Icc.mp hqM).2,hp⟩
      · intro hsmall
        have hh := sievePrimesUpTo_le R hL q hsmall
        linarith
  rw [halasz_convolution_prefix,halaszMixedPrimeConvolution,hband,sum_filter]
  apply sum_congr rfl
  intro q hq
  have hs : (∑ m ∈ Icc 1 (M/q), halaszSmoothFunction B N m) =
      ∑ m ∈ Icc 1 (M/q), B m := by
    apply sum_congr rfl
    intro m hm
    exact halasz_smooth_function_eq (mem_Icc.mp hm).1
      (((mem_Icc.mp hm).2.trans (Nat.div_le_self M q)).trans hMN)
  rw [hs]
  by_cases hqQ : q∈Q <;> simp [halaszFiniteCoefficient,hqQ,mul_assoc]

lemma halasz_mixed_grouped_triple_prefix (G B : ℕ → ℂ) (N : ℕ)
    {R : ℝ} (hL : 0 ≤ R) (P Q : Finset ℕ) (hP : P ⊆ Icc 1 N)
    (hQ : ∀ q ∈ Q, q.Prime)
    (hcover : ∀ p ∈ P, ∀ q : ℕ, q.Prime → q ≤ N/p → (q∈Q ↔ R < (q:ℝ))) :
    (∑ n ∈ Icc 1 N,
      (halaszFiniteCoefficient P
        (fun p => (Real.log (p:ℝ):ℂ)*G p/(Real.log ((N:ℝ)/p):ℂ)) ⍟
        (halaszFiniteCoefficient Q (fun q => (Real.log (q:ℝ):ℂ)*G q) ⍟
          halaszSmoothFunction B N)) n) = halaszMixedGrouped G B N R P := by
  rw [halasz_finite_convolution_prefix P _ _ N hP]
  unfold halaszMixedGrouped
  apply sum_congr rfl
  intro p hp
  rw [halasz_mixed_smooth_prefix G B N (N/p) (Nat.div_le_self N p) hL Q hQ (hcover p hp)]
  ring

end TwoPointCorrelations

end OAI
