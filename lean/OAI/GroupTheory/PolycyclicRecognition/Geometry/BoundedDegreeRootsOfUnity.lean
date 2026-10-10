import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.RootsOfUnity.Minpoly

namespace OAI

/-! # Only finitely many roots of unity have bounded degree

The complex roots of the minimal polynomial are roots of the same equation
`X^m = 1`. Its integral coefficients are uniformly bounded by the degree,
so only finitely many minimal polynomials, and hence roots, can occur.
-/

noncomputable section
namespace PolycyclicRecognition
open Polynomial

theorem torsion_minpoly_coeff_bound
    {K : Type*} [Field K] [CharZero K] (z : K)
    (m : ℕ) (hm : 0 < m) (hz : z ^ m = 1) (D : ℕ)
    (hD : (minpoly ℤ z).natDegree ≤ D) (i : ℕ) :
    |(minpoly ℤ z).coeff i| ≤ (D.choose (D / 2) : ℤ) := by
  have hi : IsIntegral ℤ z := IsIntegral.of_pow hm (by rw [hz]; exact isIntegral_one)
  have hdvd : minpoly ℤ z ∣ (X ^ m - 1 : ℤ[X]) := by
    apply minpoly.isIntegrallyClosed_dvd hi
    simp only [map_sub, aeval_X_pow, map_one, hz, sub_self]
  let f := Int.castRingHom ℂ
  have hdvdC : (minpoly ℤ z).map f ∣ (X ^ m - 1 : ℂ[X]) := by
    have hh := _root_.map_dvd (mapRingHom f) hdvd
    simpa only [coe_mapRingHom, map_sub, map_pow, map_X, map_one] using hh
  have hroots (w : ℂ) (hw : w ∈ ((minpoly ℤ z).map f).roots) : ‖w‖ ≤ 1 := by
    have hp := ((mem_roots ((minpoly.monic hi).map f).ne_zero).mp hw).dvd hdvdC
    have he : w ^ m = 1 := by
      simpa only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_one, sub_eq_zero] using hp
    exact le_of_eq (Complex.norm_eq_one_of_pow_eq_one he (Nat.ne_of_gt hm))
  have hb := coeff_bdd_of_roots_le (B := (1 : ℝ)) f (minpoly.monic hi)
    (IsAlgClosed.splits _) hD hroots i
  simp only [max_self, one_pow, one_mul, coeff_map, f, Int.coe_castRingHom,
    Complex.norm_intCast] at hb
  exact_mod_cast hb

theorem finite_rootsOfUnity_of_bounded_degree
    (K : Type*) [Field K] [CharZero K] (D : ℕ) :
    {z : K | (∃ m : ℕ, 0 < m ∧ z ^ m = 1) ∧ (minpoly ℤ z).natDegree ≤ D}.Finite := by
  classical
  let C : ℤ := D.choose (D / 2)
  have hfin := bUnion_roots_finite (Int.castRingHom K) D (Set.finite_Icc (-C) C)
  apply hfin.subset
  rintro z ⟨⟨m, hm, hz⟩, hD⟩
  have hi : IsIntegral ℤ z := IsIntegral.of_pow hm (by rw [hz]; exact isIntegral_one)
  simp only [Set.mem_iUnion]
  refine ⟨minpoly ℤ z, ⟨hD, ?_⟩, ?_⟩
  · intro i
    exact (abs_le.mp (torsion_minpoly_coeff_bound z m hm hz D hD i))
  · apply Multiset.mem_toFinset.mpr
    apply (mem_roots ((minpoly.monic hi).map (Int.castRingHom K)).ne_zero).mpr
    rw [IsRoot.def, eval_map]
    exact minpoly.aeval ℤ z

end PolycyclicRecognition

end

end OAI
