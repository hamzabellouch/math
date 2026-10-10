import OAI.NumberTheory.Ostmann.Characters.PrimitiveCharacterSieve
import OAI.NumberTheory.Ostmann.QuadraticSieve.ComplexJacobiPrimitive
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSieveDuality
import OAI.NumberTheory.Ostmann.Preliminaries.AdditiveSieveProof

namespace OAI

/-! # The initial quadratic-sieve bound from the proved additive large sieve -/

namespace Ostmann

open scoped BigOperators Classical

private theorem sum_interval_extension {R : Type*} [AddCommMonoid R]
    (N : ℕ) (S : Finset ℕ) (hS : ∀ n ∈ S, n ≤ N) (f : ℕ → R) :
    (∑ n : Fin (N + 1), if n.val ∈ S then f n.val else 0) = ∑ n ∈ S, f n := by
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => if n ∈ S then f n else 0)]
  have hsub : S ⊆ Finset.range (N + 1) := by
    intro n hn
    exact Finset.mem_range.mpr (by have := hS n hn; omega)
  have hh := Finset.sum_subset hsub (f := fun n => if n ∈ S then f n else 0)
    (by intro n _ hn; simp [hn])
  simpa only [Finset.sum_ite_mem, Finset.inter_self] using hh.symm

private noncomputable def quadraticArray (N : ℕ) (b : ℕ → ℂ) : Fin (N + 1) → ℂ :=
  fun n => if n.val ∈ oddSquarefreeRange N then b n.val else 0

private theorem quadraticArray_energy (N : ℕ) (b : ℕ → ℂ) :
    (∑ n, ‖quadraticArray N b n‖ ^ 2) = quadraticSieveEnergy N b := by
  have hh := sum_interval_extension N (oddSquarefreeRange N)
    (fun n hn => (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2) (fun n => ‖b n‖ ^ 2)
  simpa only [quadraticArray, apply_ite, norm_zero, ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, quadraticSieveEnergy] using hh

private theorem quadraticArray_character_sum (N : ℕ) (b : ℕ → ℂ) (m : ℕ) [NeZero m] :
    (∑ n, quadraticArray N b n * (jacobiComplex m)⁻¹ (n.val : ZMod m)) =
      quadraticSieveSum N b m := by
  rw [(jacobiComplex_isQuadratic m).inv]
  have hh := sum_interval_extension N (oddSquarefreeRange N)
    (fun n hn => (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2)
    (fun n => b n * (jacobiComplex m) (n : ZMod m))
  simpa only [quadraticArray, ite_mul, zero_mul, jacobiComplex_natCast,
    realJacobi, Complex.ofReal_intCast, quadraticSieveSum] using hh

 theorem quadraticSieveBound_additive (M N : ℕ) (hM : 1 ≤ M) :
    QuadraticSieveBound M N ((N : ℝ) + 1 + (M : ℝ) ^ 2) := by
  intro b
  let c := quadraticArray N b
  have hpoint (m : ℕ) (hm : m ∈ oddSquarefreeRange M) :
      ‖quadraticSieveSum N b m‖ ^ 2 ≤
        ∑ h ∈ reducedNumerators m, ‖additiveSieveSum c 0 m h‖ ^ 2 := by
    obtain ⟨hmrange, hmodd, hmsq⟩ := Finset.mem_filter.mp hm
    let : NeZero m := ⟨by have := (Finset.mem_Icc.mp hmrange).1; omega⟩
    have hi := primitive_character_sieve (jacobiComplex m)
      (jacobiComplex_squarefree_primitive m hmsq hmodd) c (fun n => (n.val : ZMod m))
    rw [quadraticArray_character_sum] at hi
    rw [sum_reducedNumerators_eq_units]
    simpa only [additiveSieveSum, sieveAdditivePhase_eq_stdAddChar, zero_add,
      Int.cast_natCast, ZMod.natCast_zmod_val, c] using hi
  have hsub : oddSquarefreeRange M ⊆ Finset.Icc 1 M := Finset.filter_subset _ _
  calc
    _ ≤ ∑ m ∈ oddSquarefreeRange M, ∑ h ∈ reducedNumerators m, ‖additiveSieveSum c 0 m h‖ ^ 2 :=
      Finset.sum_le_sum (fun m hm => hpoint m hm)
    _ ≤ ∑ m ∈ Finset.Icc 1 M, ∑ h ∈ reducedNumerators m, ‖additiveSieveSum c 0 m h‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ ≤ ((N + 1 : ℕ) + (M : ℝ) ^ 2) * ∑ n, ‖c n‖ ^ 2 :=
      publishedAdditiveLargeSieve (N + 1) M (by omega) hM 0 c
    _ = _ := by rw [show (∑ n, ‖c n‖ ^ 2) = quadraticSieveEnergy N b from quadraticArray_energy N b]; push_cast; ring

end Ostmann

end OAI
