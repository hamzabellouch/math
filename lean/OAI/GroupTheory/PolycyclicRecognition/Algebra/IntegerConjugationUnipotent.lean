import OAI.GroupTheory.PolycyclicRecognition.Algebra.DualUnipotentPower
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.RingTheory.Flat.Basic

namespace OAI

/-! # Unipotent powers of integral conjugation actions

For a finite free abelian quotient of a normal subgroup, integrality and
splitting of the eigenvalues are constructed from the characteristic
polynomial. They are not extra spectral hypotheses.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct Polynomial

theorem dual_end_charpoly {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] (T : Module.End K V) :
    T.dualMap.charpoly = T.charpoly := by
  let b := Module.Free.chooseBasis K V
  rw [← LinearMap.charpoly_toMatrix T.dualMap b.dualBasis,
    LinearMap.dualMap_def, LinearMap.toMatrix_transpose, Matrix.charpoly_transpose,
    LinearMap.charpoly_toMatrix T b]

theorem integer_tensor_unit_span {K A N : Type*} [Field K] [CharZero K]
    [AddCommGroup A] [Group N] (q : N →* Multiplicative A) (hq : Function.Surjective q) :
    Submodule.span K (Set.range (fun x : N => (1 : K) ⊗ₜ[ℤ] (q x).toAdd)) = ⊤ := by
  apply top_unique
  suffices h : ∀ v : K ⊗[ℤ] A,
      v ∈ Submodule.span K (Set.range (fun x : N => (1 : K) ⊗ₜ[ℤ] (q x).toAdd)) by
    intro v _
    exact h v
  intro v
  induction v using TensorProduct.inductionOn with
  | tmul k a =>
    obtain ⟨x, hx⟩ := hq (Multiplicative.ofAdd a)
    have he : (q x).toAdd = a := congrArg Multiplicative.toAdd hx
    have h := (Submodule.span K (Set.range (fun x : N => (1 : K) ⊗ₜ[ℤ] (q x).toAdd))).smul_mem
      k (Submodule.subset_span (Set.mem_range_self x))
    simpa only [he, TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h
  | add v w hv hw => exact Submodule.add_mem _ hv hw

theorem polynomial_growth_integer_conjugation_unipotent_power
    {G A : Type*} [Group G] [DecidableEq G] [AddCommGroup A]
    [Module.Free ℤ A] [Module.Finite ℤ A]
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d)
    (N : Subgroup G) [N.Normal] (t : G)
    (q : N →* Multiplicative A) (hq : Function.Surjective q)
    (T : Module.End ℤ A) (hT : ∀ x, (q (MulAut.conjNormal t x)).toAdd = T (q x).toAdd) :
    ∃ m : ℕ, 0 < m ∧ IsNilpotent (T ^ m - 1) := by
  let p := T.charpoly.map (Int.castRingHom ℚ)
  let K := p.SplittingField
  let : NumberField K := { }
  let U := T.baseChange K
  let qK : N →* Multiplicative (K ⊗[ℤ] A) :=
    (TensorProduct.mk ℤ K A 1).toAddMonoidHom.toMultiplicative.comp q
  have hqK : Submodule.span K (Set.range (fun x => (qK x).toAdd)) = ⊤ :=
    integer_tensor_unit_span q hq
  have hU (x : N) : (qK (MulAut.conjNormal t x)).toAdd = U (qK x).toAdd := by
    change (1 : K) ⊗ₜ[ℤ] (q (MulAut.conjNormal t x)).toAdd =
      T.baseChange K ((1 : K) ⊗ₜ[ℤ] (q x).toAdd)
    rw [hT, LinearMap.baseChange_tmul]
  have hchar : U.dualMap.charpoly = T.charpoly.map (algebraMap ℤ K) := by
    rw [dual_end_charpoly, LinearMap.charpoly_baseChange]
  have hsplit : U.dualMap.charpoly.Splits := by
    rw [hchar]
    have h := Polynomial.SplittingField.splits p
    change ((T.charpoly.map (algebraMap ℤ ℚ)).map (algebraMap ℚ K)).Splits at h
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq ℤ ℚ K] at h
    exact h
  have hint (z : K) (hz : Module.End.HasEigenvalue U.dualMap z) : IsIntegral ℤ z := by
    have hr := (Module.End.hasEigenvalue_iff_isRoot_charpoly U.dualMap z).mp hz
    rw [hchar] at hr
    refine ⟨T.charpoly, T.charpoly_monic, ?_⟩
    simpa only [Polynomial.IsRoot.def, Polynomial.eval_map] using hr
  obtain ⟨m, hm, hn⟩ := polynomial_growth_integral_conjugation_unipotent_power
    S hS hgen hvol N t qK hqK U hU hsplit hint
  refine ⟨m, hm, ?_⟩
  obtain ⟨r, hr⟩ := hn
  refine ⟨r, ?_⟩
  apply LinearMap.baseChangeHom_injective (R := ℤ) (S := K) (M := A) (N := A)
  change ((T ^ m - 1) ^ r).baseChange K = (0 : Module.End ℤ A).baseChange K
  simpa only [LinearMap.baseChange_pow, LinearMap.baseChange_sub,
    LinearMap.baseChange_one, LinearMap.baseChange_zero] using hr

end PolycyclicRecognition

end

end OAI
