import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Differentials.TorusQuotientDimensionPosCotangentFinrankThree

namespace OAI

namespace SiegelZeros

section
namespace WeightedTorusJets.Geometry

open scoped Pointwise

theorem rectangular_graded_piece_generated_by_degree_one {σ K : Type*} [CommRing K]
    (k : σ → ℕ) (hk : ∀ i, k i ≠ 0) (n : ℕ) :
    let A := MvPolynomial σ K ⧸ rectangularIdeal k
    let N : Ideal A := RingHom.ker (rectangularAugmentation k hk).toRingHom
    Submodule.span K
      ((fun x : ↥(N ^ n) => (Submodule.Quotient.mk x : idealPowLayer N n)) ''
        {x : ↥(N ^ n) | (x : A) ∈ (N : Set A) ^ n}) = ⊤ := by
  let A := MvPolynomial σ K ⧸ rectangularIdeal k
  let ε : A →ₐ[K] K := rectangularAugmentation k hk
  let N : Ideal A := RingHom.ker ε.toRingHom
  let S : Set A := (N : Set A) ^ n
  let U : Submodule K (idealPowLayer N n) := Submodule.span K
    ((fun x : ↥(N ^ n) => (Submodule.Quotient.mk x : idealPowLayer N n)) ''
      {x : ↥(N ^ n) | (x : A) ∈ S})
  have hspan : Submodule.span A S = N ^ n := (Submodule.pow_eq_span_pow_set N n).symm
  have hscalar (a : A) (x : ↥(N ^ n)) :
      (Submodule.Quotient.mk (a • x) : idealPowLayer N n) =
        ε a • (Submodule.Quotient.mk x : idealPowLayer N n) := by
    rw [← Submodule.Quotient.mk_smul, ← algebraMap_smul A (ε a) x]
    apply (idealPowLayer_eq N n _ _).mpr
    change a * (x : A) - algebraMap K A (ε a) * (x : A) ∈ (N ^ (n + 1) : Ideal A)
    rw [← sub_mul]
    rw [show (N ^ (n + 1) : Ideal A) = N * N ^ n from pow_succ' N n]
    apply Ideal.mul_mem_mul _ x.property
    change ε (a - algebraMap K A (ε a)) = 0
    simp
  have hmem (a : A) (ha : a ∈ Submodule.span A S) :
      ∀ h : a ∈ N ^ n, (Submodule.Quotient.mk ⟨a, h⟩ : idealPowLayer N n) ∈ U := by
    induction ha using Submodule.span_induction with
    | mem a ha =>
        intro h
        exact Submodule.subset_span ⟨⟨a, h⟩, ha, rfl⟩
    | zero =>
        intro h
        exact U.zero_mem
    | add a b ha hb ia ib =>
        intro h
        have haN : a ∈ N ^ n := hspan ▸ ha
        have hbN : b ∈ N ^ n := hspan ▸ hb
        exact U.add_mem (ia haN) (ib hbN)
    | smul a b hb ih =>
        intro h
        have hbN : b ∈ N ^ n := hspan ▸ hb
        change (Submodule.Quotient.mk (a • (⟨b, hbN⟩ : ↥(N ^ n))) : idealPowLayer N n) ∈ U
        rw [hscalar]
        exact U.smul_mem (ε a) (ih hbN)
  apply top_unique
  intro z _
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact hmem x (hspan.symm ▸ x.property) x.property

end WeightedTorusJets.Geometry

end

end SiegelZeros

end OAI
