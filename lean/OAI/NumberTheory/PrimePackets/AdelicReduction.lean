import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicPatch

namespace OAI

noncomputable section
open scoped TensorProduct RestrictedProduct Topology Pointwise
open Matrix Module Filter Set
namespace PrimeDegreePackets.Adelic

 

def IntegralFiniteGL {n : ℕ} (g : GL (Fin n) RationalFiniteAdeles) : Prop :=
  (∀ i j p, g.val i j p ∈ rationalLocalIntegers p) ∧
  (∀ i j p, (g⁻¹).val i j p ∈ rationalLocalIntegers p)

lemma localCoordinates_basisChange {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b m : Basis (Fin n) ℚ K) (p : Nat.Primes) (x : LocalAlgebra p.val K) :
    localAlgebraCoordinates p.val b x ᵥ*
        (finiteMatrixAt (GeneralLinearGroup.map rationalFiniteEmbedding (rowBasisChange b m)) p).val =
      localAlgebraCoordinates p.val m x := by
  have hmat : (m.baseChange (Padic p.val)).toMatrix (b.baseChange (Padic p.val)) =
      (m.toMatrix b).map (algebraMap ℚ (Padic p.val)) := by
    ext i j
    simp [Basis.toMatrix_apply,Basis.baseChange_apply,Basis.baseChange_repr_tmul,Algebra.smul_def]
  change (b.baseChange (Padic p.val)).repr x ᵥ*
    ((m.toMatrix b).map (algebraMap ℚ (Padic p.val)))ᵀ = _
  rw [← hmat,Matrix.vecMul_transpose,Basis.toMatrix_mulVec_repr]
  rfl

lemma localMatrixLattice_basisChange {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b m : Basis (Fin n) ℚ K) (g : GL (Fin n) RationalFiniteAdeles) (p : Nat.Primes) :
    localMatrixLattice m (GeneralLinearGroup.map rationalFiniteEmbedding (rowBasisChange m b) * g) p =
      localMatrixLattice b g p := by
  ext x
  simp only [mem_localMatrixLattice_iff]
  have hmul : finiteMatrixAt (GeneralLinearGroup.map rationalFiniteEmbedding
      (rowBasisChange m b) * g) p =
      finiteMatrixAt (GeneralLinearGroup.map rationalFiniteEmbedding (rowBasisChange m b)) p *
      finiteMatrixAt g p := by exact map_mul _ _ _
  rw [hmul,Units.val_mul,← Matrix.vecMul_vecMul,localCoordinates_basisChange]

lemma integralFiniteAt_of_lattice_eq {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) (g : GL (Fin n) RationalFiniteAdeles) (p : Nat.Primes)
    (h : localMatrixLattice b g p = localIntegralSpan p.val b) :
    (∀ i j, (finiteMatrixAt g p).val i j ∈ rationalLocalIntegers p) ∧
    (∀ i j, ((finiteMatrixAt g p)⁻¹).val i j ∈ rationalLocalIntegers p) := by
  classical
  constructor
  · intro i
    have hi : (b.baseChange (Padic p.val)) i ∈ localMatrixLattice b g p := by
      rw [h]
      exact Submodule.subset_span ⟨i,rfl⟩
    rw [mem_localMatrixLattice_iff] at hi
    have hcoord : localAlgebraCoordinates p.val b ((b.baseChange (Padic p.val)) i) =
        Pi.single i 1 := by
      change ⇑((b.baseChange (Padic p.val)).repr ((b.baseChange (Padic p.val)) i)) = _
      rw [Basis.repr_self]
      exact Finsupp.single_eq_pi_single i 1
    rw [hcoord,Matrix.single_one_vecMul] at hi
    exact hi
  · intro i
    let v : Fin n → Padic p.val := Pi.single i 1 ᵥ* ((finiteMatrixAt g p)⁻¹).val
    let x := (localAlgebraCoordinates p.val b).symm v
    have hx : x ∈ localMatrixLattice b g p := by
      rw [mem_localMatrixLattice_iff]
      dsimp only [x]
      rw [ContinuousLinearEquiv.apply_symm_apply]
      dsimp only [v]
      rw [Matrix.vecMul_vecMul,Units.inv_mul,Matrix.vecMul_one]
      intro j
      simp only [Pi.single_apply]
      split_ifs
      · exact (rationalLocalIntegers p).one_mem
      · exact (rationalLocalIntegers p).zero_mem
    rw [h,localIntegralSpan_mem] at hx
    change ∀ j, localAlgebraCoordinates p.val b x j ∈ rationalLocalIntegers p at hx
    dsimp only [x] at hx
    rw [ContinuousLinearEquiv.apply_symm_apply] at hx
    simpa [v,Matrix.single_vecMul] using hx

lemma completedLattice_integralSpan_basis {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : finrank ℚ K = n) (p : Nat.Primes) :
    completedLattice p.val M = localIntegralSpan p.val (fullLatticeRatBasis M hn) := by
  simp [localIntegralSpan,completedLattice_eq_span_basis]

 
theorem finite_matrix_rational_reduction {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (g : GL (Fin n) RationalFiniteAdeles) :
    ∃ c : GL (Fin n) ℚ, IntegralFiniteGL (GeneralLinearGroup.map rationalFiniteEmbedding c * g) := by
  obtain ⟨M,hM,hMp⟩ := finite_matrix_lattice_full_and_completed hn b g
  let m := fullLatticeRatBasis M hn
  let c := rowBasisChange m b
  refine ⟨c,?_,?_⟩
  · intro i j p
    have heq : localMatrixLattice m (GeneralLinearGroup.map rationalFiniteEmbedding c * g) p =
        localIntegralSpan p.val m := by
      rw [localMatrixLattice_basisChange,← hMp p,completedLattice_integralSpan_basis M hn]
    exact (integralFiniteAt_of_lattice_eq m _ p heq).1 i j
  · intro i j p
    have heq : localMatrixLattice m (GeneralLinearGroup.map rationalFiniteEmbedding c * g) p =
        localIntegralSpan p.val m := by
      rw [localMatrixLattice_basisChange,← hMp p,completedLattice_integralSpan_basis M hn]
    have hi := (integralFiniteAt_of_lattice_eq m _ p heq).2 i j
    rw [← finiteMatrixAt_inv] at hi
    exact hi

end PrimeDegreePackets.Adelic

end

end OAI
