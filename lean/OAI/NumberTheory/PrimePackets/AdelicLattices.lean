import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicCompactness

namespace OAI

noncomputable section
open scoped TensorProduct RestrictedProduct Topology Pointwise
open Matrix Module
namespace PrimeDegreePackets.Adelic

 
def finiteCoefficientRow {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) (x : K) : Fin n → RationalFiniteAdeles :=
  fun i => rationalFiniteEmbedding (b.repr x i)

 
def FiniteIntegralRow {n : ℕ} (v : Fin n → RationalFiniteAdeles) : Prop :=
  ∀ i p, v i p ∈ rationalLocalIntegers p

 
def finiteCompletedMatrixLattice {n : ℕ}
    (g : GL (Fin n) RationalFiniteAdeles) : Set (Fin n → RationalFiniteAdeles) :=
  {w | ∃ v, FiniteIntegralRow v ∧ v ᵥ* (↑g⁻¹ : Matrix (Fin n) (Fin n) RationalFiniteAdeles) = w}

 
def finiteGlobalMatrixLattice {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) (g : GL (Fin n) RationalFiniteAdeles) : Set K :=
  {x | finiteCoefficientRow b x ∈ finiteCompletedMatrixLattice g}

lemma mem_finiteCompletedMatrixLattice_iff {n : ℕ}
    (g : GL (Fin n) RationalFiniteAdeles) (w : Fin n → RationalFiniteAdeles) :
    w ∈ finiteCompletedMatrixLattice g ↔
      FiniteIntegralRow (w ᵥ* (g : Matrix (Fin n) (Fin n) RationalFiniteAdeles)) := by
  constructor
  · rintro ⟨v,hv,rfl⟩
    simpa only [Matrix.vecMul_vecMul,Units.inv_mul,Matrix.vecMul_one] using hv
  · intro hw
    refine ⟨w ᵥ* (g : Matrix (Fin n) (Fin n) RationalFiniteAdeles),hw,?_⟩
    simp only [Matrix.vecMul_vecMul,Units.mul_inv,Matrix.vecMul_one]

 
def rowBasisChange {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b m : Basis (Fin n) ℚ K) : GL (Fin n) ℚ where
  val := (m.toMatrix b)ᵀ
  inv := (b.toMatrix m)ᵀ
  val_inv := by rw [← Matrix.transpose_mul,b.toMatrix_mul_toMatrix_flip,Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul,m.toMatrix_mul_toMatrix_flip,Matrix.transpose_one]

lemma vecMul_rowBasisChange {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b m : Basis (Fin n) ℚ K) (x : K) :
    (b.repr x : Fin n → ℚ) ᵥ* (rowBasisChange b m : Matrix (Fin n) (Fin n) ℚ) = m.repr x := by
  change (b.repr x : Fin n → ℚ) ᵥ* (m.toMatrix b)ᵀ = _
  rw [Matrix.vecMul_transpose,Basis.toMatrix_mulVec_repr]

lemma finiteCoefficientRow_basisChange {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b m : Basis (Fin n) ℚ K) (x : K) :
    finiteCoefficientRow b x ᵥ*
      (GeneralLinearGroup.map rationalFiniteEmbedding (rowBasisChange b m) :
        Matrix (Fin n) (Fin n) RationalFiniteAdeles) = finiteCoefficientRow m x := by
  funext i
  change ((rationalFiniteEmbedding ∘ (b.repr x)) ᵥ*
    (rowBasisChange b m).val.map rationalFiniteEmbedding) i = rationalFiniteEmbedding (m.repr x i)
  rw [← RingHom.map_vecMul,vecMul_rowBasisChange]

lemma finiteIntegralRow_latticeBasis_iff {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (M : FullLattice n K) (x : K) :
    FiniteIntegralRow (finiteCoefficientRow (fullLatticeRatBasis M hn) x) ↔ x ∈ M.carrier := by
  constructor
  · intro hx
    have hint (i : Fin n) : ∃ a : ℤ, (a : ℚ) = (fullLatticeRatBasis M hn).repr x i := by
      apply rat_integral_of_padic_integral
      intro p hp
      exact hx i ⟨p,hp⟩
    choose a ha using hint
    have hsum : x = ∑ i, a i • (M.basis i : K) := by
      rw [← (fullLatticeRatBasis M hn).sum_repr x]
      apply Finset.sum_congr rfl
      intro i _
      rw [← ha i,fullLatticeRatBasis_apply]
      simp [Algebra.smul_def]
    rw [hsum]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (M.basis i).property)
  · intro hx i p
    obtain ⟨a,ha⟩ := fullLatticeRatBasis_repr_integral M hn hx i
    change (((fullLatticeRatBasis M hn).repr x i : ℚ) : Padic p.val) ∈ rationalLocalIntegers p
    rw [ha,Rat.cast_intCast]
    exact intCast_mem (rationalLocalIntegers p) a

 

theorem every_full_lattice_occurs {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (M : FullLattice n K) :
    ∃ g : GL (Fin n) RationalFiniteAdeles,
      finiteGlobalMatrixLattice b g = (M.carrier : Set K) := by
  refine ⟨GeneralLinearGroup.map rationalFiniteEmbedding
    (rowBasisChange b (fullLatticeRatBasis M hn)),?_⟩
  ext x
  change finiteCoefficientRow b x ∈ finiteCompletedMatrixLattice _ ↔ x ∈ M.carrier
  rw [mem_finiteCompletedMatrixLattice_iff,finiteCoefficientRow_basisChange,
    finiteIntegralRow_latticeBasis_iff]

end PrimeDegreePackets.Adelic

end

end OAI
