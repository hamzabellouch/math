import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicAmbient

namespace OAI

noncomputable section
open scoped TensorProduct RestrictedProduct Topology Pointwise MatrixGroups
open Matrix Module Filter Set
namespace PrimeDegreePackets.Adelic

 
def rowRegular {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Fintype ι] [DecidableEq ι] (b : Basis ι R S) : S →ₐ[R] Matrix ι ι R where
  toFun x := (Algebra.leftMulMatrix b x)ᵀ
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by simp
  map_mul' x y := by
    rw [← Matrix.transpose_mul,← map_mul,mul_comm]
  commutes' r := by
    rw [AlgHom.commutes]
    simp [Algebra.algebraMap_eq_smul_one]

lemma rowRegular_apply {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Fintype ι] [DecidableEq ι] (b : Basis ι R S) (x : S) (i j : ι) :
    rowRegular b x i j = b.repr (x * b i) j :=
  Algebra.leftMulMatrix_eq_repr_mul b x j i

lemma vecMul_rowRegular {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Fintype ι] [DecidableEq ι] (b : Basis ι R S) (x y : S) :
    (b.repr y : ι → R) ᵥ* rowRegular b x = b.repr (x * y) := by
  change (b.repr y : ι → R) ᵥ* (Algebra.leftMulMatrix b x)ᵀ = _
  rw [Matrix.vecMul_transpose,Algebra.leftMulMatrix_mulVec_repr]

 
def rowRegularUnits {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Fintype ι] [DecidableEq ι] (b : Basis ι R S) : Sˣ →* GL ι R :=
  Units.map (rowRegular b).toMonoidHom

lemma rowRegular_baseChange {n : ℕ} {K : Type*} [Field K] [NumberField K]
    {A : Type*} [CommRing A] [Algebra ℚ A] (b : Basis (Fin n) ℚ K) (x : K) :
    rowRegular (b.baseChange A) (Algebra.TensorProduct.includeRight x) =
      (rowRegular b x).map (algebraMap ℚ A) := by
  ext i j
  rw [rowRegular_apply]
  simp [Basis.baseChange_apply,Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul,Basis.baseChange_repr_tmul,rowRegular_apply,
    Algebra.smul_def]

 
def adelicRegular {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) : (TensorAdeles K)ˣ →* AdelicPGL n :=
  ((ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (RingHom.fst ℝ RationalFiniteAdeles))).prod
    (ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (RingHom.snd ℝ RationalFiniteAdeles)))).comp
    (rowRegularUnits (b.baseChange RationalAdeles))

def realBasisGL {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (σ : OrderedEmbeddings n K) : GL (Fin n) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero (embeddingMatrix (basisFullLattice b) σ)
    (embeddingMatrix_det_ne_zero (basisFullLattice b) σ hn)

@[simp] lemma realBasisGL_apply {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (σ : OrderedEmbeddings n K) (i j : Fin n) :
    (realBasisGL hn b σ).val i j = σ j (b i) := by
  simp [realBasisGL,embeddingMatrix]

 

def adelicPacketSupport {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (σ : OrderedEmbeddings n K)
    (g : GL (Fin n) RationalFiniteAdeles) : Set (AmbientQuotient n) :=
  Set.range (fun t : (TensorAdeles K)ˣ =>
    DoubleCoset.mk (rationalProjectiveGroup n) (finiteProjectiveIntegral n)
      (adelicRegular b t * (ProjGenLinGroup.mk (realBasisGL hn b σ),ProjGenLinGroup.mk g)))

 
def matrixFullLattice {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (g : GL (Fin n) RationalFiniteAdeles) :
    FullLattice n K := (finite_matrix_lattice_full_and_completed hn b g).choose

lemma matrixFullLattice_carrier {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (g : GL (Fin n) RationalFiniteAdeles) :
    ((matrixFullLattice hn b g).carrier : Set K) = finiteGlobalMatrixLattice b g :=
  (finite_matrix_lattice_full_and_completed hn b g).choose_spec.1

lemma matrixFullLattice_completed {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (g : GL (Fin n) RationalFiniteAdeles)
    (p : Nat.Primes) : completedLattice p.val (matrixFullLattice hn b g) = localMatrixLattice b g p :=
  (finite_matrix_lattice_full_and_completed hn b g).choose_spec.2 p

 
def ambientEquiv {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hodd : Odd n) (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) : X n ≃ AmbientQuotient n :=
  (ambient_quotient_equiv hodd hn b).choose

lemma ambientEquiv_mk {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hodd : Odd n) (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (h : G n) :
    ambientEquiv hodd hn b (Quotient.mk _ h) = realAmbientPoint h :=
  (ambient_quotient_equiv hodd hn b).choose_spec h

end PrimeDegreePackets.Adelic

end

end OAI
