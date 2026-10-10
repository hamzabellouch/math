import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicRepresentation

namespace OAI

noncomputable section
open scoped TensorProduct RestrictedProduct Topology Pointwise MatrixGroups
open Matrix Module Filter Set
namespace PrimeDegreePackets.Adelic

lemma rowRegular_tmul {n : ℕ} {K : Type*} [Field K] [NumberField K]
    {A : Type*} [CommRing A] [Algebra ℚ A] (b : Basis (Fin n) ℚ K) (r : A) (x : K) :
    rowRegular (b.baseChange A) (r ⊗ₜ[ℚ] x) =
      r • (rowRegular b x).map (algebraMap ℚ A) := by
  ext i j
  simp [rowRegular_apply,Basis.baseChange_apply,Algebra.TensorProduct.tmul_mul_tmul,
    Basis.baseChange_repr_tmul,Algebra.smul_def,mul_comm]

lemma rowRegular_tensor_map {n : ℕ} {K : Type*} [Field K] [NumberField K]
    {A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
    (b : Basis (Fin n) ℚ K) (f : A →ₐ[ℚ] B) (x : A ⊗[ℚ] K) :
    (rowRegular (b.baseChange A) x).map f =
      rowRegular (b.baseChange B) (Algebra.TensorProduct.map f (.id ℚ K) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    simp only [Algebra.TensorProduct.map_tmul,AlgHom.id_apply,rowRegular_tmul]
    ext i j
    change f (r * algebraMap ℚ A (rowRegular b a i j)) =
      f r * algebraMap ℚ B (rowRegular b a i j)
    rw [map_mul,AlgHom.commutes]
  | add x y hx hy =>
    ext i j
    simpa only [map_add,Matrix.map_apply,Matrix.add_apply] using
      congrArg₂ (· + ·) (congrFun (congrFun hx i) j) (congrFun (congrFun hy i) j)

lemma realTensorMap_coordinates {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (σ : OrderedEmbeddings n K)
    (x : RealAlgebra K) :
    (b.baseChange ℝ).equivFun x ᵥ* (realBasisGL hn b σ).val = realTensorMap σ x := by
  have H : (realBasisGL hn b σ).val.vecMulLinear.comp (b.baseChange ℝ).equivFun.toLinearMap =
      (realTensorMap σ).toLinearMap := by
    apply (b.baseChange ℝ).ext
    intro i
    ext j
    have hc : (b.baseChange ℝ).equivFun ((b.baseChange ℝ) i) = Pi.single i 1 := by
      ext k
      simpa only [Pi.single_apply,eq_comm] using (b.baseChange ℝ).equivFun_self i k
    change ((b.baseChange ℝ).equivFun ((b.baseChange ℝ) i) ᵥ* (realBasisGL hn b σ).val) j = _
    rw [hc,Matrix.single_one_vecMul]
    simp [Basis.baseChange_apply,realTensorMap_tmul]
  exact congrArg (fun f : RealAlgebra K →ₗ[ℝ] (Fin n → ℝ) => f x) H

lemma real_regular_diagonalization {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (σ : OrderedEmbeddings n K)
    (x : RealAlgebra K) :
    rowRegular (b.baseChange ℝ) x * (realBasisGL hn b σ).val =
      (realBasisGL hn b σ).val * Matrix.diagonal (realTensorMap σ x) := by
  ext i j
  have H := congrFun (realTensorMap_coordinates hn b σ (x * (b.baseChange ℝ) i)) j
  have H' : (rowRegular (b.baseChange ℝ) x * (realBasisGL hn b σ).val) i j =
      ((b.baseChange ℝ).equivFun (x * (b.baseChange ℝ) i) ᵥ*
        (realBasisGL hn b σ).val) j := by
    simp only [Matrix.mul_apply,Matrix.vecMul,dotProduct,rowRegular_apply]
    rfl
  rw [H',H,Matrix.mul_diagonal,map_mul]
  simp [Basis.baseChange_apply,mul_comm]

lemma rowRegular_finite_at {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) (x : FiniteTensorAdeles K) (p : Nat.Primes) :
    (rowRegular (b.baseChange RationalFiniteAdeles) x).map
        (RestrictedProduct.evalRingHom (fun p : Nat.Primes => Padic p.val) p) =
      rowRegular (b.baseChange (Padic p.val)) (finiteTensorMap K x p) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    rw [rowRegular_tmul,finiteTensorMap_tmul_apply]
    rw [Algebra.TensorProduct.includeRight_apply,TensorProduct.smul_tmul',smul_eq_mul,mul_one,
      rowRegular_tmul]
    ext i j
    change (RestrictedProduct.evalRingHom (fun p : Nat.Primes => Padic p.val) p)
      (r * algebraMap ℚ RationalFiniteAdeles (rowRegular b a i j)) =
        r p * algebraMap ℚ (Padic p.val) (rowRegular b a i j)
    rw [map_mul]
    rfl
  | add x y hx hy =>
    ext i j
    simpa only [map_add,Matrix.map_apply,Matrix.add_apply,RestrictedProduct.add_apply] using
      congrArg₂ (· + ·) (congrFun (congrFun hx i) j) (congrFun (congrFun hy i) j)

lemma rowRegular_real_component {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) (x : TensorAdeles K) :
    (rowRegular (b.baseChange RationalAdeles) x).map (RingHom.fst ℝ RationalFiniteAdeles) =
      rowRegular (b.baseChange ℝ) (tensorProdEquiv K x).1 := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    rw [rowRegular_tmul]
    change _ = rowRegular (b.baseChange ℝ) (r.1 ⊗ₜ[ℚ] a)
    rw [rowRegular_tmul]
    rfl
  | add x y hx hy =>
    ext i j
    simpa only [map_add,Matrix.map_apply,Matrix.add_apply,Prod.fst_add] using
      congrArg₂ (· + ·) (congrFun (congrFun hx i) j) (congrFun (congrFun hy i) j)

lemma rowRegular_finite_component {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) (x : TensorAdeles K) :
    (rowRegular (b.baseChange RationalAdeles) x).map (RingHom.snd ℝ RationalFiniteAdeles) =
      rowRegular (b.baseChange RationalFiniteAdeles) (tensorProdEquiv K x).2 := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    rw [rowRegular_tmul]
    change _ = rowRegular (b.baseChange RationalFiniteAdeles) (r.2 ⊗ₜ[ℚ] a)
    rw [rowRegular_tmul]
    rfl
  | add x y hx hy =>
    apply Matrix.ext
    intro i j
    simpa only [map_add,Matrix.map_apply,Matrix.add_apply,Prod.snd_add] using
      congrArg₂ (· + ·) (congrFun (congrFun hx i) j) (congrFun (congrFun hy i) j)

def finiteRegular {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) : (LocalFiniteAdeles K)ˣ →* GL (Fin n) RationalFiniteAdeles :=
  (rowRegularUnits (b.baseChange RationalFiniteAdeles)).comp
    (Units.map (finiteTensorEquiv K).symm.toMonoidHom)

lemma finiteRegular_at {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) (t : (LocalFiniteAdeles K)ˣ) (p : Nat.Primes) :
    finiteMatrixAt (finiteRegular b t) p = rowRegularUnits (b.baseChange (Padic p.val)) (localUnit K t p) := by
  apply Units.ext
  change (rowRegular (b.baseChange RationalFiniteAdeles) ((finiteTensorEquiv K).symm t.val)).map _ = _
  rw [rowRegular_finite_at]
  have he : finiteTensorMap K ((finiteTensorEquiv K).symm t.val) = t.val :=
    (finiteTensorEquiv K).apply_symm_apply t.val
  rw [he]
  rfl

lemma localMatrixLattice_finiteRegular {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) (t : (LocalFiniteAdeles K)ˣ)
    (g : GL (Fin n) RationalFiniteAdeles) (p : Nat.Primes) :
    (localMatrixLattice b (finiteRegular b t * g) p : Set (LocalAlgebra p.val K)) =
      (fun x => ((localUnit K t p)⁻¹ : (LocalAlgebra p.val K)ˣ).val * x) ''
        (localMatrixLattice b g p : Set (LocalAlgebra p.val K)) := by
  have hmem (x : LocalAlgebra p.val K) :
      x ∈ localMatrixLattice b (finiteRegular b t * g) p ↔
        (localUnit K t p).val * x ∈ localMatrixLattice b g p := by
    simp only [mem_localMatrixLattice_iff]
    have hmul : finiteMatrixAt (finiteRegular b t * g) p =
        finiteMatrixAt (finiteRegular b t) p * finiteMatrixAt g p := map_mul _ _ _
    rw [hmul,finiteRegular_at,Units.val_mul,← Matrix.vecMul_vecMul]
    change (∀ i, (((b.baseChange (Padic p.val)).repr x : Fin n → Padic p.val) ᵥ*
        rowRegular (b.baseChange (Padic p.val)) ((localUnit K t p).val) ᵥ* _) i ∈ _) ↔ _
    rw [vecMul_rowRegular]
    rfl
  ext x
  rw [SetLike.mem_coe,hmem]
  constructor
  · intro hx
    refine ⟨(localUnit K t p).val * x,hx,?_⟩
    change (localUnit K t p)⁻¹.val * ((localUnit K t p).val * x) = x
    rw [← mul_assoc,Units.inv_mul,one_mul]
  · rintro ⟨y,hy,rfl⟩
    change (localUnit K t p).val * ((localUnit K t p)⁻¹.val * y) ∈ _
    rw [← mul_assoc,Units.mul_inv,one_mul]
    exact hy

lemma matrixFullLattice_finiteRegular_locallyHomothetic {n : ℕ} {K : Type*}
    [Field K] [NumberField K] (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K)
    (t : (LocalFiniteAdeles K)ˣ) (g : GL (Fin n) RationalFiniteAdeles) :
    LocallyHomothetic (matrixFullLattice hn b g)
      (matrixFullLattice hn b (finiteRegular b t * g)) := by
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  refine ⟨(localUnit K t ⟨p,hp⟩)⁻¹,?_⟩
  rw [matrixFullLattice_completed hn b _ ⟨p,hp⟩,
    matrixFullLattice_completed hn b _ ⟨p,hp⟩]
  exact localMatrixLattice_finiteRegular b t g ⟨p,hp⟩

 
def assembleFiniteIdele {K : Type*} [Field K] [NumberField K]
    (c : (p : Nat.Primes) → (LocalAlgebra p.val K)ˣ)
    (hc : ∀ᶠ p : Nat.Primes in cofinite, c p = 1) : (LocalFiniteAdeles K)ˣ where
  val := ⟨fun p => (c p).val,by
    filter_upwards [hc] with p hp
    rw [hp,Units.val_one]
    exact (completedMaximalOrder (K := K) p.val).one_mem⟩
  inv := ⟨fun p => (c p)⁻¹.val,by
    filter_upwards [hc] with p hp
    rw [hp,inv_one,Units.val_one]
    exact (completedMaximalOrder (K := K) p.val).one_mem⟩
  val_inv := by ext p; exact (c p).val_inv
  inv_val := by ext p; exact (c p).inv_val

@[simp] lemma localUnit_assembleFiniteIdele {K : Type*} [Field K] [NumberField K]
    (c : (p : Nat.Primes) → (LocalAlgebra p.val K)ˣ)
    (hc : ∀ᶠ p : Nat.Primes in cofinite, c p = 1) (p : Nat.Primes) :
    localUnit K (assembleFiniteIdele c hc) p = c p := rfl

lemma completedLattice_eq_of_carrier_eq {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (h : M.carrier = N.carrier) (p : Nat.Primes) :
    completedLattice p.val M = completedLattice p.val N := by
  simp only [completedLattice,h]

lemma finiteIdele_realizes_local_homothety {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K)
    (g : GL (Fin n) RationalFiniteAdeles) (M : FullLattice n K)
    (hM : LocallyHomothetic (matrixFullLattice hn b g) M) :
    ∃ t : (LocalFiniteAdeles K)ˣ,
      (matrixFullLattice hn b (finiteRegular b t * g)).carrier = M.carrier := by
  classical
  obtain ⟨g',hg'⟩ := every_full_lattice_occurs hn b M
  have hcar : (matrixFullLattice hn b g').carrier = M.carrier := by
    apply SetLike.coe_injective
    rw [matrixFullLattice_carrier,hg']
  have hM' (p : Nat.Primes) : completedLattice p.val M = localMatrixLattice b g' p := by
    rw [← completedLattice_eq_of_carrier_eq _ _ hcar p,matrixFullLattice_completed]
  have he : ∀ᶠ p : Nat.Primes in cofinite,
      completedLattice p.val M = completedLattice p.val (matrixFullLattice hn b g) := by
    filter_upwards [localMatrixLattice_eventually_eq b g,localMatrixLattice_eventually_eq b g']
      with p hp hq
    rw [hM',matrixFullLattice_completed,hp,hq]
  let c : (p : Nat.Primes) → (LocalAlgebra p.val K)ˣ := fun p =>
    if completedLattice p.val M = completedLattice p.val (matrixFullLattice hn b g) then 1
    else (hM p.val p.property).choose
  have hc : ∀ᶠ p : Nat.Primes in cofinite, (c p)⁻¹ = 1 := by
    filter_upwards [he] with p hp
    simp [c,hp]
  have hcp (p : Nat.Primes) : (completedLattice p.val M : Set (LocalAlgebra p.val K)) =
      (fun x => (c p).val * x) '' (completedLattice p.val (matrixFullLattice hn b g) : Set _) := by
    dsimp only [c]
    split_ifs with hp
    · rw [hp]
      simp only [Units.val_one,one_mul]
      change _ = (fun x : LocalAlgebra p.val K => x) '' _
      ext x
      constructor
      · intro hx; exact ⟨x,hx,rfl⟩
      · rintro ⟨y,hy,rfl⟩; exact hy
    · exact (hM p.val p.property).choose_spec
  let t := assembleFiniteIdele (fun p => (c p)⁻¹) hc
  refine ⟨t,fullLattice_carrier_eq_of_completions_eq _ M hn ?_⟩
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  apply SetLike.coe_injective
  rw [matrixFullLattice_completed hn b _ ⟨p,hp⟩,
    localMatrixLattice_finiteRegular b t g ⟨p,hp⟩,hcp ⟨p,hp⟩,matrixFullLattice_completed hn b g ⟨p,hp⟩]
  rfl

end PrimeDegreePackets.Adelic

end

end OAI
