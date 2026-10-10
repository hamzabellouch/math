import Mathlib
import OAI.NumberTheory.PrimePackets.ZetaResidues

namespace OAI

noncomputable section
open scoped TensorProduct RestrictedProduct Topology Pointwise nonZeroDivisors NumberField
open Filter Set Module
namespace PrimeDegreePackets.Adelic

instance primeFact (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

def rationalLocalIntegers (p : Nat.Primes) : Subring (Padic p.val) :=
  (PadicInt.subring p.val)

instance rationalIntegersOpen : Fact (∀ p : Nat.Primes,
    IsOpen (rationalLocalIntegers p : Set (Padic p.val))) := ⟨fun p => by
  simpa [rationalLocalIntegers, PadicInt.subring, Subtype.range_coe_subtype] using
    (PadicInt.isOpenEmbedding_coe (p := p.val)).isOpen_range⟩

abbrev RationalFiniteAdeles :=
  Πʳ p : Nat.Primes, [Padic p.val, rationalLocalIntegers p]

lemma rational_eventually_integral (q : ℚ) :
    ∀ᶠ p : Nat.Primes in cofinite, (q : Padic p.val) ∈ rationalLocalIntegers p := by
  have hf : {p : Nat.Primes | p.val ∣ q.den}.Finite := by
    apply (q.den.divisors.finite_toSet.preimage Subtype.val_injective.injOn).subset
    intro p hp
    exact Nat.mem_divisors.mpr ⟨hp, q.den_ne_zero⟩
  have he : ∀ᶠ p : Nat.Primes in cofinite, ¬p.val ∣ q.den :=
    Filter.eventually_cofinite.mpr (by simpa only [not_not] using hf)
  filter_upwards [he] with p hp
  exact Padic.norm_rat_le_one hp

def rationalFiniteEmbedding : ℚ →+* RationalFiniteAdeles where
  toFun q := ⟨fun p => (q : Padic p.val), rational_eventually_integral q⟩
  map_one' := by ext; simp
  map_mul' x y := by
    ext p
    change ((x*y : ℚ) : Padic p.val) = (x : Padic p.val) * (y : Padic p.val)
    exact Rat.cast_mul x y
  map_zero' := by ext; simp
  map_add' x y := by
    ext p
    change ((x+y : ℚ) : Padic p.val) = (x : Padic p.val) + (y : Padic p.val)
    exact Rat.cast_add x y

instance : Algebra ℚ RationalFiniteAdeles := rationalFiniteEmbedding.toAlgebra

abbrev RationalAdeles := ℝ × RationalFiniteAdeles

 
abbrev TensorAdeles (K : Type*) [Field K] [NumberField K] := RationalAdeles ⊗[ℚ] K

instance (K : Type*) [Field K] [NumberField K] :
    TopologicalSpace (TensorAdeles K) := moduleTopology RationalAdeles (TensorAdeles K)
instance (K : Type*) [Field K] [NumberField K] :
    IsModuleTopology RationalAdeles (TensorAdeles K) := ⟨rfl⟩
instance (K : Type*) [Field K] [NumberField K] :
    IsTopologicalRing (TensorAdeles K) :=
  IsModuleTopology.isTopologicalRing RationalAdeles (TensorAdeles K)

 

def torusPrincipalScalarSubgroup (K : Type*) [Field K] [NumberField K] :
    Subgroup (TensorAdeles K)ˣ :=
  (Units.map (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] TensorAdeles K).toMonoidHom).range ⊔
  (Units.map (Algebra.TensorProduct.includeLeft : RationalAdeles →ₐ[ℚ] TensorAdeles K).toMonoidHom).range

abbrev TorusQuotient (K : Type*) [Field K] [NumberField K] :=
  (TensorAdeles K)ˣ ⧸ torusPrincipalScalarSubgroup K

instance tensorUnitsCommGroup (K : Type*) [Field K] [NumberField K] :
    CommGroup (TensorAdeles K)ˣ := @Units.instCommGroupUnits (TensorAdeles K) inferInstance

 
abbrev LocalFiniteAdeles (K : Type*) [Field K] [NumberField K] :=
  Πʳ p : Nat.Primes, [LocalAlgebra p.val K, completedMaximalOrder (K := K) p.val]

instance maximalOrdersOpen (K : Type*) [Field K] [NumberField K] :
    Fact (∀ p : Nat.Primes,
      IsOpen (completedMaximalOrder (K := K) p.val : Set (LocalAlgebra p.val K))) := ⟨fun p =>
  completedLattice_open (fractionalIdealFullLattice (K := K) rfl 1) rfl p.val⟩

 
def integerRatBasis (K : Type*) [Field K] [NumberField K] :
    Basis (Fin (finrank ℚ K)) ℚ K :=
  fullLatticeRatBasis (fractionalIdealFullLattice (K := K) rfl 1) rfl

lemma localIntegralSpan_integerRatBasis (K : Type*) [Field K] [NumberField K]
    (p : Nat.Primes) :
    localIntegralSpan p.val (integerRatBasis K) =
      (completedMaximalOrder (K := K) p.val).toSubmodule := by
  simpa [localIntegralSpan, integerRatBasis, completedLattice_eq_span_basis] using
    (completedLattice_fractionalIdealFullLattice (K := K) rfl 1 p.val)

lemma field_eventually_integral (K : Type*) [Field K] [NumberField K] (a : K) :
    ∀ᶠ p : Nat.Primes in cofinite,
      (Algebra.TensorProduct.includeRight a : LocalAlgebra p.val K) ∈
        completedMaximalOrder (K := K) p.val := by
  have he : ∀ᶠ p : Nat.Primes in cofinite,
      ∀ i, (((integerRatBasis K).repr a i : ℚ) : Padic p.val) ∈ rationalLocalIntegers p :=
    Filter.eventually_all.mpr (fun i => rational_eventually_integral ((integerRatBasis K).repr a i))
  filter_upwards [he] with p hp
  change (Algebra.TensorProduct.includeRight a : LocalAlgebra p.val K) ∈
      (completedMaximalOrder (K := K) p.val).toSubmodule
  rw [← localIntegralSpan_integerRatBasis K p, localIntegralSpan_mem]
  intro i
  change ‖((integerRatBasis K).baseChange (Padic p.val)).repr (1 ⊗ₜ[ℚ] a) i‖ ≤ 1
  have hi : ‖(((integerRatBasis K).repr a i : ℚ) : Padic p.val)‖ ≤ 1 := hp i
  rw [Basis.baseChange_repr_tmul]
  simpa only [Rat.smul_def, mul_one] using hi

 
def localFiniteEmbedding (K : Type*) [Field K] [NumberField K] :
    K →+* LocalFiniteAdeles K where
  toFun a := ⟨fun p => Algebra.TensorProduct.includeRight a, field_eventually_integral K a⟩
  map_one' := by ext p; exact map_one Algebra.TensorProduct.includeRight
  map_mul' a b := by ext p; exact map_mul Algebra.TensorProduct.includeRight a b
  map_zero' := by ext; simp
  map_add' a b := by ext p; exact map_add Algebra.TensorProduct.includeRight a b

instance (K : Type*) [Field K] [NumberField K] : Algebra K (LocalFiniteAdeles K) :=
  (localFiniteEmbedding K).toAlgebra
instance (K : Type*) [Field K] [NumberField K] : Algebra ℚ (LocalFiniteAdeles K) :=
  Algebra.compHom _ (algebraMap ℚ K)
instance (K : Type*) [Field K] [NumberField K] :
    IsScalarTower ℚ K (LocalFiniteAdeles K) := IsScalarTower.of_algebraMap_eq' rfl

@[simp] lemma localFiniteEmbedding_apply (K : Type*) [Field K] [NumberField K]
    (a : K) (p : Nat.Primes) : (localFiniteEmbedding K a) p =
      (Algebra.TensorProduct.includeRight a : LocalAlgebra p.val K) := rfl

lemma integerRatBasis_coordinate_mem (K : Type*) [Field K] [NumberField K]
    (p : Nat.Primes) {x : LocalAlgebra p.val K}
    (hx : x ∈ completedMaximalOrder (K := K) p.val) (i : Fin (finrank ℚ K)) :
    localAlgebraCoordinates p.val (integerRatBasis K) x i ∈ rationalLocalIntegers p := by
  change ‖localAlgebraCoordinates p.val (integerRatBasis K) x i‖ ≤ 1
  apply (localIntegralSpan_mem p.val (integerRatBasis K) x).mp _ i
  rwa [localIntegralSpan_integerRatBasis]

 
def finiteCoordinates (K : Type*) [Field K] [NumberField K]
    (x : LocalFiniteAdeles K) (i : Fin (finrank ℚ K)) : RationalFiniteAdeles :=
  ⟨fun p => localAlgebraCoordinates p.val (integerRatBasis K) (x p) i,
    x.property.mono (fun p hp => integerRatBasis_coordinate_mem K p hp i)⟩

@[simp] lemma finiteCoordinates_apply (K : Type*) [Field K] [NumberField K]
    (x : LocalFiniteAdeles K) (i : Fin (finrank ℚ K)) (p : Nat.Primes) :
    finiteCoordinates K x i p = localAlgebraCoordinates p.val (integerRatBasis K) (x p) i := rfl

lemma continuous_finiteCoordinates (K : Type*) [Field K] [NumberField K]
    (i : Fin (finrank ℚ K)) : Continuous (fun x => finiteCoordinates K x i) := by
  exact RestrictedProduct.mapAlong_continuous
    (fun p : Nat.Primes => LocalAlgebra p.val K) (fun p : Nat.Primes => Padic p.val)
    id tendsto_id (fun p x => localAlgebraCoordinates p.val (integerRatBasis K) x i)
    (Filter.Eventually.of_forall (fun p x hx => integerRatBasis_coordinate_mem K p hx i))
    (fun p => (continuous_apply i).comp (localAlgebraCoordinates p.val (integerRatBasis K)).continuous)

def fromFiniteCoordinates (K : Type*) [Field K] [NumberField K]
    (c : Fin (finrank ℚ K) → RationalFiniteAdeles) : LocalFiniteAdeles K :=
  ⟨fun p => (localAlgebraCoordinates p.val (integerRatBasis K)).symm (fun i => c i p), by
    have he : ∀ᶠ p : Nat.Primes in cofinite, ∀ i, c i p ∈ rationalLocalIntegers p :=
      Filter.eventually_all.mpr (fun i => (c i).property)
    filter_upwards [he] with p hp
    change (localAlgebraCoordinates p.val (integerRatBasis K)).symm (fun i => c i p) ∈
      (completedMaximalOrder (K := K) p.val).toSubmodule
    rw [← localIntegralSpan_integerRatBasis K p, localIntegralSpan_mem]
    intro i
    change ‖(localAlgebraCoordinates p.val (integerRatBasis K))
      ((localAlgebraCoordinates p.val (integerRatBasis K)).symm (fun i => c i p)) i‖ ≤ 1
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hp i⟩

@[simp] lemma finiteCoordinates_fromFiniteCoordinates (K : Type*) [Field K] [NumberField K]
    (c : Fin (finrank ℚ K) → RationalFiniteAdeles) :
    finiteCoordinates K (fromFiniteCoordinates K c) = c := by
  funext i
  ext p
  exact congrFun ((localAlgebraCoordinates p.val (integerRatBasis K)).apply_symm_apply _) i

@[simp] lemma fromFiniteCoordinates_finiteCoordinates (K : Type*) [Field K] [NumberField K]
    (x : LocalFiniteAdeles K) : fromFiniteCoordinates K (finiteCoordinates K x) = x := by
  ext p
  exact (localAlgebraCoordinates p.val (integerRatBasis K)).symm_apply_apply (x p)

 
def finiteScalarEmbedding (K : Type*) [Field K] [NumberField K] :
    RationalFiniteAdeles →+* LocalFiniteAdeles K where
  toFun x := ⟨fun p => algebraMap (Padic p.val) (LocalAlgebra p.val K) (x p), by
    filter_upwards [x.property] with p hp
    let z : PadicInt p.val := ⟨x p, hp⟩
    exact (completedMaximalOrder (K := K) p.val).algebraMap_mem z⟩
  map_one' := by ext p; exact map_one (algebraMap (Padic p.val) (LocalAlgebra p.val K))
  map_mul' x y := by ext p; exact map_mul (algebraMap (Padic p.val) (LocalAlgebra p.val K)) (x p) (y p)
  map_zero' := by ext p; exact map_zero (algebraMap (Padic p.val) (LocalAlgebra p.val K))
  map_add' x y := by ext p; exact map_add (algebraMap (Padic p.val) (LocalAlgebra p.val K)) (x p) (y p)

@[simp] lemma finiteScalarEmbedding_apply (K : Type*) [Field K] [NumberField K]
    (x : RationalFiniteAdeles) (p : Nat.Primes) :
    finiteScalarEmbedding K x p = algebraMap (Padic p.val) (LocalAlgebra p.val K) (x p) := rfl

def finiteScalarAlgHom (K : Type*) [Field K] [NumberField K] :
    RationalFiniteAdeles →ₐ[ℚ] LocalFiniteAdeles K where
  __ := finiteScalarEmbedding K
  commutes' q := by
    ext p
    change algebraMap (Padic p.val) (LocalAlgebra p.val K) (q : Padic p.val) =
      Algebra.TensorProduct.includeRight (algebraMap ℚ K q)
    exact (Algebra.TensorProduct.includeLeft : Padic p.val →ₐ[ℚ] LocalAlgebra p.val K).commutes q |>.trans
      ((Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p.val K).commutes q).symm

instance (K : Type*) [Field K] [NumberField K] :
    Algebra RationalFiniteAdeles (LocalFiniteAdeles K) :=
  (finiteScalarEmbedding K).toAlgebra

instance (K : Type*) [Field K] [NumberField K] :
    IsScalarTower ℚ RationalFiniteAdeles (LocalFiniteAdeles K) :=
  IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro q
    exact ((finiteScalarAlgHom K).commutes q).symm)

@[simp] lemma finite_smul_apply (K : Type*) [Field K] [NumberField K]
    (c : RationalFiniteAdeles) (x : LocalFiniteAdeles K) (p : Nat.Primes) :
    (c • x) p = c p • x p := by
  simp only [Algebra.smul_def]
  rfl

def finiteCoordinatesLinear (K : Type*) [Field K] [NumberField K] :
    LocalFiniteAdeles K →ₗ[RationalFiniteAdeles]
      (Fin (finrank ℚ K) → RationalFiniteAdeles) where
  toFun := finiteCoordinates K
  map_add' x y := by
    funext i
    ext p
    change localAlgebraCoordinates p.val (integerRatBasis K) (x p + y p) i = _
    simp
  map_smul' c x := by
    funext i
    ext p
    change localAlgebraCoordinates p.val (integerRatBasis K) ((c • x) p) i =
      c p * localAlgebraCoordinates p.val (integerRatBasis K) (x p) i
    rw [finite_smul_apply, map_smul]
    rfl

def finiteCoordinatesEquiv (K : Type*) [Field K] [NumberField K] :
    LocalFiniteAdeles K ≃ₗ[RationalFiniteAdeles]
      (Fin (finrank ℚ K) → RationalFiniteAdeles) :=
  LinearEquiv.ofBijective (finiteCoordinatesLinear K) ⟨by
    intro x y h
    calc
      x = fromFiniteCoordinates K (finiteCoordinates K x) :=
        (fromFiniteCoordinates_finiteCoordinates K x).symm
      _ = fromFiniteCoordinates K (finiteCoordinates K y) := congrArg (fromFiniteCoordinates K) h
      _ = y := fromFiniteCoordinates_finiteCoordinates K y,
    fun c => ⟨fromFiniteCoordinates K c, finiteCoordinates_fromFiniteCoordinates K c⟩⟩

abbrev FiniteTensorAdeles (K : Type*) [Field K] [NumberField K] :=
  RationalFiniteAdeles ⊗[ℚ] K

def finiteTensorMap (K : Type*) [Field K] [NumberField K] :
    FiniteTensorAdeles K →ₐ[RationalFiniteAdeles] LocalFiniteAdeles K :=
  AlgHom.liftEquiv ℚ RationalFiniteAdeles K (LocalFiniteAdeles K)
    (IsScalarTower.toAlgHom ℚ K (LocalFiniteAdeles K))

lemma finiteTensorMap_tmul_apply (K : Type*) [Field K] [NumberField K]
    (x : RationalFiniteAdeles) (a : K) (p : Nat.Primes) :
    finiteTensorMap K (x ⊗ₜ[ℚ] a) p =
      x p • (Algebra.TensorProduct.includeRight a : LocalAlgebra p.val K) := by
  change (x • localFiniteEmbedding K a) p = _
  rw [finite_smul_apply, localFiniteEmbedding_apply]

lemma finiteCoordinates_finiteTensorMap (K : Type*) [Field K] [NumberField K]
    (x : FiniteTensorAdeles K) :
    finiteCoordinates K (finiteTensorMap K x) =
      ((integerRatBasis K).baseChange RationalFiniteAdeles).equivFun x := by
  induction x using TensorProduct.inductionOn with
  | tmul x a =>
    funext i
    ext p
    rw [finiteCoordinates_apply, finiteTensorMap_tmul_apply]
    change ((integerRatBasis K).baseChange (Padic p.val)).repr
      (x p • (1 ⊗ₜ[ℚ] a)) i =
      (((integerRatBasis K).baseChange RationalFiniteAdeles).repr (x ⊗ₜ[ℚ] a) i) p
    simp only [map_smul, Finsupp.smul_apply, Basis.baseChange_repr_tmul]
    change x p * (((integerRatBasis K).repr a i) • (1 : Padic p.val)) =
      (algebraMap ℚ RationalFiniteAdeles ((integerRatBasis K).repr a i) * x) p
    simp only [Rat.smul_def, mul_one]
    change x p * (((integerRatBasis K).repr a i : ℚ) : Padic p.val) =
      (((integerRatBasis K).repr a i : ℚ) : Padic p.val) * x p
    exact mul_comm _ _
  | add x y hx hy =>
    change finiteCoordinatesLinear K (finiteTensorMap K (x + y)) = _
    simp only [map_add]
    exact congrArg₂ (· + ·) hx hy

def finiteTensorEquiv (K : Type*) [Field K] [NumberField K] :
    FiniteTensorAdeles K ≃ₐ[RationalFiniteAdeles] LocalFiniteAdeles K :=
  AlgEquiv.ofBijective (finiteTensorMap K) ⟨by
    intro x y h
    apply ((integerRatBasis K).baseChange RationalFiniteAdeles).equivFun.injective
    rw [← finiteCoordinates_finiteTensorMap, ← finiteCoordinates_finiteTensorMap, h], by
    intro y
    let x := ((integerRatBasis K).baseChange RationalFiniteAdeles).equivFun.symm
      (finiteCoordinates K y)
    refine ⟨x, ?_⟩
    apply (finiteCoordinatesEquiv K).injective
    change finiteCoordinates K (finiteTensorMap K x) = finiteCoordinates K y
    rw [finiteCoordinates_finiteTensorMap]
    exact LinearEquiv.apply_symm_apply _ _⟩

 
abbrev RealAlgebra (K : Type*) [Field K] [NumberField K] := ℝ ⊗[ℚ] K
instance (K : Type*) [Field K] [NumberField K] : TopologicalSpace (RealAlgebra K) :=
  moduleTopology ℝ (RealAlgebra K)
instance (K : Type*) [Field K] [NumberField K] : IsModuleTopology ℝ (RealAlgebra K) := ⟨rfl⟩
instance (K : Type*) [Field K] [NumberField K] : IsTopologicalRing (RealAlgebra K) :=
  IsModuleTopology.isTopologicalRing ℝ (RealAlgebra K)
instance (K : Type*) [Field K] [NumberField K] : ContinuousSMul ℝ (RealAlgebra K) :=
  IsModuleTopology.toContinuousSMul ℝ (RealAlgebra K)
instance (K : Type*) [Field K] [NumberField K] :
    ContinuousSMul RationalAdeles (TensorAdeles K) :=
  IsModuleTopology.toContinuousSMul RationalAdeles (TensorAdeles K)

abbrev ModelAdeles (K : Type*) [Field K] [NumberField K] :=
  RealAlgebra K × LocalFiniteAdeles K

def tensorProdEquiv (K : Type*) [Field K] [NumberField K] :
    TensorAdeles K ≃ₐ[ℚ] RealAlgebra K × FiniteTensorAdeles K :=
  (Algebra.TensorProduct.comm ℚ RationalAdeles K).trans
    ((Algebra.TensorProduct.prodRight ℚ ℚ K ℝ RationalFiniteAdeles).trans
      (AlgEquiv.prodCongr (Algebra.TensorProduct.comm ℚ K ℝ)
        (Algebra.TensorProduct.comm ℚ K RationalFiniteAdeles)))

def tensorModelEquiv (K : Type*) [Field K] [NumberField K] :
    TensorAdeles K ≃ₐ[ℚ] ModelAdeles K :=
  (tensorProdEquiv K).trans
    (AlgEquiv.prodCongr (AlgEquiv.refl : RealAlgebra K ≃ₐ[ℚ] RealAlgebra K)
      ((finiteTensorEquiv K).restrictScalars ℚ))

@[simp] lemma tensorModelEquiv_tmul (K : Type*) [Field K] [NumberField K]
    (x : RationalAdeles) (a : K) :
    tensorModelEquiv K (x ⊗ₜ[ℚ] a) =
      (x.1 ⊗ₜ[ℚ] a, finiteTensorMap K (x.2 ⊗ₜ[ℚ] a)) := rfl

def modelCoordinates (K : Type*) [Field K] [NumberField K]
    (x : ModelAdeles K) : Fin (finrank ℚ K) → RationalAdeles := fun i =>
  (((integerRatBasis K).baseChange ℝ).equivFun x.1 i,
    finiteCoordinates K x.2 i)

lemma modelCoordinates_tensorModelEquiv (K : Type*) [Field K] [NumberField K]
    (x : TensorAdeles K) :
    modelCoordinates K (tensorModelEquiv K x) =
      ((integerRatBasis K).baseChange RationalAdeles).equivFun x := by
  induction x using TensorProduct.inductionOn with
  | tmul x a =>
    rw [tensorModelEquiv_tmul]
    funext i
    apply Prod.ext
    · change ((integerRatBasis K).baseChange ℝ).repr (x.1 ⊗ₜ[ℚ] a) i =
        (((integerRatBasis K).baseChange RationalAdeles).repr (x ⊗ₜ[ℚ] a) i).1
      rw [Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul]
      rfl
    · change finiteCoordinates K (finiteTensorMap K (x.2 ⊗ₜ[ℚ] a)) i = _
      rw [finiteCoordinates_finiteTensorMap]
      change ((integerRatBasis K).baseChange RationalFiniteAdeles).repr (x.2 ⊗ₜ[ℚ] a) i =
        (((integerRatBasis K).baseChange RationalAdeles).repr (x ⊗ₜ[ℚ] a) i).2
      rw [Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul]
      rfl
  | add x y hx hy =>
    rw [map_add, map_add]
    calc
      modelCoordinates K (tensorModelEquiv K x + tensorModelEquiv K y) =
          modelCoordinates K (tensorModelEquiv K x) + modelCoordinates K (tensorModelEquiv K y) := by
        funext i
        apply Prod.ext
        · exact congrFun (map_add ((integerRatBasis K).baseChange ℝ).equivFun _ _) i
        · exact congrFun (map_add (finiteCoordinatesLinear K) _ _) i
      _ = _ := congrArg₂ (· + ·) hx hy

lemma continuous_modelCoordinates (K : Type*) [Field K] [NumberField K] :
    Continuous (modelCoordinates K) := by
  apply continuous_pi
  intro i
  exact (((continuous_apply i).comp (IsModuleTopology.continuous_of_linearMap
    ((integerRatBasis K).baseChange ℝ).equivFun.toLinearMap)).comp continuous_fst).prodMk
    ((continuous_finiteCoordinates K i).comp continuous_snd)

lemma tensorModelEquiv_symm_eq_coordinates (K : Type*) [Field K] [NumberField K]
    (x : ModelAdeles K) :
    (tensorModelEquiv K).symm x =
      ((integerRatBasis K).baseChange RationalAdeles).equivFun.symm (modelCoordinates K x) := by
  apply ((integerRatBasis K).baseChange RationalAdeles).equivFun.injective
  rw [LinearEquiv.apply_symm_apply, ← modelCoordinates_tensorModelEquiv,
    AlgEquiv.apply_symm_apply]

lemma continuous_tensorModelEquiv_symm (K : Type*) [Field K] [NumberField K] :
    Continuous (tensorModelEquiv K).symm := by
  have he : ⇑(tensorModelEquiv K).symm =
      ((integerRatBasis K).baseChange RationalAdeles).equivFun.symm ∘ modelCoordinates K :=
    funext (tensorModelEquiv_symm_eq_coordinates K)
  rw [he]
  exact (IsModuleTopology.continuous_of_linearMap
    ((integerRatBasis K).baseChange RationalAdeles).equivFun.symm.toLinearMap).comp
      (continuous_modelCoordinates K)

 
lemma local_vector_denominator (K : Type*) [Field K] [NumberField K]
    (p : Nat.Primes) (x : LocalAlgebra p.val K) :
    ∃ k : ℕ, (p.val : PadicInt p.val)^k • x ∈ completedMaximalOrder (K := K) p.val := by
  obtain ⟨k, hk⟩ := localModule_denominator p.val
    (Submodule.span (PadicInt p.val) {x}) (Submodule.fg_span_singleton x)
  exact ⟨k, hk x (Submodule.subset_span (Set.mem_singleton x))⟩

 
lemma local_principal_clear_denominators (K : Type*) [Field K] [NumberField K]
    (p : Nat.Primes) (z : (LocalAlgebra p.val K)ˣ) :
    ∃ c : (Padic p.val)ˣ, ∃ m : ℕ,
      (c.val • z.val) • (completedMaximalOrder (K := K) p.val).toSubmodule ≤
        (completedMaximalOrder (K := K) p.val).toSubmodule ∧
      ∀ y ∈ (completedMaximalOrder (K := K) p.val).toSubmodule,
        (p.val : PadicInt p.val)^m • y ∈
          (c.val • z.val) • (completedMaximalOrder (K := K) p.val).toSubmodule := by
  let R := completedMaximalOrder (K := K) p.val
  obtain ⟨k,hk⟩ := local_vector_denominator K p z.val
  let c : (Padic p.val)ˣ := Units.mk0 ((p.val : Padic p.val)^k)
    (pow_ne_zero _ (Nat.cast_ne_zero.mpr p.property.ne_zero))
  let w : (LocalAlgebra p.val K)ˣ :=
    Units.map (algebraMap (Padic p.val) (LocalAlgebra p.val K)).toMonoidHom c * z
  have hw : (w : LocalAlgebra p.val K) = c.val • z.val := by
    change (algebraMap (Padic p.val) (LocalAlgebra p.val K) c.val) * z.val = _
    rw [Algebra.smul_def]
  have hwR : (w : LocalAlgebra p.val K) ∈ R := by
    rw [hw]
    change (p.val : Padic p.val)^k • (z : LocalAlgebra p.val K) ∈ R
    simpa only [← IsScalarTower.algebraMap_smul (Padic p.val), map_pow,
      map_natCast] using hk
  obtain ⟨m,hm⟩ := local_vector_denominator K p (↑(w⁻¹) : LocalAlgebra p.val K)
  refine ⟨c,m,?_,?_⟩
  · rintro x hx
    obtain ⟨y,hy,rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    change (c.val • z.val) * y ∈ R
    rw [← hw]
    exact R.mul_mem hwR hy
  · intro y hy
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
      ⟨((p.val : PadicInt p.val)^m • (↑(w⁻¹) : LocalAlgebra p.val K)) * y,
        R.mul_mem hm hy, ?_⟩
    change (c.val • z.val) * (((p.val : PadicInt p.val)^m •
      (↑(w⁻¹) : LocalAlgebra p.val K)) * y) = _
    rw [← hw, ← mul_assoc, mul_smul_comm, Units.mul_inv, smul_mul_assoc, one_mul]

 
def localUnit (K : Type*) [Field K] [NumberField K]
    (z : (LocalFiniteAdeles K)ˣ) (p : Nat.Primes) : (LocalAlgebra p.val K)ˣ :=
  Units.map (RestrictedProduct.evalMonoidHom (fun p : Nat.Primes => LocalAlgebra p.val K) p) z

@[simp] lemma localUnit_val (K : Type*) [Field K] [NumberField K]
    (z : (LocalFiniteAdeles K)ˣ) (p : Nat.Primes) :
    (localUnit K z p : LocalAlgebra p.val K) = (z : LocalFiniteAdeles K) p := rfl

lemma localUnit_eventually_integral (K : Type*) [Field K] [NumberField K]
    (z : (LocalFiniteAdeles K)ˣ) : ∀ᶠ p : Nat.Primes in cofinite,
      (localUnit K z p : LocalAlgebra p.val K) ∈ completedMaximalOrder (K := K) p.val ∧
      ((localUnit K z p)⁻¹ : (LocalAlgebra p.val K)ˣ).val ∈
        completedMaximalOrder (K := K) p.val :=
  z.val.property.and z.inv.property

lemma local_unit_smul_order (K : Type*) [Field K] [NumberField K]
    (p : Nat.Primes) (z : (LocalAlgebra p.val K)ˣ)
    (hz : z.val ∈ completedMaximalOrder (K := K) p.val ∧
      (z⁻¹).val ∈ completedMaximalOrder (K := K) p.val) :
    (z : LocalAlgebra p.val K) • (completedMaximalOrder (K := K) p.val).toSubmodule =
      (completedMaximalOrder (K := K) p.val).toSubmodule := by
  let v : (completedMaximalOrder (K := K) p.val)ˣ :=
    { val := ⟨z.val,hz.1⟩
      inv := ⟨(z⁻¹).val,hz.2⟩
      val_inv := Subtype.ext z.val_inv
      inv_val := Subtype.ext z.inv_val }
  exact completedMaximalOrder_unit_smul p.val v

 

theorem finite_idele_ideal_patch (K : Type*) [Field K] [NumberField K]
    (z : (LocalFiniteAdeles K)ˣ) :
    ∃ s : RationalFiniteAdelesˣ, ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      ∀ p : Nat.Primes, completedFractionalIdeal p.val (I : FractionalIdeal (𝓞 K)⁰ K) =
        (((s : RationalFiniteAdeles) p) • ((z : LocalFiniteAdeles K) p)) •
          (completedMaximalOrder (K := K) p.val).toSubmodule := by
  classical
  let S : Set Nat.Primes := {p | ¬((localUnit K z p).val ∈ completedMaximalOrder (K := K) p.val ∧
    ((localUnit K z p)⁻¹).val ∈ completedMaximalOrder (K := K) p.val)}
  have hS : S.Finite := Filter.eventually_cofinite.mp (localUnit_eventually_integral K z)
  let : Fintype S := hS.fintype
  choose c m hle hpow using (fun p : S => local_principal_clear_denominators K p.val (localUnit K z p.val))
  let cs (p : Nat.Primes) : (Padic p.val)ˣ := if hp : p ∈ S then c ⟨p,hp⟩ else 1
  have hcs : ∀ᶠ p : Nat.Primes in cofinite,
      cs p ∈ (Submonoid.ofClass (rationalLocalIntegers p)).units := by
    filter_upwards [show ∀ᶠ p : Nat.Primes in cofinite, p ∉ S from
      Filter.eventually_cofinite.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using hS)] with p hp
    simp only [cs, dite_eq_right hp]
    exact one_mem _
  let s : RationalFiniteAdelesˣ := RestrictedProduct.mkUnit cs hcs
  let M := fractionalIdealFullLattice (K := K) rfl (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  let N (p : S) : Submodule (PadicInt p.val.val) (LocalAlgebra p.val.val K) :=
    ((c p).val • (localUnit K z p.val).val) •
      (completedMaximalOrder (K := K) p.val.val).toSubmodule
  have hinj : Function.Injective (fun p : S => p.val.val) := by
    intro p q hpq
    exact Subtype.ext (Subtype.ext hpq)
  obtain ⟨L,_hLM,hL,hLoff⟩ := patch_fullLattice_completions M rfl
    (fun p : S => p.val.val) hinj m N hle hpow
  refine ⟨s,saturationIdealUnit L,?_⟩
  intro p
  change completedFractionalIdeal p.val (saturationFractionalIdeal L) = _
  rw [completed_saturation]
  by_cases hp : p ∈ S
  · rw [hL ⟨p,hp⟩]
    have hs : ((s : RationalFiniteAdeles) p) = (c ⟨p,hp⟩).val := by
      change (cs p).val = _
      simp only [cs, dite_eq_left hp]
    rw [hs]
    change (completedMaximalOrder (K := K) p.val).toSubmodule *
      (((c ⟨p,hp⟩).val • (localUnit K z p).val) •
        (completedMaximalOrder (K := K) p.val).toSubmodule) = _
    rw [mul_smul_comm, (completedMaximalOrder (K := K) p.val).isIdempotentElem_toSubmodule.eq]
    rfl
  · have hnot : p.val ∉ Set.range (fun q : S => q.val.val) := by
      rintro ⟨q,hq⟩
      exact hp ((show q.val = p from Subtype.ext hq) ▸ q.property)
    rw [hLoff p.val p.property hnot]
    have hs : ((s : RationalFiniteAdeles) p) = 1 := by
      change (cs p).val = _
      simp only [cs, dite_eq_right hp, Units.val_one]
    rw [hs, one_smul]
    change (completedMaximalOrder (K := K) p.val).toSubmodule *
      (completedMaximalOrder (K := K) p.val).toSubmodule = _
    rw [(completedMaximalOrder (K := K) p.val).isIdempotentElem_toSubmodule.eq]
    exact (local_unit_smul_order K p (localUnit K z p) (not_not.mp hp)).symm

 
abbrev IntegralFiniteUnits (K : Type*) [Field K] [NumberField K] :=
  (p : Nat.Primes) → (completedMaximalOrder (K := K) p.val)ˣ

def integralFiniteUnit (K : Type*) [Field K] [NumberField K]
    (u : IntegralFiniteUnits K) : (LocalFiniteAdeles K)ˣ where
  val := RestrictedProduct.structureMap _ _ cofinite (fun p => (u p).val)
  inv := RestrictedProduct.structureMap _ _ cofinite (fun p => (u p).inv)
  val_inv := by ext p; exact congrArg Subtype.val (u p).val_inv
  inv_val := by ext p; exact congrArg Subtype.val (u p).inv_val

@[simp] lemma integralFiniteUnit_apply (K : Type*) [Field K] [NumberField K]
    (u : IntegralFiniteUnits K) (p : Nat.Primes) :
    (integralFiniteUnit K u).val p = ((u p).val : LocalAlgebra p.val K) := rfl

lemma continuous_integralFiniteUnit (K : Type*) [Field K] [NumberField K] :
    Continuous (integralFiniteUnit K) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact RestrictedProduct.isEmbedding_structureMap.continuous.comp
      (continuous_pi fun p => Units.continuous_val.comp (continuous_apply p))
  · exact RestrictedProduct.isEmbedding_structureMap.continuous.comp
      (continuous_pi fun p => Units.continuous_coe_inv.comp (continuous_apply p))

abbrev finitePrincipal (K : Type*) [Field K] [NumberField K] :=
  Units.map (localFiniteEmbedding K).toMonoidHom
abbrev finiteScalar (K : Type*) [Field K] [NumberField K] :=
  Units.map (finiteScalarEmbedding K).toMonoidHom

 

theorem finite_idele_finite_representatives (K : Type*) [Field K] [NumberField K] :
    ∃ C : Set (LocalFiniteAdeles K)ˣ, C.Finite ∧
      ∀ z : (LocalFiniteAdeles K)ˣ, ∃ c ∈ C, ∃ a : Kˣ,
        ∃ s : RationalFiniteAdelesˣ, ∃ u : IntegralFiniteUnits K,
          finitePrincipal K a * finiteScalar K s * z = c * integralFiniteUnit K u := by
  classical
  let P (j : ClassGroup (𝓞 K)) (z : (LocalFiniteAdeles K)ˣ) : Prop :=
    ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ClassGroup.mk K I = j ∧
      ∀ p : Nat.Primes, completedFractionalIdeal p.val (I : FractionalIdeal (𝓞 K)⁰ K) =
        (z.val p) • (completedMaximalOrder (K := K) p.val).toSubmodule
  let J := {j : ClassGroup (𝓞 K) // ∃ z, P j z}
  choose rep I hclass hloc using (fun j : J => j.property)
  refine ⟨Set.range rep, Set.finite_range rep, ?_⟩
  intro z
  obtain ⟨s,I',hI'⟩ := finite_idele_ideal_patch K z
  have hgen (p : Nat.Primes) :
      completedFractionalIdeal p.val (I' : FractionalIdeal (𝓞 K)⁰ K) =
        ((finiteScalar K s * z).val p) •
          (completedMaximalOrder (K := K) p.val).toSubmodule := by
    rw [hI']
    congr 1
    rw [Algebra.smul_def]
    rfl
  let j : J := ⟨ClassGroup.mk K I', finiteScalar K s * z, I', rfl, hgen⟩
  obtain ⟨a,ha,heq⟩ := (fractionalIdeal_same_class I' (I j)).mp (hclass j).symm
  let au : Kˣ := Units.mk0 a ha
  let w := finitePrincipal K au * finiteScalar K s * z
  have hw (p : Nat.Primes) :
      (localUnit K w p).val • (completedMaximalOrder (K := K) p.val).toSubmodule =
        (localUnit K (rep j) p).val •
          (completedMaximalOrder (K := K) p.val).toSubmodule := by
    have H := congrArg (completedFractionalIdeal p.val) heq
    rw [completedFractionalIdeal_singleton_mul, hI' p, hloc j p, smul_smul] at H
    change (((Algebra.TensorProduct.includeRight a : LocalAlgebra p.val K) *
      algebraMap (Padic p.val) (LocalAlgebra p.val K) (s.val p)) * z.val p) • _ = _
    rw [mul_assoc, ← Algebra.smul_def]
    exact H
  choose u hu using (fun p : Nat.Primes =>
    local_generators_associated p.val (localUnit K w p) (localUnit K (rep j) p) (hw p))
  refine ⟨rep j, ⟨j,rfl⟩, au, s, u, ?_⟩
  apply Units.ext
  ext p
  change (localUnit K w p).val = (localUnit K (rep j) p).val * ((u p).val : LocalAlgebra p.val K)
  simpa only [mul_comm] using hu p

 
def realTensorMap {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) : RealAlgebra K →ₐ[ℝ] (Fin n → ℝ) :=
  AlgHom.liftEquiv ℚ ℝ K (Fin n → ℝ)
    (AlgHom.pi (fun i => RingHom.equivRatAlgHom K ℝ (σ i)))

@[simp] lemma realTensorMap_tmul {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (r : ℝ) (a : K) (i : Fin n) :
    realTensorMap σ (r ⊗ₜ[ℚ] a) i = r * σ i a := rfl

lemma realTensorMap_bijective {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : finrank ℚ K = n) :
    Function.Bijective (realTensorMap σ) := by
  classical
  let M := fractionalIdealFullLattice (K := K) hn (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  let b := fullLatticeRatBasis M hn
  have hlin : (realTensorMap σ).toLinearMap =
      (embeddingMatrix M σ).vecMulLinear.comp (b.baseChange ℝ).equivFun.toLinearMap := by
    apply (b.baseChange ℝ).ext
    intro j
    ext i
    have hc : (b.baseChange ℝ).equivFun ((b.baseChange ℝ) j) = Pi.single j 1 := by
      ext k
      simpa only [Pi.single_apply, eq_comm] using (b.baseChange ℝ).equivFun_self j k
    change realTensorMap σ ((b.baseChange ℝ) j) i =
      Matrix.vecMul ((b.baseChange ℝ).equivFun ((b.baseChange ℝ) j)) (embeddingMatrix M σ) i
    rw [hc]
    simp [Basis.baseChange_apply, Matrix.vecMul, dotProduct, embeddingMatrix, b, Pi.single_apply]
  have hinj : Function.Injective (embeddingMatrix M σ).vecMulLinear :=
    Matrix.vecMul_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr
        (embeddingMatrix_det_ne_zero M σ hn)))
  have hbij : Function.Bijective (embeddingMatrix M σ).vecMulLinear :=
    ⟨hinj, LinearMap.surjective_of_injective hinj⟩
  change Function.Bijective (realTensorMap σ).toLinearMap
  rw [hlin]
  exact hbij.comp (b.baseChange ℝ).equivFun.bijective

def realTensorEquiv {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : finrank ℚ K = n) :
    RealAlgebra K ≃ₐ[ℝ] (Fin n → ℝ) :=
  AlgEquiv.ofBijective (realTensorMap σ) (realTensorMap_bijective σ hn)

lemma continuous_realTensorEquiv_symm {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : finrank ℚ K = n) :
    Continuous (realTensorEquiv σ hn).symm :=
  IsModuleTopology.continuous_of_linearMap (realTensorEquiv σ hn).symm.toLinearMap

 
def chooseOrderedEmbeddings {n : ℕ} (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (hn : finrank ℚ K = n) : OrderedEmbeddings n K :=
  (Fintype.equivFinOfCardEq (show Fintype.card (NumberField.InfinitePlace K) = n by
    rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, add_zero,
      ← NumberField.IsTotallyReal.finrank, hn])).symm.trans
    (Equiv.ofBijective (realPlace (K := K))
      ⟨realPlace_injective,realPlace_surjective⟩).symm

 
def fullLog (d : ℕ) (t : Fin d → ℝ) : Fin (d+1) → ℝ :=
  Fin.snoc t (- ∑ i, t i)

lemma continuous_fullLog (d : ℕ) : Continuous (fullLog d) := by
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [fullLog, Fin.snoc_last]
    exact (continuous_finsetSum _ (fun i _ => continuous_apply i)).neg
  · simpa [fullLog] using (continuous_apply j : Continuous (fun t : Fin d → ℝ => t j))

def signedExpUnit (n : ℕ) (s : Fin n → SignTypeˣ) (t : Fin n → ℝ) :
    (Fin n → ℝ)ˣ where
  val i := signValue (s i) * Real.exp (t i)
  inv i := signValue (s i) * Real.exp (-t i)
  val_inv := by
    ext i
    change (signValue (s i) * Real.exp (t i)) * (signValue (s i) * Real.exp (-t i)) = 1
    rw [mul_mul_mul_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one,
      ← sq, signValue_sq]
  inv_val := by
    ext i
    change (signValue (s i) * Real.exp (-t i)) * (signValue (s i) * Real.exp (t i)) = 1
    rw [mul_mul_mul_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one,
      ← sq, signValue_sq]

lemma continuous_signedExpUnit (n : ℕ) :
    Continuous (fun x : (Fin n → SignTypeˣ) × (Fin n → ℝ) => signedExpUnit n x.1 x.2) := by
  apply Units.continuous_iff.mpr
  constructor <;> apply continuous_pi <;> intro i
  · exact ((continuous_of_discreteTopology : Continuous (fun s : Fin n → SignTypeˣ => signValue (s i))).comp
      continuous_fst).mul (Real.continuous_exp.comp ((continuous_apply i).comp continuous_snd))
  · exact ((continuous_of_discreteTopology : Continuous (fun s : Fin n → SignTypeˣ => signValue (s i))).comp
      continuous_fst).mul (Real.continuous_exp.comp (((continuous_apply i).comp continuous_snd).neg))

abbrev splitScalar (n : ℕ) : ℝˣ →* (Fin n → ℝ)ˣ :=
  Units.map (algebraMap ℝ (Fin n → ℝ)).toMonoidHom
abbrev splitPrincipal {n : ℕ} {K : Type*} [Field K] (σ : OrderedEmbeddings n K) :
    Kˣ →* (Fin n → ℝ)ˣ := Units.map (RingHom.pi (fun i => σ i)).toMonoidHom

lemma splitUnit_nonzero {n : ℕ} (z : (Fin n → ℝ)ˣ) (i : Fin n) : z.val i ≠ 0 := by
  intro h
  have H := congrFun z.val_inv i
  change z.val i * z.inv i = 1 at H
  rw [h, zero_mul] at H
  exact zero_ne_one H

 
lemma exists_compact_log_representatives {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K) :
    ∃ P : Set (Fin d → ℝ), IsCompact P ∧ ∀ x : Fin d → ℝ,
      ∃ u : (𝓞 K)ˣ, x + orderedUnitLog σ (Additive.ofMul u) ∈ P := by
  let L := orderedLogSubgroup σ (⊤ : Subgroup (𝓞 K)ˣ)
  have := ZLattice.module_free ℝ L
  let b := Module.Free.chooseBasis ℤ L
  let B := b.ofZLatticeBasis ℝ
  refine ⟨B.parallelepiped, B.parallelepiped.isCompact, ?_⟩
  intro x
  let l := ZSpan.floor B x
  have hl : (l : Fin d → ℝ) ∈ L := by
    exact (le_of_eq (show (Submodule.span ℤ (Set.range B) : Submodule ℤ (Fin d → ℝ)) = L from
      b.ofZLatticeBasis_span ℝ)) l.property
  obtain ⟨u,_,hu⟩ := (mem_orderedLogSubgroup σ ⊤ (-(l : Fin d → ℝ))).mp (L.neg_mem hl)
  refine ⟨u, ?_⟩
  rw [hu, ← sub_eq_add_neg]
  exact ZSpan.fundamentalDomain_subset_parallelepiped B (ZSpan.fract_mem_fundamentalDomain B x)

 

theorem real_split_compact_representatives {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K) :
    ∃ C : Set (Fin (d+1) → ℝ)ˣ, IsCompact C ∧
      ∀ z : (Fin (d+1) → ℝ)ˣ, ∃ c ∈ C, ∃ r : ℝˣ, ∃ u : (𝓞 K)ˣ,
        splitScalar (d+1) r * splitPrincipal σ (integralUnit u) * z = c := by
  classical
  obtain ⟨P,hP,hcover⟩ := exists_compact_log_representatives σ
  let f (x : (Fin (d+1) → SignTypeˣ) × (Fin d → ℝ)) :=
    signedExpUnit (d+1) x.1 (fullLog d x.2)
  have hf : Continuous f := (continuous_signedExpUnit (d+1)).comp
    (continuous_fst.prodMk ((continuous_fullLog d).comp continuous_snd))
  let C := f '' (Set.univ ×ˢ P)
  refine ⟨C, (isCompact_univ.prod hP).image hf, ?_⟩
  intro z
  let l (i : Fin (d+1)) := Real.log |z.val i|
  let m : ℝ := (∑ i, l i) / (d+1 : ℕ)
  let v (i : Fin d) := l i.castSucc - m
  obtain ⟨u,hu⟩ := hcover v
  let r : ℝˣ := Units.mk0 (Real.exp (-m)) (Real.exp_ne_zero _)
  let w := splitScalar (d+1) r * splitPrincipal σ (integralUnit u) * z
  let t := v + orderedUnitLog σ (Additive.ofMul u)
  have hune (i : Fin (d+1)) : σ i (u : K) ≠ 0 :=
    (map_ne_zero (σ i)).mpr (integralUnit u).ne_zero
  have hwlog (i : Fin (d+1)) : Real.log |w.val i| =
      -m + Real.log |σ i (u : K)| + l i := by
    change Real.log |(Real.exp (-m) * σ i (u : K)) * z.val i| = _
    rw [Real.log_abs, Real.log_mul (mul_ne_zero (Real.exp_ne_zero _) (hune i)) (splitUnit_nonzero z i),
      Real.log_mul (Real.exp_ne_zero _) (hune i), Real.log_exp]
    simp only [Real.log_abs, l]
  have hsum : ∑ i, Real.log |w.val i| = 0 := by
    simp only [hwlog, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, sum_orderedUnitLog_full σ u]
    have hn0 : ((d+1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d)
    dsimp [m]
    field_simp
    ring
  have hdel (i : Fin d) : Real.log |w.val i.castSucc| = t i := by
    rw [hwlog]
    change -m + _ + _ = (l i.castSucc - m) + orderedUnitLog σ (Additive.ofMul u) i
    rw [orderedUnitLog_apply]
    ring
  have hfull : (fun i => Real.log |w.val i|) = fullLog d t := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.sum_univ_castSucc] at hsum
      simp only [hdel] at hsum
      simp only [fullLog,Fin.snoc_last]
      linarith
    · simpa only [fullLog, Fin.snoc_castSucc] using hdel j
  let s (i : Fin (d+1)) : SignTypeˣ :=
    Units.map (signHom : ℝ →*₀ SignType).toMonoidHom
      (Units.map (Pi.evalMonoidHom (fun _ : Fin (d+1) => ℝ) i) w)
  have hw : w = signedExpUnit (d+1) s (fullLog d t) := by
    apply Units.ext
    funext i
    change w.val i = signValue (s i) * Real.exp (fullLog d t i)
    rw [← hfull, Real.exp_log (abs_pos.mpr (splitUnit_nonzero w i))]
    exact (sign_mul_abs (w.val i)).symm
  refine ⟨w, ?_, r, u, rfl⟩
  exact ⟨(s,t), ⟨Set.mem_univ _,hu⟩, hw.symm⟩

 
def integralUnitFinite (K : Type*) [Field K] [NumberField K]
    (u : (𝓞 K)ˣ) : IntegralFiniteUnits K := fun p =>
  Units.map ((Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p.val K).toRingHom.comp
    (algebraMap (𝓞 K) K) |>.codRestrict (completedMaximalOrder (K := K) p.val).toSubring
    (fun a => show (Algebra.TensorProduct.includeRight (a : K) : LocalAlgebra p.val K) ∈
      completedFractionalIdeal p.val (1 : FractionalIdeal (𝓞 K)⁰ K) from
      Submodule.subset_span ⟨(a : K), (FractionalIdeal.mem_one_iff (𝓞 K)⁰).mpr ⟨a,rfl⟩,rfl⟩)).toMonoidHom u

@[simp] lemma integralFiniteUnit_integralUnitFinite (K : Type*) [Field K] [NumberField K]
    (u : (𝓞 K)ˣ) : integralFiniteUnit K (integralUnitFinite K u) =
      finitePrincipal K (integralUnit u) := by
  apply Units.ext
  ext p
  rfl

@[simp] lemma integralFiniteUnit_mul (K : Type*) [Field K] [NumberField K]
    (u v : IntegralFiniteUnits K) : integralFiniteUnit K (u*v) =
      integralFiniteUnit K u * integralFiniteUnit K v := by
  apply Units.ext
  ext p
  rfl

 
def splitTensorEquiv {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : finrank ℚ K = n) :
    TensorAdeles K ≃ₐ[ℚ] (Fin n → ℝ) × LocalFiniteAdeles K :=
  (tensorModelEquiv K).trans (AlgEquiv.prodCongr ((realTensorEquiv σ hn).restrictScalars ℚ)
    (AlgEquiv.refl : LocalFiniteAdeles K ≃ₐ[ℚ] LocalFiniteAdeles K))

lemma continuous_splitTensorEquiv_symm {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : finrank ℚ K = n) :
    Continuous (splitTensorEquiv σ hn).symm := by
  change Continuous ((tensorModelEquiv K).symm ∘
    (fun x : (Fin n → ℝ) × LocalFiniteAdeles K => ((realTensorEquiv σ hn).symm x.1,x.2)))
  exact (continuous_tensorModelEquiv_symm K).comp
    (((continuous_realTensorEquiv_symm σ hn).comp continuous_fst).prodMk continuous_snd)

def ideleEquiv {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : finrank ℚ K = n) :
    (TensorAdeles K)ˣ ≃* (Fin n → ℝ)ˣ × (LocalFiniteAdeles K)ˣ :=
  (Units.mapEquiv (splitTensorEquiv σ hn).toMulEquiv).trans MulEquiv.prodUnits

lemma continuous_ideleEquiv_symm {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : finrank ℚ K = n) :
    Continuous (ideleEquiv σ hn).symm := by
  apply Units.continuous_iff.mpr
  constructor
  · exact (continuous_splitTensorEquiv_symm σ hn).comp
      ((Units.continuous_val.comp continuous_fst).prodMk (Units.continuous_val.comp continuous_snd))
  · exact (continuous_splitTensorEquiv_symm σ hn).comp
      ((Units.continuous_coe_inv.comp continuous_fst).prodMk (Units.continuous_coe_inv.comp continuous_snd))

abbrev tensorPrincipal (K : Type*) [Field K] [NumberField K] : Kˣ →* (TensorAdeles K)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] TensorAdeles K).toMonoidHom
abbrev tensorScalar (K : Type*) [Field K] [NumberField K] : RationalAdelesˣ →* (TensorAdeles K)ˣ :=
  Units.map (Algebra.TensorProduct.includeLeft : RationalAdeles →ₐ[ℚ] TensorAdeles K).toMonoidHom

@[simp] lemma ideleEquiv_tensorPrincipal {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : finrank ℚ K = n) (a : Kˣ) :
    ideleEquiv σ hn (tensorPrincipal K a) = (splitPrincipal σ a, finitePrincipal K a) := by
  apply Prod.ext <;> apply Units.ext
  · funext i
    change 1 * σ i a.val = σ i a.val
    exact one_mul _
  · ext p
    change finiteTensorMap K ((1 : RationalFiniteAdeles) ⊗ₜ[ℚ] a.val) p =
      (Algebra.TensorProduct.includeRight a.val : LocalAlgebra p.val K)
    rw [finiteTensorMap_tmul_apply]
    exact one_smul _ _

@[simp] lemma ideleEquiv_tensorScalar {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : finrank ℚ K = n)
    (r : ℝˣ) (s : RationalFiniteAdelesˣ) :
    ideleEquiv σ hn (tensorScalar K (MulEquiv.prodUnits.symm (r,s))) =
      (splitScalar n r, finiteScalar K s) := by
  apply Prod.ext <;> apply Units.ext
  · funext i
    change r.val * σ i 1 = r.val
    rw [map_one,mul_one]
  · ext p
    change finiteTensorMap K (s.val ⊗ₜ[ℚ] (1 : K)) p =
      algebraMap (Padic p.val) (LocalAlgebra p.val K) (s.val p)
    rw [finiteTensorMap_tmul_apply,map_one,Algebra.smul_def,mul_one]

 
def localQuotientMap {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : finrank ℚ K = n) :
    ((Fin n → ℝ)ˣ × (LocalFiniteAdeles K)ˣ) →* TorusQuotient K :=
  (QuotientGroup.mk' (torusPrincipalScalarSubgroup K)).comp (ideleEquiv σ hn).symm.toMonoidHom

lemma continuous_localQuotientMap {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : finrank ℚ K = n) :
    Continuous (localQuotientMap σ hn) :=
  QuotientGroup.continuous_mk.comp (continuous_ideleEquiv_symm σ hn)

@[simp] lemma localQuotientMap_principal {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : finrank ℚ K = n) (a : Kˣ) :
    localQuotientMap σ hn (splitPrincipal σ a,finitePrincipal K a) = 1 := by
  rw [← ideleEquiv_tensorPrincipal σ hn a]
  change QuotientGroup.mk ((ideleEquiv σ hn).symm (ideleEquiv σ hn (tensorPrincipal K a))) = 1
  rw [MulEquiv.symm_apply_apply]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact (le_sup_left : (tensorPrincipal K).range ≤ torusPrincipalScalarSubgroup K) ⟨a,rfl⟩

@[simp] lemma localQuotientMap_scalar {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : finrank ℚ K = n) (r : ℝˣ) (s : RationalFiniteAdelesˣ) :
    localQuotientMap σ hn (splitScalar n r,finiteScalar K s) = 1 := by
  rw [← ideleEquiv_tensorScalar σ hn r s]
  change QuotientGroup.mk ((ideleEquiv σ hn).symm
    (ideleEquiv σ hn (tensorScalar K (MulEquiv.prodUnits.symm (r,s))))) = 1
  rw [MulEquiv.symm_apply_apply]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact (le_sup_right : (tensorScalar K).range ≤ torusPrincipalScalarSubgroup K)
    ⟨MulEquiv.prodUnits.symm (r,s),rfl⟩

 

theorem adelic_torus_quotient_compact (d : ℕ) (_hprime : (d+1).Prime)
    (_hdegree : 5 ≤ d+1) (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (hn : finrank ℚ K = d+1) :
    CompactSpace (TorusQuotient K) := by
  classical
  let σ := chooseOrderedEmbeddings K hn
  obtain ⟨Cr,hCr,hcoverr⟩ := real_split_compact_representatives σ
  obtain ⟨Cf,hCf,hcoverf⟩ := finite_idele_finite_representatives K
  let f (x : (((Fin (d+1) → ℝ)ˣ × (LocalFiniteAdeles K)ˣ) × IntegralFiniteUnits K)) :=
    localQuotientMap σ hn (x.1.1,x.1.2 * integralFiniteUnit K x.2)
  have hf : Continuous f := (continuous_localQuotientMap σ hn).comp
    (continuous_fst.fst.prodMk (continuous_fst.snd.mul
      ((continuous_integralFiniteUnit K).comp continuous_snd)))
  have himage : f '' ((Cr ×ˢ Cf) ×ˢ (Set.univ : Set (IntegralFiniteUnits K))) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨z,hz⟩ := (QuotientGroup.mk_surjective : Function.Surjective
      (QuotientGroup.mk : (TensorAdeles K)ˣ → TorusQuotient K)) q
    let zp := ideleEquiv σ hn z
    obtain ⟨cf,hcf,a,s,u,hfinite⟩ := hcoverf zp.2
    obtain ⟨cr,hcr,r,e,hreal⟩ := hcoverr (splitPrincipal σ a * zp.1)
    let u' := integralUnitFinite K e * u
    refine ⟨((cr,cf),u'), ⟨⟨hcr,hcf⟩,Set.mem_univ _⟩, ?_⟩
    have heq : (cr,cf * integralFiniteUnit K u') =
        (splitScalar (d+1) r, finiteScalar K s) *
        (splitPrincipal σ (integralUnit e * a),finitePrincipal K (integralUnit e * a)) * zp := by
      apply Prod.ext
      · change cr = splitScalar (d+1) r * splitPrincipal σ (integralUnit e * a) * zp.1
        simpa only [map_mul,mul_assoc] using hreal.symm
      · change cf * integralFiniteUnit K u' =
          finiteScalar K s * finitePrincipal K (integralUnit e * a) * zp.2
        simp only [u',integralFiniteUnit_mul,integralFiniteUnit_integralUnitFinite,map_mul]
        let : CommGroup (LocalFiniteAdeles K)ˣ :=
          @Units.instCommGroupUnits (LocalFiniteAdeles K) inferInstance
        calc
          cf * (finitePrincipal K (integralUnit e) * integralFiniteUnit K u) =
              finitePrincipal K (integralUnit e) * (cf * integralFiniteUnit K u) := by ac_rfl
          _ = finitePrincipal K (integralUnit e) *
              (finitePrincipal K a * finiteScalar K s * zp.2) := congrArg _ hfinite.symm
          _ = _ := by ac_rfl
    change localQuotientMap σ hn (cr,cf * integralFiniteUnit K u') = q
    rw [heq,map_mul,map_mul,localQuotientMap_scalar,localQuotientMap_principal,one_mul,one_mul]
    change QuotientGroup.mk ((ideleEquiv σ hn).symm (ideleEquiv σ hn z)) = q
    rw [MulEquiv.symm_apply_apply]
    exact hz
  have hcompact := ((hCr.prod hCf.isCompact).prod isCompact_univ).image hf
  rw [himage] at hcompact
  exact isCompact_univ_iff.mp hcompact

end PrimeDegreePackets.Adelic

end

end OAI
