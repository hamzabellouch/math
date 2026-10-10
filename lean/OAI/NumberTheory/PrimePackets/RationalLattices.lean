import Mathlib
import OAI.NumberTheory.PrimePackets.ProjectivePeriods

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
namespace PrimeDegreePackets

lemma pointLattice_basis_nonempty {n : ℕ} (x : X n) :
    Nonempty (Basis (Fin n) ℤ (pointLattice x)) := by
  induction x using Quotient.inductionOn with
  | h g =>
    exact ⟨(Pi.basisFun ℤ (Fin n)).map (integerRowEquiv g)⟩

def pointLatticeBasis {n : ℕ} (x : X n) : Basis (Fin n) ℤ (pointLattice x) :=
  Classical.choice (pointLattice_basis_nonempty x)

def rationalPointRealization {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (x : X n) (f : K ≃ₗ[ℚ] rationalPointSpace x) : K →ₗ[ℚ] (Fin n → ℝ) :=
  (rationalPointSpace x).subtype.comp f.toLinearMap

def rationalPointPullback {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (x : X n) (f : K ≃ₗ[ℚ] rationalPointSpace x) : Submodule ℤ K :=
  (pointLattice x).comap ((rationalPointRealization x f).restrictScalars ℤ)

def rationalPointPullbackMap {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (x : X n) (f : K ≃ₗ[ℚ] rationalPointSpace x) :
    rationalPointPullback x f →ₗ[ℤ] pointLattice x where
  toFun a := ⟨rationalPointRealization x f a,a.prop⟩
  map_add' a b := Subtype.ext (map_add _ a.val b.val)
  map_smul' z a := Subtype.ext (map_smul ((rationalPointRealization x f).restrictScalars ℤ) z a.val)

lemma rationalPointPullbackMap_bijective {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (x : X n) (f : K ≃ₗ[ℚ] rationalPointSpace x) :
    Function.Bijective (rationalPointPullbackMap x f) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    apply f.injective
    apply Subtype.ext
    exact congrArg (fun w : pointLattice x => w.val) hab
  · intro w
    let v : rationalPointSpace x := ⟨w.val,Submodule.subset_span w.prop⟩
    refine ⟨⟨f.symm v,?_⟩,?_⟩
    · change (f (f.symm v)).val ∈ pointLattice x
      simpa only [f.apply_symm_apply] using w.prop
    · apply Subtype.ext
      change (f (f.symm v)).val = w.val
      simp [v]

def rationalPointPullbackEquiv {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (x : X n) (f : K ≃ₗ[ℚ] rationalPointSpace x) :
    rationalPointPullback x f ≃ₗ[ℤ] pointLattice x :=
  LinearEquiv.ofBijective (rationalPointPullbackMap x f) (rationalPointPullbackMap_bijective x f)

lemma rationalPointPullback_spans {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (x : X n) (f : K ≃ₗ[ℚ] rationalPointSpace x) :
    Submodule.span ℚ (rationalPointPullback x f : Set K) = ⊤ := by
  change Submodule.span ℚ ((rationalPointRealization x f) ⁻¹' (pointLattice x : Set _)) = ⊤
  rw [Submodule.span_preimage_eq ⟨0,(pointLattice x).zero_mem⟩ (by
    intro w hw
    refine ⟨f.symm ⟨w,Submodule.subset_span hw⟩,?_⟩
    simp [rationalPointRealization])]
  apply top_unique
  intro a ha
  exact (f a).prop

 

def rationalPointFullLattice {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (x : X n) (f : K ≃ₗ[ℚ] rationalPointSpace x) : FullLattice n K where
  carrier := rationalPointPullback x f
  basis := (pointLatticeBasis x).map (rationalPointPullbackEquiv x f).symm
  spans := rationalPointPullback_spans x f

lemma rationalPointFullLattice_image {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (x : X n) (f : K ≃ₗ[ℚ] rationalPointSpace x) :
    (rationalPointFullLattice x f).carrier.map
      ((rationalPointRealization x f).restrictScalars ℤ) = pointLattice x := by
  ext w
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ha
  · intro hw
    refine ⟨f.symm ⟨w,Submodule.subset_span hw⟩,?_,?_⟩
    · change (f (f.symm ⟨w,Submodule.subset_span hw⟩)).val ∈ pointLattice x
      simpa using hw
    · simp [rationalPointRealization]

end PrimeDegreePackets

open scoped NumberField
namespace PrimeDegreePackets

lemma pointLattice_injective {n : ℕ} : Function.Injective (@pointLattice n) := by
  intro x y h
  induction x using Quotient.inductionOn with
  | h g =>
    induction y using Quotient.inductionOn with
    | h k => exact (quotient_eq_iff_rowLattice_eq g k).mpr h

lemma rationalPoint_units_invariant {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (x : X n) (f : K ≃ₗ[ℚ] rationalPointSpace x) (σ : OrderedEmbeddings n K)
    (hmul : ∀ a b : K, ∀ i,
      rationalPointRealization x f (a*b) i = σ i a * rationalPointRealization x f b i)
    (u : (𝓞 K)ˣ) (hu : u ∈ unitStabilizer (rationalPointFullLattice x f)) :
    (pointLattice x).map (diagonalLinear n (fun i => σ i (u : K))) = pointLattice x := by
  rw [←rationalPointFullLattice_image x f]
  apply le_antisymm
  · rintro w hw
    obtain ⟨y,hy,rfl⟩ := Submodule.mem_map.mp hw
    obtain ⟨a,ha,rfl⟩ := Submodule.mem_map.mp hy
    refine Submodule.mem_map.mpr ⟨(u : K)*a,(hu a).mp ha,?_⟩
    funext i
    exact hmul (u : K) a i
  · rintro w hw
    obtain ⟨a,ha,rfl⟩ := Submodule.mem_map.mp hw
    refine Submodule.mem_map.mpr ⟨rationalPointRealization x f ((↑u⁻¹ : K)*a),
      Submodule.mem_map.mpr ⟨_,((unitStabilizer _).inv_mem hu a).mp ha,rfl⟩,?_⟩
    funext i
    change σ i (u : K) * rationalPointRealization x f ((↑u⁻¹ : K)*a) i = _
    rw [hmul,←mul_assoc,←map_mul]
    simp

 

theorem rationalPoint_orderedLog_le_period {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (x : X (d+1)) (f : K ≃ₗ[ℚ] rationalPointSpace x) (σ : OrderedEmbeddings (d+1) K)
    (hmul : ∀ a b : K, ∀ i,
      rationalPointRealization x f (a*b) i = σ i a * rationalPointRealization x f b i) :
    (orderedLogSubgroup σ (positiveUnitStabilizer (rationalPointFullLattice x f) σ)).toAddSubgroup ≤
      periodGroup x := by
  intro v hv
  obtain ⟨u,hu,rfl⟩ := (mem_orderedLogSubgroup σ _ v).mp hv
  have H := (mem_positiveUnitStabilizer (rationalPointFullLattice x f) σ u).mp hu
  change orbitMap x (orderedUnitLog σ (Additive.ofMul u)) = x
  apply pointLattice_injective
  rw [orbitMap,pointLattice_rightAction_diagonal x _ _ (diagonalFlow_orderedUnitLog σ u H.2)]
  exact rationalPoint_units_invariant x f σ hmul u H.1

 

theorem rationalPoint_period_isZLattice {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (x : X (d+1)) (f : K ≃ₗ[ℚ] rationalPointSpace x) (σ : OrderedEmbeddings (d+1) K)
    (hmul : ∀ a b : K, ∀ i,
      rationalPointRealization x f (a*b) i = σ i a * rationalPointRealization x f b i) :
    IsZLattice ℝ (periodGroup x).toIntSubmodule := by
  let L := orderedLogSubgroup σ (positiveUnitStabilizer (rationalPointFullLattice x f) σ)
  let : IsZLattice ℝ L := (positiveStabilizer_fullLogLattice (rationalPointFullLattice x f) σ).2
  constructor
  apply top_unique
  rw [←IsZLattice.span_top (K := ℝ) (L := L)]
  apply Submodule.span_mono
  exact rationalPoint_orderedLog_le_period x f σ hmul

 
theorem rationalPoint_diagonalOrbit_isCompact {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (x : X (d+1)) (f : K ≃ₗ[ℚ] rationalPointSpace x) (σ : OrderedEmbeddings (d+1) K)
    (hmul : ∀ a b : K, ∀ i,
      rationalPointRealization x f (a*b) i = σ i a * rationalPointRealization x f b i) :
    IsCompact (diagonalOrbit x) := by
  let := rationalPoint_period_isZLattice x f σ hmul
  apply IsZLattice.isCompact_range_of_periodic (periodGroup x).toIntSubmodule
    (orbitMap x) (continuous_orbitMap _)
  intro z w hw
  change orbitMap x w = x at hw
  rw [add_comm z w,orbitMap_add,hw]

end PrimeDegreePackets


namespace PrimeDegreePackets

 

def fieldRatLinearEquiv {K V : Type*} [Field K] [CharZero K]
    [AddCommGroup V] [Module ℚ V] (f : K ≃+ V) : K ≃ₗ[ℚ] V :=
  { f with map_smul' := by intro q a; exact map_rat_smul f q a }

theorem diagonalRationalAlgebra_fullDegree_period {d : ℕ} (x : X (d+1))
    (hx : ∀ w ∈ rationalPointSpace x, w ≠ 0 → ∀ i, w i ≠ 0)
    (hdim : Module.finrank ℚ (diagonalRationalAlgebra (rationalPointSpace x)) = d+1) :
    IsZLattice ℝ (periodGroup x).toIntSubmodule := by
  let W := rationalPointSpace x
  obtain ⟨v,hv⟩ := rationalPointSpace_exists_nonzero_coordinates x
  let : Field (diagonalRationalAlgebra W) := (diagonalRationalAlgebra_isField W v hv hx).toField
  let : NumberField (diagonalRationalAlgebra W) := {
    to_finiteDimensional := by
      convert diagonalRationalAlgebra_finite W v hv using 1
      exact Subsingleton.elim _ _ }
  let : NumberField.IsTotallyReal (diagonalRationalAlgebra W) :=
    diagonalRationalAlgebra_totallyReal W v hv hx (rationalPointSpace_finrank x) hdim
      (rationalPointSpace_real_span x)
  have hinj : Function.Injective (diagonalCoordinateEmbedding W) := by
    intro i j hij
    apply diagonalComplexEmbedding_injective W v hv (hdim.trans (rationalPointSpace_finrank x).symm)
      (rationalPointSpace_real_span x)
    exact congrArg (fun f => Complex.ofRealHom.comp f) hij
  have hsurj : Function.Surjective (diagonalCoordinateEmbedding W) := by
    intro θ
    obtain ⟨i,hi⟩ := diagonalComplexEmbedding_surjective W v hv hx
      (rationalPointSpace_finrank x) hdim (rationalPointSpace_real_span x)
      (Complex.ofRealHom.comp θ)
    refine ⟨i,?_⟩
    ext a
    exact Complex.ofReal_injective (congrArg (fun F : diagonalRationalAlgebra W →+* ℂ => F a) hi)
  let σ : OrderedEmbeddings (d+1) (diagonalRationalAlgebra W) :=
    Equiv.ofBijective (diagonalCoordinateEmbedding W) ⟨hinj,hsurj⟩
  let f : diagonalRationalAlgebra W ≃ₗ[ℚ] W := LinearEquiv.ofBijective
    (diagonalRationalEval W v) ⟨diagonalRationalEval_injective W v hv,
      diagonalRationalEval_surjective W v hv (hdim.trans (rationalPointSpace_finrank x).symm)⟩
  apply rationalPoint_period_isZLattice x
    (fieldRatLinearEquiv f.toAddEquiv) σ
  intro a b i
  change (a.val i*b.val i)*v.val i = a.val i*(b.val i*v.val i)
  exact mul_assoc _ _ _

theorem diagonalRationalAlgebra_fullDegree_compact {d : ℕ} (x : X (d+1))
    (hx : ∀ w ∈ rationalPointSpace x, w ≠ 0 → ∀ i, w i ≠ 0)
    (hdim : Module.finrank ℚ (diagonalRationalAlgebra (rationalPointSpace x)) = d+1) :
    IsCompact (diagonalOrbit x) := by
  let := diagonalRationalAlgebra_fullDegree_period x hx hdim
  apply IsZLattice.isCompact_range_of_periodic (periodGroup x).toIntSubmodule
    (orbitMap x) (continuous_orbitMap _)
  intro z w hw
  change orbitMap x w = x at hw
  rw [add_comm z w,orbitMap_add,hw]

 

theorem ae_scalar_commutant_or_compact (d : ℕ) (hn : (d+1).Prime)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, diagonalRationalAlgebra (rationalPointSpace x) = ⊥ ∨
      IsCompact (diagonalOrbit x) := by
  filter_upwards [ae_rationalPointSpace_no_coordinate_zero d μ hA,
    ae_point_diagonalRationalAlgebra_prime_degree d hn μ hA] with x hx hd
  rcases hd with h | h
  · exact Or.inl h
  · exact Or.inr (diagonalRationalAlgebra_fullDegree_compact x hx h)

end PrimeDegreePackets


namespace PrimeDegreePackets

def AlgebraicReal := {r : ℝ // IsAlgebraic ℚ r}

instance algebraicReal_countable : Countable AlgebraicReal :=
  (Algebraic.countable ℚ ℝ).to_subtype

abbrev AlgebraicFrame (n : ℕ) := Matrix (Fin n) (Fin n) AlgebraicReal

lemma diagonalRationalAlgebra_coordinate_algebraic {n : ℕ}
    (W : Submodule ℚ (Fin n → ℝ)) [Module.Finite ℚ W]
    (v : W) (hv : ∀ i, v.val i ≠ 0) (a : diagonalRationalAlgebra W) (i : Fin n) :
    IsAlgebraic ℚ (a.val i) := by
  let := diagonalRationalAlgebra_finite W v hv
  let f : diagonalRationalAlgebra W →ₐ[ℚ] ℝ :=
    (Pi.evalAlgHom ℚ (fun _ : Fin n => ℝ) i).comp (diagonalRationalAlgebra W).val
  exact (Algebra.IsAlgebraic.isAlgebraic a).algHom f

 

theorem exists_algebraicFrame_of_fullDegree {n : ℕ} (g : G n)
    (hdim : Module.finrank ℚ (diagonalRationalAlgebra
      (rationalPointSpace (Quotient.mk _ g : X n))) = n) :
    ∃ B : AlgebraicFrame n, ∃ v : Fin n → ℝ, (∀ j, 0 < v j) ∧
      ∀ i j, g.1 i j = (B i j).val * v j := by
  let x : X n := Quotient.mk _ g
  let W := rationalPointSpace x
  obtain ⟨v,hv⟩ := rationalPointSpace_exists_nonzero_coordinates x
  have hs := diagonalRationalEval_surjective W v hv (hdim.trans (rationalPointSpace_finrank x).symm)
  have hrows (i : Fin n) : g.1 i ∈ W := by
    change g.1 i ∈ rationalPointSpace (Quotient.mk _ g : X n)
    rw [rationalPointSpace_mk]
    exact Submodule.subset_span ⟨i,rfl⟩
  have ha (i j : Fin n) : IsAlgebraic ℚ (g.1 i j/v.val j) := by
    obtain ⟨a,ha⟩ := hs ⟨g.1 i,hrows i⟩
    have hij : g.1 i j/v.val j = a.val j := by
      rw [div_eq_iff (hv j)]
      exact (congrArg (fun w : W => w.val j) ha).symm
    rw [hij]
    exact diagonalRationalAlgebra_coordinate_algebraic W v hv a j
  have habs (i j : Fin n) : IsAlgebraic ℚ (g.1 i j/|v.val j|) := by
    rcases lt_or_gt_of_ne (hv j) with hj | hj
    · rw [abs_of_neg hj,div_neg]
      exact (ha i j).neg
    · rw [abs_of_pos hj]
      exact ha i j
  refine ⟨fun i j => ⟨g.1 i j/|v.val j|,habs i j⟩,fun j => |v.val j|,
    fun j => abs_pos.mpr (hv j),?_⟩
  intro i j
  exact (div_mul_cancel₀ _ (abs_ne_zero.mpr (hv j))).symm

 
def algebraicFrameClass {d : ℕ} (B : AlgebraicFrame (d+1)) : Set (X (d+1)) :=
  {x | ∃ g : G (d+1), ∃ v : Fin (d+1) → ℝ,
    (∀ j, 0 < v j) ∧ (∀ i j, g.1 i j = (B i j).val*v j) ∧ Quotient.mk _ g = x}

lemma algebraicFrameClass_sameOrbit {d : ℕ} (B : AlgebraicFrame (d+1))
    {x y : X (d+1)} (hx : x ∈ algebraicFrameClass B) (hy : y ∈ algebraicFrameClass B) :
    y ∈ diagonalOrbit x := by
  obtain ⟨g,v,hv,hg,rfl⟩ := hx
  obtain ⟨h,w,hw,hh,rfl⟩ := hy
  let t : Fin (d+1) → ℝ := fun j => w j / v j
  have ht : ∀ j, 0 < t j := fun j => div_pos (hw j) (hv j)
  have hm : h.1 = g.1 * Matrix.diagonal t := by
    ext i j
    rw [Matrix.mul_diagonal,hg,hh]
    dsimp [t]
    field_simp [ne_of_gt (hv j)]
  have hp : ∏ j, t j = 1 := by
    have H := congrArg Matrix.det hm
    rw [h.property,Matrix.det_mul,g.property,one_mul,Matrix.det_diagonal] at H
    exact H.symm
  obtain ⟨u,hu⟩ := exists_diagonalFlow_of_positive t ht hp
  refine ⟨u,?_⟩
  change Quotient.mk _ (g*diagonalFlow u) = Quotient.mk _ h
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  exact (congrArg (fun M => g.1*M) hu).trans hm.symm

lemma fullDegree_mem_algebraicFrameClass {d : ℕ} (x : X (d+1))
    (hdim : Module.finrank ℚ (diagonalRationalAlgebra (rationalPointSpace x)) = d+1) :
    ∃ B : AlgebraicFrame (d+1), x ∈ algebraicFrameClass B := by
  induction x using Quotient.inductionOn with
  | h g =>
    obtain ⟨B,v,hv,hg⟩ := exists_algebraicFrame_of_fullDegree g hdim
    exact ⟨B,g,v,hv,hg,rfl⟩

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma orbitQuotientMap_injective {d : ℕ} (x : X (d+1)) :
    Function.Injective (orbitQuotientMap x) := by
  intro a b hab
  obtain ⟨u,rfl⟩ := QuotientAddGroup.mk_surjective a
  obtain ⟨v,rfl⟩ := QuotientAddGroup.mk_surjective b
  apply QuotientAddGroup.eq.mpr
  change orbitMap x (-u+v) = x
  rw [add_comm (-u),orbitMap_add]
  change orbitMap x u = orbitMap x v at hab
  rw [←hab,←orbitMap_add,add_neg_cancel,orbitMap_zero]

lemma range_orbitQuotientMap {d : ℕ} (x : X (d+1)) :
    Set.range (orbitQuotientMap x) = diagonalOrbit x := by
  apply Set.ext
  intro y
  constructor
  · rintro ⟨a,rfl⟩
    obtain ⟨u,rfl⟩ := QuotientAddGroup.mk_surjective a
    exact ⟨u,rfl⟩
  · rintro ⟨u,rfl⟩
    exact ⟨QuotientAddGroup.mk u,rfl⟩

lemma orbitQuotientMap_measurableEmbedding {d : ℕ} (x : X (d+1))
    [IsZLattice ℝ (periodGroup x).toIntSubmodule] :
    MeasurableEmbedding (orbitQuotientMap x) := by
  let := compact_quotient_of_isZLattice (periodGroup x).toIntSubmodule
  exact ((continuous_orbitQuotientMap x).isClosedEmbedding
    (orbitQuotientMap_injective x)).measurableEmbedding

 

theorem measureEntropy_eq_zero_of_ae_mem_fullPeriodOrbit {d : ℕ} (x : X (d+1))
    [IsZLattice ℝ (periodGroup x).toIntSubmodule]
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun y => rightAction y (diagonalFlow u)) = μ)
    (hs : ∀ᵐ y ∂μ, y ∈ diagonalOrbit x) (u : LogCoordinates d) :
    measureEntropy μ (fun y => rightAction y (diagonalFlow u)) = 0 := by
  let := compact_quotient_of_isZLattice (periodGroup x).toIntSubmodule
  let f := orbitQuotientMap x
  have hf : MeasurableEmbedding f := orbitQuotientMap_measurableEmbedding x
  have hr : ∀ᵐ y ∂μ, y ∈ Set.range f := by rwa [range_orbitQuotientMap]
  let ν := μ.comap f
  let : IsProbabilityMeasure ν := hf.isProbabilityMeasure_comap hr
  have hmap : ν.map f = μ := (hf.map_comap μ).trans (Measure.restrict_eq_self_of_ae_mem hr)
  let a : LogCoordinates d ⧸ (periodGroup x).toIntSubmodule.toAddSubgroup := QuotientAddGroup.mk u
  let T := fun y : X (d+1) => rightAction y (diagonalFlow u)
  have hT : Measurable T := (continuous_rightAction _).measurable
  have hν : MeasurePreserving (fun v => a+v) ν ν := by
    refine ⟨(continuous_const_add a).measurable,?_⟩
    apply hf.map_injective
    rw [Measure.map_map hf.measurable (continuous_const_add a).measurable]
    have heq : f ∘ (fun v => a+v) = T ∘ f := funext (orbitQuotientMap_add x u)
    rw [heq,←Measure.map_map hT hf.measurable,hmap]
    exact hA u
  have hz : measureEntropy ν (fun v => a+v) = 0 :=
    measureEntropy_eq_zero_of_isometry ν hν (isometry_add_left a)
  apply le_antisymm _ bot_le
  rw [←hmap]
  exact (measureEntropy_map_semiconj_le ν f hf.measurable (fun v => a+v) T hT
    (orbitQuotientMap_add x u)).trans_eq hz

end PrimeDegreePackets


namespace PrimeDegreePackets

 
def FullDegreeFrame (d : ℕ) := {B : AlgebraicFrame (d+1) //
  ∃ x : X (d+1), (∀ w ∈ rationalPointSpace x, w ≠ 0 → ∀ i, w i ≠ 0) ∧
    Module.finrank ℚ (diagonalRationalAlgebra (rationalPointSpace x)) = d+1 ∧
    x ∈ algebraicFrameClass B}

instance fullDegreeFrame_countable (d : ℕ) : Countable (FullDegreeFrame d) := by
  let : Countable (AlgebraicFrame (d+1)) := by
    unfold AlgebraicFrame Matrix
    infer_instance
  unfold FullDegreeFrame
  infer_instance

def fullDegreeFramePoint {d : ℕ} (B : FullDegreeFrame d) : X (d+1) :=
  B.property.choose

lemma fullDegreeFramePoint_spec {d : ℕ} (B : FullDegreeFrame d) :
    (∀ w ∈ rationalPointSpace (fullDegreeFramePoint B), w ≠ 0 → ∀ i, w i ≠ 0) ∧
    Module.finrank ℚ (diagonalRationalAlgebra (rationalPointSpace (fullDegreeFramePoint B))) = d+1 ∧
    fullDegreeFramePoint B ∈ algebraicFrameClass B.val := B.property.choose_spec

lemma fullDegreeFramePoint_period {d : ℕ} (B : FullDegreeFrame d) :
    IsZLattice ℝ (periodGroup (fullDegreeFramePoint B)).toIntSubmodule :=
  diagonalRationalAlgebra_fullDegree_period _ (fullDegreeFramePoint_spec B).1
    (fullDegreeFramePoint_spec B).2.1

 

theorem fullDegree_mem_range_compact_orbits {d : ℕ} (x : X (d+1))
    (hx : ∀ w ∈ rationalPointSpace x, w ≠ 0 → ∀ i, w i ≠ 0)
    (hdim : Module.finrank ℚ (diagonalRationalAlgebra (rationalPointSpace x)) = d+1) :
    ∃ B : FullDegreeFrame d, x ∈ diagonalOrbit (fullDegreeFramePoint B) := by
  obtain ⟨B,hB⟩ := fullDegree_mem_algebraicFrameClass x hdim
  let C : FullDegreeFrame d := ⟨B,x,hx,hdim,hB⟩
  exact ⟨C,algebraicFrameClass_sameOrbit B (fullDegreeFramePoint_spec C).2.2 hB⟩

lemma diagonalOrbit_rightAction_mem_iff {d : ℕ} (x y : X (d+1)) (u : LogCoordinates d) :
    rightAction y (diagonalFlow u) ∈ diagonalOrbit x ↔ y ∈ diagonalOrbit x := by
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨v-u,?_⟩
    rw [sub_eq_add_neg,orbitMap_add,hv]
    change orbitMap (orbitMap y u) (-u) = y
    rw [←orbitMap_add,add_neg_cancel,orbitMap_zero]
  · rintro ⟨v,rfl⟩
    exact ⟨v+u,orbitMap_add x v u⟩

lemma measurableSet_diagonalOrbit_fullPeriod {d : ℕ} (x : X (d+1))
    [IsZLattice ℝ (periodGroup x).toIntSubmodule] : MeasurableSet (diagonalOrbit x) := by
  rw [←range_orbitQuotientMap]
  exact (orbitQuotientMap_measurableEmbedding x).measurableSet_range

 

theorem ae_not_mem_fullPeriodOrbit_of_positive_entropy {d : ℕ}
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (u : LogCoordinates d)
    (hp : 0 < measureEntropy μ (fun y => rightAction y (diagonalFlow u)))
    (x : X (d+1)) [IsZLattice ℝ (periodGroup x).toIntSubmodule] :
    ∀ᵐ y ∂μ, y ∉ diagonalOrbit x := by
  have he := MeasureTheory.aeconst_of_forall_preimage_smul_ae_eq
    (Multiplicative (LogCoordinates d)) (μ := μ)
    (measurableSet_diagonalOrbit_fullPeriod x).nullMeasurableSet (fun a => by
      apply ae_of_all
      intro y
      apply propext
      exact diagonalOrbit_rightAction_mem_iff x y a.toAdd)
  rcases eventuallyEmptyOrUniv_iff.mp he with hs | hs
  · have hA (v : LogCoordinates d) :
        μ.map (fun y => rightAction y (diagonalFlow v)) = μ :=
      (measurePreserving_smul (Multiplicative.ofAdd v) μ).map_eq
    have hz := measureEntropy_eq_zero_of_ae_mem_fullPeriodOrbit x μ hA hs u
    exact (hp.ne' hz).elim
  · exact hs

 

theorem ae_scalar_diagonalRationalAlgebra_of_positive_entropy (d : ℕ) (hn : (d+1).Prime)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (u : LogCoordinates d)
    (hp : 0 < measureEntropy μ (fun y => rightAction y (diagonalFlow u))) :
    ∀ᵐ x ∂μ, diagonalRationalAlgebra (rationalPointSpace x) = ⊥ := by
  have hA (v : LogCoordinates d) :
      μ.map (fun y => rightAction y (diagonalFlow v)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd v) μ).map_eq
  have hnot : ∀ᵐ x ∂μ, ∀ B : FullDegreeFrame d, x ∉ diagonalOrbit (fullDegreeFramePoint B) := by
    rw [ae_all_iff]
    intro B
    let := fullDegreeFramePoint_period B
    exact ae_not_mem_fullPeriodOrbit_of_positive_entropy μ u hp (fullDegreeFramePoint B)
  filter_upwards [ae_rationalPointSpace_no_coordinate_zero d μ hA,
    ae_point_diagonalRationalAlgebra_prime_degree d hn μ hA,hnot] with x hx hd hn
  rcases hd with hd | hd
  · exact hd
  · obtain ⟨B,hB⟩ := fullDegree_mem_range_compact_orbits x hx hd
    exact (hn B hB).elim

end PrimeDegreePackets
end
end

end OAI
