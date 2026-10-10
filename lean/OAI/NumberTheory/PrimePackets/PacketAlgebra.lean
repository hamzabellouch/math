import Mathlib

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
namespace PrimeDegreePackets

abbrev G (n : ℕ) := Matrix.SpecialLinearGroup (Fin n) ℝ

 
def integralGroup (n : ℕ) : Subgroup (G n) :=
  (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)).range

 
abbrev X (n : ℕ) := Quotient (QuotientGroup.rightRel (integralGroup n))

instance xMeasurableSpace (n : ℕ) : MeasurableSpace (X n) := borel (X n)
instance xBorelSpace (n : ℕ) : BorelSpace (X n) := ⟨rfl⟩

 
def rightAction {n : ℕ} (x : X n) (g : G n) : X n :=
  Quotient.map (fun h => h * g) (by
    intro a b hab
    change (QuotientGroup.rightRel (integralGroup n)) a b at hab
    change (QuotientGroup.rightRel (integralGroup n)) (a * g) (b * g)
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using hab) x

@[simp] theorem rightAction_one {n : ℕ} (x : X n) : rightAction x 1 = x := by
  induction x using Quotient.inductionOn with
  | h a => exact congrArg (Quotient.mk _) (mul_one a)

@[simp] theorem rightAction_mul {n : ℕ} (x : X n) (g h : G n) :
    rightAction (rightAction x g) h = rightAction x (g * h) := by
  induction x using Quotient.inductionOn with
  | h a => exact congrArg (Quotient.mk _) (mul_assoc a g h)

 

def LogHyperplane (n : ℕ) := {u : Fin n → ℝ // ∑ i, u i = 0}

 
def positiveDiagonal (n : ℕ) : Set (G n) :=
  {g | (∀ i j, i ≠ j → g.1 i j = 0) ∧ ∀ i, 0 < g.1 i i}

 
def signMatrices (n : ℕ) : Set (G n) :=
  {g | (∀ i j, i ≠ j → g.1 i j = 0) ∧ ∀ i, g.1 i i = 1 ∨ g.1 i i = -1}

 
def rowLattice {n : ℕ} (g : Matrix (Fin n) (Fin n) ℝ) : Submodule ℤ (Fin n → ℝ) :=
  Submodule.span ℤ (Set.range fun i => g i)

 

structure FullLattice (n : ℕ) (K : Type*) [Field K] [NumberField K] where
  carrier : Submodule ℤ K
  basis : Basis (Fin n) ℤ carrier
  spans : Submodule.span ℚ (carrier : Set K) = ⊤

 
def multiplierOrder {n : ℕ} {K : Type*} [Field K] [NumberField K] (M : FullLattice n K) : AddSubgroup K where
  carrier := {a | ∀ x ∈ M.carrier, a * x ∈ M.carrier}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb x hx
    simpa only [add_mul] using M.carrier.add_mem (ha x hx) (hb x hx)
  neg_mem' := by
    intro a ha x hx
    simpa only [neg_mul] using M.carrier.neg_mem (ha x hx)

 
def integralElements (K : Type*) [Field K] : AddSubgroup K :=
  (integralClosure ℤ K).toSubring.toAddSubgroup

 
def multiplierDiscriminant {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : ℝ :=
  |(NumberField.discr K : ℝ)| *
    ((multiplierOrder M).relIndex (integralElements K) : ℝ) ^ 2

 
abbrev OrderedEmbeddings (n : ℕ) (K : Type*) [Field K] := Fin n ≃ (K →+* ℝ)

 
def embeddingMatrix {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => σ j (M.basis i)

 
def normalizedLattice {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) : Submodule ℤ (Fin n → ℝ) :=
  let B := embeddingMatrix M σ
  rowLattice (|(Matrix.det B)| ^ (-(1 : ℝ) / n) • B)

 

def latticePoint {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) : X n :=
  if h : ∃ g : G n, rowLattice g.1 = normalizedLattice M σ then
    Quotient.mk _ h.choose
  else Quotient.mk _ (1 : G n)

 
abbrev LogCoordinates (d : ℕ) := Fin d → ℝ

 
def diagonalFlow {d : ℕ} (u : LogCoordinates d) : G (d + 1) :=
  ⟨Matrix.diagonal (Fin.snoc (fun i => Real.exp (u i)) (Real.exp (-∑ i, u i))), by
    rw [Matrix.det_diagonal, Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [← Real.exp_sum, ← Real.exp_add, add_neg_cancel, Real.exp_zero]⟩

@[simp] theorem diagonalFlow_zero (d : ℕ) : diagonalFlow (0 : LogCoordinates d) = 1 := by
  apply Subtype.ext
  change Matrix.diagonal _ = (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
  simp
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

@[simp] theorem diagonalFlow_add {d : ℕ} (u v : LogCoordinates d) :
    diagonalFlow (u + v) = diagonalFlow u * diagonalFlow v := by
  apply Subtype.ext
  change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Real.exp_add, Finset.sum_add_distrib, neg_add_rev, mul_comm]
  · simp [Real.exp_add]

 
def orbitMap {d : ℕ} (x : X (d + 1)) (u : LogCoordinates d) : X (d + 1) :=
  rightAction x (diagonalFlow u)

@[simp] theorem orbitMap_zero {d : ℕ} (x : X (d + 1)) : orbitMap x 0 = x := by
  simp [orbitMap]

@[simp] theorem orbitMap_add {d : ℕ} (x : X (d + 1)) (u v : LogCoordinates d) :
    orbitMap x (u + v) = orbitMap (orbitMap x u) v := by
  simp [orbitMap]

 
def periodGroup {d : ℕ} (x : X (d + 1)) : AddSubgroup (LogCoordinates d) where
  carrier := {u | orbitMap x u = x}
  zero_mem' := orbitMap_zero x
  add_mem' := by
    intro u v hu hv
    change orbitMap x (u + v) = x
    rw [orbitMap_add, hu, hv]
  neg_mem' := by
    intro u hu
    have h := congrArg (fun y => orbitMap y (-u)) hu
    rw [← orbitMap_add, add_neg_cancel, orbitMap_zero] at h
    exact h.symm

 
def diagonalOrbit {d : ℕ} (x : X (d + 1)) : Set (X (d + 1)) := Set.range (orbitMap x)

 
def orbitVolume {d : ℕ} (x : X (d + 1)) : ℝ≥0∞ :=
  addCovolume (periodGroup x) (LogCoordinates d) volume

 

def orbitalHaar {d : ℕ} (x : X (d + 1)) : Measure (X (d + 1)) :=
  if h : HasAddFundamentalDomain (periodGroup x) (LogCoordinates d) volume then
    Measure.map (orbitMap x) (volume.restrict h.ExistsIsAddFundamentalDomain.choose)
  else 0

 
def orbitProbability {d : ℕ} (x : X (d + 1)) : Measure (X (d + 1)) :=
  (orbitVolume x)⁻¹ • orbitalHaar x

 
abbrev LocalAlgebra (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K] :=
  Padic p ⊗[ℚ] K

 
def completedLattice {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (M : FullLattice n K) :
    Submodule (PadicInt p) (LocalAlgebra p K) :=
  Submodule.span (PadicInt p)
    ((Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K) '' (M.carrier : Set K))

 
def LocallyHomothetic {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M M' : FullLattice n K) : Prop :=
  ∀ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩
    ∃ c : (LocalAlgebra p K)ˣ,
      (completedLattice p M' : Set (LocalAlgebra p K)) =
        (fun z => (c : LocalAlgebra p K) * z) '' (completedLattice p M : Set (LocalAlgebra p K))

 

def packetOrbits {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d + 1) K) (σ : OrderedEmbeddings (d + 1) K) :
    Set (Set (X (d + 1))) :=
  {O | ∃ M' : FullLattice (d + 1) K, LocallyHomothetic M M' ∧
    ∃ w ∈ signMatrices (d + 1), O = diagonalOrbit (rightAction (latticePoint M' σ) w)}

 

def orbitBasepoint {d : ℕ} {K : Type*} [Field K] [NumberField K]
    {M : FullLattice (d + 1) K} {σ : OrderedEmbeddings (d + 1) K}
    (O : packetOrbits M σ) : X (d + 1) :=
  Classical.epsilon (fun x => diagonalOrbit x = O.1)

 

def packetMeasure {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d + 1) K) (σ : OrderedEmbeddings (d + 1) K) : Measure (X (d + 1)) :=
  (∑' O : packetOrbits M σ, orbitVolume (orbitBasepoint O))⁻¹ •
    Measure.sum (fun O : packetOrbits M σ =>
      orbitVolume (orbitBasepoint O) • orbitProbability (orbitBasepoint O))

 
def IsHaarProbability {n : ℕ} (μ : Measure (X n)) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ g : G n, Measure.map (fun x => rightAction x g) μ = μ

 

def WeakProbabilityConvergence {n : ℕ} (μ : ℕ → Measure (X n)) (m : Measure (X n)) : Prop :=
  (∀ i, IsProbabilityMeasure (μ i)) ∧ IsProbabilityMeasure m ∧
    ∀ f : BoundedContinuousFunction (X n) ℝ,
    Tendsto (fun i => ∫ x, f x ∂μ i) atTop (𝓝 (∫ x, f x ∂m))

end PrimeDegreePackets

universe u
open scoped TensorProduct
open Set Module
namespace PrimeDegreePackets

lemma fullLattice_span_basis {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) :
    Submodule.span ℤ (Set.range fun i => (M.basis i : K)) = M.carrier := by
  rw [show (Set.range fun i => (M.basis i : K)) =
    M.carrier.subtype '' Set.range M.basis by rw [← Set.range_comp]; rfl]
  rw [← Submodule.map_span, M.basis.span_eq, Submodule.map_top, Submodule.range_subtype]

lemma fullLattice_rat_span_basis {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) :
    Submodule.span ℚ (Set.range fun i => (M.basis i : K)) = ⊤ := by
  rw [← Submodule.span_span_of_tower ℤ ℚ, fullLattice_span_basis, M.spans]

 

def fullLatticeRatBasis {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) : Basis (Fin n) ℚ K :=
  basisOfTopLeSpanOfCardEqFinrank (fun i => (M.basis i : K))
    (fullLattice_rat_span_basis M).ge (by simpa using hn.symm)

@[simp] lemma fullLatticeRatBasis_apply {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (i : Fin n) :
    fullLatticeRatBasis M hn i = M.basis i := by
  simp [fullLatticeRatBasis, coe_basisOfTopLeSpanOfCardEqFinrank]

lemma completedLattice_eq_span_basis {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime] :
    completedLattice p M = Submodule.span (PadicInt p)
      (Set.range fun i => (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K)
        (M.basis i)) := by
  let f : K →ₐ[ℚ] LocalAlgebra p K := Algebra.TensorProduct.includeRight
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    rw [← fullLattice_span_basis M] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i,rfl⟩ := hy
      exact Submodule.subset_span ⟨i,rfl⟩
    | zero => simp
    | add x y hx hy ihx ihy =>
      change f (x+y) ∈ _
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
    | smul a x hx ih =>
      change f (a • x) ∈ _
      rw [map_zsmul]
      exact (Submodule.span (PadicInt p) (Set.range fun i => f (M.basis i))).toAddSubgroup.zsmul_mem ih a
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Submodule.subset_span ⟨M.basis i,(M.basis i).property,rfl⟩

lemma completedLattice_basis_independent {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] :
    LinearIndependent (PadicInt p)
      (fun i => (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K) (M.basis i)) := by
  have H := (((fullLatticeRatBasis M hn).baseChange (Padic p)).linearIndependent).restrict_scalars'
    (PadicInt p)
  convert H using 1
  ext i
  simp

 

def completedLatticeBasis {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] : Basis (Fin n) (PadicInt p) (completedLattice p M) :=
  (Basis.span (completedLattice_basis_independent M hn p)).map
    (LinearEquiv.ofEq _ _ (completedLattice_eq_span_basis M p).symm)

@[simp] lemma completedLatticeBasis_coe {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] (i : Fin n) :
    (completedLatticeBasis M hn p i : LocalAlgebra p K) =
      (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K) (M.basis i) := by
  unfold completedLatticeBasis
  rw [Basis.map_apply, Basis.span_apply]
  rfl

 
def completedReduction {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] (k : ℕ) :
    (completedLattice p M) →+ (Fin n → ZMod (p^k)) where
  toFun x i := PadicInt.toZModPow k ((completedLatticeBasis M hn p).equivFun x i)
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

lemma completedReduction_surjective {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] (k : ℕ) :
    Function.Surjective (completedReduction M hn p k) := by
  intro x
  choose y hy using fun i => ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) k) (x i)
  refine ⟨(completedLatticeBasis M hn p).equivFun.symm y,?_⟩
  ext i
  change PadicInt.toZModPow k
    ((completedLatticeBasis M hn p).equivFun
      ((completedLatticeBasis M hn p).equivFun.symm y) i) = x i
  rw [LinearEquiv.apply_symm_apply]
  exact hy i

lemma completedReduction_eq_zero_iff {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] (k : ℕ) (x : completedLattice p M) :
    completedReduction M hn p k x = 0 ↔
      ∃ y : completedLattice p M, x = (p : PadicInt p)^k • y := by
  let b := completedLatticeBasis M hn p
  constructor
  · intro hx
    have h (i : Fin n) : (p : PadicInt p)^k ∣ b.equivFun x i := by
      have H := congrFun hx i
      change PadicInt.toZModPow k (b.equivFun x i) = 0 at H
      rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at H
      exact H
    choose y hy using h
    refine ⟨b.equivFun.symm y,?_⟩
    apply b.equivFun.injective
    ext i
    simpa only [map_smul,LinearEquiv.apply_symm_apply,Pi.smul_apply,smul_eq_mul] using hy i
  · rintro ⟨y,rfl⟩
    ext i
    change PadicInt.toZModPow k (b.equivFun ((p : PadicInt p)^k • y) i) = 0
    simp only [map_smul,Pi.smul_apply,smul_eq_mul,map_mul,map_pow,map_natCast]
    rw [← Nat.cast_pow,ZMod.natCast_self,zero_mul]

 
theorem completedReduction_index {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] (k : ℕ) :
    (completedReduction M hn p k).ker.index = p^(k*n) := by
  rw [AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.mpr (completedReduction_surjective M hn p k)]
  simp [pow_mul]

 
def completionEmbedding {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime] :
    M.carrier →ₗ[ℤ] (completedLattice p M) where
  toFun x := ⟨Algebra.TensorProduct.includeRight x,Submodule.subset_span ⟨x,x.property,rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext
    change (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K) (x+y) = _
    exact map_add _ _ _
  map_smul' a x := by
    apply Subtype.ext
    change (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K) (a • (x : K)) = _
    exact map_zsmul _ _ _

@[simp] lemma completionEmbedding_basis {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] (i : Fin n) :
    completionEmbedding M p (M.basis i) = completedLatticeBasis M hn p i := by
  apply Subtype.ext
  exact (completedLatticeBasis_coe M hn p i).symm

lemma completionEmbedding_coordinates {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] (x : M.carrier) (i : Fin n) :
    (completedLatticeBasis M hn p).equivFun (completionEmbedding M p x) i =
      (M.basis.equivFun x i : PadicInt p) := by
  classical
  conv_lhs => rw [← M.basis.sum_equivFun x]
  simp only [map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply,
    completionEmbedding_basis M hn p, Basis.equivFun_self]
  simp

 

theorem completedReduction_global_surjective {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] (k : ℕ) :
    Function.Surjective ((completedReduction M hn p k).comp
      (completionEmbedding M p).toAddMonoidHom) := by
  intro z
  choose a ha using fun i => ZMod.intCast_surjective (z i)
  refine ⟨M.basis.equivFun.symm a,?_⟩
  ext i
  change PadicInt.toZModPow k
    ((completedLatticeBasis M hn p).equivFun (completionEmbedding M p _) i) = z i
  rw [completionEmbedding_coordinates,LinearEquiv.apply_symm_apply,map_intCast]
  exact ha i

 

theorem completedReduction_simultaneous_surjective
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ j, Fact (p j).Prime]
    (hp : Function.Injective p) (k : ι → ℕ)
    (z : ∀ j, Fin n → ZMod ((p j)^(k j))) :
    ∃ x : M.carrier, ∀ j,
      completedReduction M hn (p j) (k j) (completionEmbedding M (p j) x) = z j := by
  classical
  have hc : Pairwise (fun i j => Nat.Coprime ((p i)^(k i)) ((p j)^(k j))) := by
    intro i j hij
    exact ((Nat.coprime_primes (Fact.out : (p i).Prime)
      (Fact.out : (p j).Prime)).mpr (hp.ne hij)).pow _ _
  let e := ZMod.prodEquivPi (fun j => (p j)^(k j)) hc
  have h (i : Fin n) : ∃ a : ℤ, ∀ j, (a : ZMod ((p j)^(k j))) = z j i := by
    obtain ⟨a,ha⟩ := ZMod.intCast_surjective (e.symm (fun j => z j i))
    refine ⟨a,?_⟩
    have H := congrArg e ha
    rw [RingEquiv.apply_symm_apply] at H
    intro j
    have Hj := congrFun H j
    simpa using Hj
  choose a ha using h
  refine ⟨M.basis.equivFun.symm a,?_⟩
  intro j
  ext i
  change PadicInt.toZModPow (k j)
    ((completedLatticeBasis M hn (p j)).equivFun
      (completionEmbedding M (p j) _) i) = z j i
  rw [completionEmbedding_coordinates,LinearEquiv.apply_symm_apply,map_intCast]
  exact ha i j

 

theorem exists_fullLattice_of_between
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (N : Submodule ℤ K) (hNM : N ≤ M.carrier)
    (q : ℕ) (hq : q ≠ 0) (hMq : ∀ x ∈ M.carrier, (q : ℤ) • x ∈ N) :
    ∃ L : FullLattice n K, L.carrier = N := by
  classical
  have hspan : Submodule.span ℚ (N : Set K) = ⊤ := by
    apply top_unique
    rw [← M.spans]
    apply Submodule.span_le.mpr
    intro x hx
    have H := Submodule.smul_mem (Submodule.span ℚ (N : Set K)) ((q : ℚ)⁻¹)
      (Submodule.subset_span (hMq x hx))
    simpa [Algebra.smul_def, hq] using H
  obtain ⟨m,b⟩ := Submodule.basisOfPidOfLE hNM M.basis
  have hlin : LinearIndependent ℚ (fun i => (b i : K)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp
      (b.linearIndependent.map' N.subtype (Submodule.ker_subtype N))
  have hbspan : Submodule.span ℚ (Set.range fun i => (b i : K)) = ⊤ := by
    have H : Submodule.span ℤ (Set.range fun i => (b i : K)) = N := by
      rw [show (Set.range fun i => (b i : K)) =
        N.subtype '' Set.range b by rw [← Set.range_comp]; rfl]
      rw [← Submodule.map_span,b.span_eq,Submodule.map_top,Submodule.range_subtype]
    rw [← Submodule.span_span_of_tower ℤ ℚ,H,hspan]
  have hmn : m = n := by
    let bQ := Basis.mk hlin hbspan.ge
    have H := Module.finrank_eq_card_basis bQ
    simpa [hn] using H.symm
  exact ⟨⟨N,b.reindex (finCongr hmn),hspan⟩,rfl⟩

 

def residueConditions
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    {ι : Type*} (p : ι → ℕ) [∀ j, Fact (p j).Prime] (k : ι → ℕ)
    (H : ∀ j, AddSubgroup (Fin n → ZMod ((p j)^(k j)))) : Submodule ℤ M.carrier where
  carrier := {x | ∀ j, completedReduction M hn (p j) (k j)
    (completionEmbedding M (p j) x) ∈ H j}
  zero_mem' := by intro j; simp
  add_mem' hx hy := by
    intro j
    simpa only [map_add] using (H j).add_mem (hx j) (hy j)
  smul_mem' a x hx := by
    intro j
    simpa only [map_zsmul] using (H j).zsmul_mem (hx j) a

lemma smul_mem_residueConditions
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ j, Fact (p j).Prime] (k : ι → ℕ)
    (H : ∀ j, AddSubgroup (Fin n → ZMod ((p j)^(k j)))) (x : M.carrier) :
    ((∏ j, (p j)^(k j) : ℕ) : ℤ) • x ∈ residueConditions M hn p k H := by
  classical
  intro j
  have hd : (p j)^(k j) ∣ ∏ j, (p j)^(k j) :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  have hzero : completedReduction M hn (p j) (k j)
      (completionEmbedding M (p j) (((∏ j, (p j)^(k j) : ℕ) : ℤ) • x)) = 0 := by
    ext i
    change PadicInt.toZModPow (k j)
      ((completedLatticeBasis M hn (p j)).equivFun
        (completionEmbedding M (p j) _) i) = 0
    rw [completionEmbedding_coordinates]
    simp only [map_zsmul,Pi.smul_apply,zsmul_eq_mul,Int.cast_mul,Int.cast_natCast,map_mul,map_natCast]
    rw [(ZMod.natCast_eq_zero_iff _ _).mpr hd,zero_mul]
  rw [hzero]
  exact (H j).zero_mem

 

theorem exists_fullLattice_residueConditions
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ j, Fact (p j).Prime] (k : ι → ℕ)
    (H : ∀ j, AddSubgroup (Fin n → ZMod ((p j)^(k j)))) :
    ∃ L : FullLattice n K, L.carrier ≤ M.carrier ∧
      ∀ x : M.carrier, (x : K) ∈ L.carrier ↔
        ∀ j, completedReduction M hn (p j) (k j)
          (completionEmbedding M (p j) x) ∈ H j := by
  classical
  let N := (residueConditions M hn p k H).map M.carrier.subtype
  have hNM : N ≤ M.carrier := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Submodule.mem_map.mp hx
    exact y.property
  have hq : (∏ j, (p j)^(k j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => pow_ne_zero _ (Fact.out : (p j).Prime).ne_zero)
  obtain ⟨L,hL⟩ := exists_fullLattice_of_between M hn N hNM _ hq (by
    intro x hx
    exact Submodule.mem_map.mpr ⟨((∏ j, (p j)^(k j) : ℕ) : ℤ) • (⟨x,hx⟩ : M.carrier),
      smul_mem_residueConditions M hn p k H ⟨x,hx⟩,rfl⟩)
  refine ⟨L,hL ▸ hNM,?_⟩
  intro x
  rw [hL]
  change (x : K) ∈ (residueConditions M hn p k H).map M.carrier.subtype ↔ _
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y,hy,hxy⟩
    have : y = x := Subtype.ext hxy
    subst y
    exact hy
  · intro hx
    exact ⟨x,hx,rfl⟩

 

theorem residueConditions_surjective
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ j, Fact (p j).Prime]
    (hp : Function.Injective p) (k : ι → ℕ)
    (H : ∀ j, AddSubgroup (Fin n → ZMod ((p j)^(k j))))
    (z : ∀ j, Fin n → ZMod ((p j)^(k j))) (hz : ∀ j, z j ∈ H j) :
    ∃ x ∈ residueConditions M hn p k H, ∀ j,
      completedReduction M hn (p j) (k j) (completionEmbedding M (p j) x) = z j := by
  obtain ⟨x,hx⟩ := completedReduction_simultaneous_surjective M hn p hp k z
  exact ⟨x,fun j => (hx j).symm ▸ hz j,hx⟩

 

lemma completedReduction_mem_image_iff
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] (k : ℕ)
    (N : Submodule (PadicInt p) (completedLattice p M))
    (hN : ∀ y, (p : PadicInt p)^k • y ∈ N) (x : completedLattice p M) :
    completedReduction M hn p k x ∈ N.toAddSubgroup.map (completedReduction M hn p k) ↔
      x ∈ N := by
  constructor
  · rintro ⟨y,hy,hyx⟩
    have H : completedReduction M hn p k (x-y) = 0 := by rw [map_sub,hyx,sub_self]
    obtain ⟨z,hz⟩ := (completedReduction_eq_zero_iff M hn p k _).mp H
    have hd : x-y ∈ N := hz ▸ hN z
    simpa only [sub_add_cancel] using N.add_mem hd hy
  · intro hx
    exact ⟨x,hx,rfl⟩

 
lemma completedLattice_mono
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    {M N : FullLattice n K} (hMN : M.carrier ≤ N.carrier)
    (p : ℕ) [Fact p.Prime] : completedLattice p M ≤ completedLattice p N :=
  Submodule.span_mono (Set.image_mono hMN)

 

lemma completedLattice_smul_mem
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    {M N : FullLattice n K} (q : ℕ)
    (hMN : ∀ x ∈ M.carrier, (q : ℤ) • x ∈ N.carrier)
    (p : ℕ) [Fact p.Prime] {y : LocalAlgebra p K} (hy : y ∈ completedLattice p M) :
    (q : PadicInt p) • y ∈ completedLattice p N := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z,hz,rfl⟩ := hx
    have H : (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K)
        ((q : ℤ) • z) ∈ completedLattice p N := Submodule.subset_span
      (show (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K)
          ((q : ℤ) • z) ∈
        (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K) ''
          (N.carrier : Set K) from ⟨(q : ℤ) • z,hMN z hz,rfl⟩)
    simpa only [map_zsmul, map_nsmul, Nat.cast_smul_eq_nsmul] using H
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [smul_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
    rw [smul_comm]
    exact Submodule.smul_mem _ _ ih

 

lemma completedLattice_primePower_mem
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    {M N : FullLattice n K} (q : ℕ)
    (hMN : ∀ x ∈ M.carrier, (q : ℤ) • x ∈ N.carrier)
    (p : ℕ) [Fact p.Prime] (k r : ℕ) (hqr : q = p^k*r)
    (hr : Nat.Coprime p r) {y : LocalAlgebra p K} (hy : y ∈ completedLattice p M) :
    (p : PadicInt p)^k • y ∈ completedLattice p N := by
  have hu : IsUnit (r : PadicInt p) := PadicInt.isUnit_iff.mpr
    (PadicInt.norm_natCast_eq_one_iff.mpr hr)
  obtain ⟨u,hu⟩ := hu
  have H := Submodule.smul_mem (completedLattice p N) (↑(u⁻¹) : PadicInt p)
    (completedLattice_smul_mem q hMN p hy)
  rw [smul_smul,hqr,Nat.cast_mul,Nat.cast_pow,← hu] at H
  have he : (↑(u⁻¹) : PadicInt p) * ((p : PadicInt p)^k * u) = (p : PadicInt p)^k := by
    rw [mul_left_comm,Units.inv_mul,mul_one]
  rwa [he] at H

lemma prime_coprime_other_factors {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ j, Fact (p j).Prime] (hp : Function.Injective p) (k : ι → ℕ) (j : ι) :
    Nat.Coprime (p j) (∏ i ∈ Finset.univ.erase j, (p i)^(k i)) := by
  apply Nat.Coprime.prod_right
  intro i hi
  apply Nat.Coprime.pow_right
  exact (Nat.coprime_primes (Fact.out : (p j).Prime) (Fact.out : (p i).Prime)).mpr
    (hp.ne (Finset.ne_of_mem_erase hi).symm)

 

theorem patch_fullLattice_completions
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ j, Fact (p j).Prime]
    (hp : Function.Injective p) (k : ι → ℕ)
    (N : ∀ j, Submodule (PadicInt (p j)) (LocalAlgebra (p j) K))
    (hNM : ∀ j, N j ≤ completedLattice (p j) M)
    (hNpow : ∀ j y, y ∈ completedLattice (p j) M → (p j : PadicInt (p j))^(k j) • y ∈ N j) :
    ∃ L : FullLattice n K, L.carrier ≤ M.carrier ∧
      (∀ j, completedLattice (p j) L = N j) ∧
      ∀ (r : ℕ) (hr : r.Prime), letI : Fact r.Prime := ⟨hr⟩;
        r ∉ Set.range p → completedLattice r L = completedLattice r M := by
  classical
  let R (j : ι) := (N j).comap (completedLattice (p j) M).subtype
  let H (j : ι) := (R j).toAddSubgroup.map (completedReduction M hn (p j) (k j))
  have hR (j : ι) (y : completedLattice (p j) M) : (p j : PadicInt (p j))^(k j) • y ∈ R j :=
    hNpow j y y.property
  have hred (j : ι) (x : completedLattice (p j) M) :
      completedReduction M hn (p j) (k j) x ∈ H j ↔ (x : LocalAlgebra (p j) K) ∈ N j :=
    completedReduction_mem_image_iff M hn (p j) (k j) (R j) (hR j) x
  obtain ⟨L,hLM,hL⟩ := exists_fullLattice_residueConditions M hn p k H
  let q := ∏ j, (p j)^(k j)
  have hmul (x : K) (hx : x ∈ M.carrier) : (q : ℤ) • x ∈ L.carrier := by
    exact (hL ((q : ℤ) • (⟨x,hx⟩ : M.carrier))).mpr
      (smul_mem_residueConditions M hn p k H ⟨x,hx⟩)
  have hL' (x : M.carrier) : (x : K) ∈ L.carrier ↔
      ∀ j, (completionEmbedding M (p j) x : LocalAlgebra (p j) K) ∈ N j := by
    rw [hL x]
    exact forall_congr' (fun j => hred j _)
  have hle (j : ι) : completedLattice (p j) L ≤ N j := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    exact (hL' ⟨x,hLM hx⟩).mp hx j
  refine ⟨L,hLM,?_,?_⟩
  · intro j
    apply le_antisymm (hle j)
    intro y hy
    let yM : completedLattice (p j) M := ⟨y,hNM j hy⟩
    let z : ∀ i, Fin n → ZMod ((p i)^(k i)) :=
      Pi.single j (completedReduction M hn (p j) (k j) yM)
    have hz : ∀ i, z i ∈ H i := by
      intro i
      by_cases hij : i = j
      · subst i
        simpa only [z,Pi.single_eq_same] using (hred j yM).mpr hy
      · simpa only [z,Pi.single_eq_of_ne hij] using (H i).zero_mem
    obtain ⟨x,hx,hxz⟩ := residueConditions_surjective M hn p hp k H z hz
    have hxL : (x : K) ∈ L.carrier := (hL x).mpr hx
    have hker : completedReduction M hn (p j) (k j)
        (yM - completionEmbedding M (p j) x) = 0 := by
      rw [map_sub,hxz j]
      simp only [z,Pi.single_eq_same,sub_self]
    obtain ⟨a,ha⟩ := (completedReduction_eq_zero_iff M hn (p j) (k j) _).mp hker
    have hpa : (p j : PadicInt (p j))^(k j) • (a : LocalAlgebra (p j) K) ∈
        completedLattice (p j) L := by
      apply completedLattice_primePower_mem q hmul (p j) (k j)
        (∏ i ∈ Finset.univ.erase j, (p i)^(k i))
      · exact (Finset.mul_prod_erase Finset.univ (fun i => (p i)^(k i))
          (Finset.mem_univ j)).symm
      · exact prime_coprime_other_factors p hp k j
      · exact a.property
    have had : y - (completionEmbedding M (p j) x : LocalAlgebra (p j) K) ∈
        completedLattice (p j) L := by
      have he := congrArg Subtype.val ha
      change y - (completionEmbedding M (p j) x : LocalAlgebra (p j) K) =
        (p j : PadicInt (p j))^(k j) • (a : LocalAlgebra (p j) K) at he
      rw [he]
      exact hpa
    have hxe : (completionEmbedding M (p j) x : LocalAlgebra (p j) K) ∈
        completedLattice (p j) L := Submodule.subset_span ⟨x,hxL,rfl⟩
    simpa only [sub_add_cancel] using (completedLattice (p j) L).add_mem had hxe
  · intro r hr
    let : Fact r.Prime := ⟨hr⟩
    intro hnot
    apply le_antisymm (completedLattice_mono hLM r)
    intro y hy
    have hc : Nat.Coprime r q := by
      apply Nat.Coprime.prod_right
      intro j _
      apply Nat.Coprime.pow_right
      apply (Nat.coprime_primes hr (Fact.out : (p j).Prime)).mpr
      exact fun he => hnot ⟨j,he.symm⟩
    simpa only [pow_zero,one_smul] using
      completedLattice_primePower_mem q hmul r 0 q (by simp) hc hy

lemma rat_integral_of_padic_integral (q : ℚ)
    (h : ∀ (p : ℕ) (hp : p.Prime), let : Fact p.Prime := ⟨hp⟩;
      ‖(q : Padic p)‖ ≤ 1) : ∃ z : ℤ, (z : ℚ) = q := by
  suffices hd : q.den = 1 from ⟨q.num, (Rat.den_eq_one_iff q).mp hd⟩
  by_contra hd
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd
  let : Fact p.Prime := ⟨hp⟩
  have hdn : (q.den : Padic p) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
  have hdlt : ‖(q.den : Padic p)‖ < 1 := Padic.norm_natCast_lt_one_iff.mpr hpd
  have hn : ‖(q.num : Padic p)‖ = 1 := by
    rw [← norm_natAbs]
    exact Padic.norm_natCast_eq_one_iff.mpr (q.reduced.coprime_dvd_right hpd).symm
  have hq := h p hp
  change ‖(q : Padic p)‖ ≤ 1 at hq
  rw [Rat.cast_def, norm_div, hn] at hq
  have := (one_lt_div (norm_pos_iff.mpr hdn)).mpr hdlt
  exact (not_lt_of_ge hq) this

 
lemma fullLatticeRatBasis_repr_integral {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) {x : K} (hx : x ∈ M.carrier)
    (i : Fin n) : ∃ z : ℤ, (fullLatticeRatBasis M hn).repr x i = z := by
  rw [← fullLattice_span_basis M] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      change ∃ z : ℤ, (fullLatticeRatBasis M hn).repr (M.basis j) i = z
      rw [← fullLatticeRatBasis_apply M hn j, Basis.repr_self_apply]
      by_cases h : j = i
      · exact ⟨1, by simp [h]⟩
      · exact ⟨0, by simp [h]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      exact ⟨a + b, by simp [ha, hb]⟩
  | smul a x hx ih =>
      obtain ⟨b, hb⟩ := ih
      refine ⟨a * b, ?_⟩
      rw [map_zsmul, Finsupp.smul_apply, hb]
      simp

 

lemma completedLattice_coordinate_integral {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] {x : LocalAlgebra p K} (hx : x ∈ completedLattice p M)
    (i : Fin n) : ∃ a : PadicInt p,
      ((fullLatticeRatBasis M hn).baseChange (Padic p)).repr x i = (a : Padic p) := by
  let b := (fullLatticeRatBasis M hn).baseChange (Padic p)
  let c := (b.coord i).restrictScalars (PadicInt p)
  change ∃ a : PadicInt p, c x = (a : Padic p)
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      obtain ⟨a, ha⟩ := fullLatticeRatBasis_repr_integral M hn hz i
      refine ⟨a, ?_⟩
      change ((fullLatticeRatBasis M hn).baseChange (Padic p)).repr
        (1 ⊗ₜ[ℚ] z) i = ((a : PadicInt p) : Padic p)
      rw [Basis.baseChange_repr_tmul, ha]
      simp
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      exact ⟨a + b, by simp [ha, hb]⟩
  | smul a x hx ih =>
      obtain ⟨b, hb⟩ := ih
      refine ⟨a * b, ?_⟩
      rw [map_smul, hb]
      simp [Algebra.smul_def]

 
theorem mem_fullLattice_iff_forall_completed {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (x : K) :
    x ∈ M.carrier ↔ ∀ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩;
      Algebra.TensorProduct.includeRight (R := ℚ) (A := Padic p) x ∈ completedLattice p M := by
  constructor
  · intro hx p hp
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  · intro hx
    have hint (i : Fin n) : ∃ a : ℤ, (a : ℚ) = (fullLatticeRatBasis M hn).repr x i := by
      apply rat_integral_of_padic_integral
      intro p hp
      let : Fact p.Prime := ⟨hp⟩
      obtain ⟨a, ha⟩ := completedLattice_coordinate_integral M hn p (hx p hp) i
      simp only [Algebra.TensorProduct.includeRight_apply, Basis.baseChange_repr_tmul,
        Algebra.smul_def, mul_one] at ha
      change ‖((algebraMap ℚ (Padic p)) ((fullLatticeRatBasis M hn).repr x i))‖ ≤ 1
      rw [ha]
      exact a.property
    choose a ha using hint
    have hsum : x = ∑ i, a i • (M.basis i : K) := by
      have h := (fullLatticeRatBasis M hn).sum_repr x
      simp only [← funext_iff] at ha
      rw [← h]
      apply Finset.sum_congr rfl
      intro i _
      rw [← congrFun ha i, fullLatticeRatBasis_apply]
      simp [Algebra.smul_def]
    rw [hsum]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (M.basis i).property)

 

theorem fullLattice_carrier_eq_of_completions_eq
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (h : ∀ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩;
      completedLattice p M = completedLattice p N) : M.carrier = N.carrier := by
  ext x
  rw [mem_fullLattice_iff_forall_completed M hn x,mem_fullLattice_iff_forall_completed N hn x]
  exact forall_congr' (fun p => forall_congr' (fun hp => by rw [h p hp]))

 

theorem patch_fullLattice_completions_unique
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ j, Fact (p j).Prime]
    (hp : Function.Injective p) (k : ι → ℕ)
    (N : ∀ j, Submodule (PadicInt (p j)) (LocalAlgebra (p j) K))
    (hNM : ∀ j, N j ≤ completedLattice (p j) M)
    (hNpow : ∀ j y, y ∈ completedLattice (p j) M → (p j : PadicInt (p j))^(k j) • y ∈ N j) :
    ∃ L : FullLattice n K, L.carrier ≤ M.carrier ∧
      (∀ j, completedLattice (p j) L = N j) ∧
      (∀ (r : ℕ) (hr : r.Prime), letI : Fact r.Prime := ⟨hr⟩;
        r ∉ Set.range p → completedLattice r L = completedLattice r M) ∧
      ∀ L' : FullLattice n K,
        (∀ j, completedLattice (p j) L' = N j) →
        (∀ (r : ℕ) (hr : r.Prime), letI : Fact r.Prime := ⟨hr⟩;
          r ∉ Set.range p → completedLattice r L' = completedLattice r M) →
        L'.carrier = L.carrier := by
  obtain ⟨L,hLM,hL,hLoff⟩ := patch_fullLattice_completions M hn p hp k N hNM hNpow
  refine ⟨L,hLM,hL,hLoff,?_⟩
  intro L' hL' hL'off
  apply fullLattice_carrier_eq_of_completions_eq L' L hn
  intro r hr
  let : Fact r.Prime := ⟨hr⟩
  by_cases hs : r ∈ Set.range p
  · obtain ⟨j,rfl⟩ := hs
    exact (hL' j).trans (hL j).symm
  · exact (hL'off r hr hs).trans (hLoff r hr hs).symm

open scoped NumberField Pointwise nonZeroDivisors
open NumberField

 
def completedFractionalIdeal {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I : FractionalIdeal (𝓞 K)⁰ K) :
    Submodule (PadicInt p) (LocalAlgebra p K) :=
  Submodule.span (PadicInt p)
    ((Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K) '' (I : Set K))

lemma completedFractionalIdeal_mono {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] {I J : FractionalIdeal (𝓞 K)⁰ K} (h : I ≤ J) :
    completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) ≤ completedFractionalIdeal p J :=
  Submodule.span_mono (Set.image_mono h)

lemma completedFractionalIdeal_fg {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I : FractionalIdeal (𝓞 K)⁰ K) :
    (completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K)).FG := by
  classical
  have hI := (FractionalIdeal.fg_of_isNoetherianRing (le_refl (𝓞 K)⁰) I).restrictScalars (R := ℤ)
  obtain ⟨s,hs⟩ := hI
  let f : K →ₐ[ℚ] LocalAlgebra p K := Algebra.TensorProduct.includeRight
  refine ⟨s.image f, le_antisymm ?_ ?_⟩
  · apply Submodule.span_le.mpr
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    apply Submodule.subset_span
    refine ⟨x,?_,rfl⟩
    have hx' : x ∈ Submodule.span ℤ (s : Set K) := Submodule.subset_span hx
    rwa [hs] at hx'
  · apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    change x ∈ (I : Submodule (𝓞 K) K).restrictScalars ℤ at hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨y,hy,rfl⟩))
    | zero => simp
    | add x y hx hy ihx ihy =>
      change f (x+y) ∈ _
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
    | smul a x hx ih =>
      change f (a • x) ∈ _
      rw [map_zsmul]
      have H := Submodule.smul_mem
        (Submodule.span (PadicInt p) ((s.image f : Finset (LocalAlgebra p K)) : Set (LocalAlgebra p K)))
        (a : PadicInt p) ih
      simp only [Int.cast_smul_eq_zsmul, f] at H
      exact H

lemma completedFractionalIdeal_add {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I J : FractionalIdeal (𝓞 K)⁰ K) :
    completedFractionalIdeal p (I+J) = completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) ⊔ completedFractionalIdeal p J := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨a,ha,b,hb,rfl⟩ := (FractionalIdeal.mem_add I J x).mp hx
    rw [map_add]
    exact Submodule.add_mem _ ((show completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) ≤ _ from le_sup_left) (Submodule.subset_span ⟨a,ha,rfl⟩))
      ((show completedFractionalIdeal p J ≤ _ from le_sup_right) (Submodule.subset_span ⟨b,hb,rfl⟩))
  · apply sup_le
    · exact completedFractionalIdeal_mono p (show I ≤ I+J from le_sup_left)
    · exact completedFractionalIdeal_mono p (show J ≤ I+J from le_sup_right)

lemma completedFractionalIdeal_zero {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] : completedFractionalIdeal p (0 : FractionalIdeal (𝓞 K)⁰ K) = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨x,hx,rfl⟩
  have hx' : x = 0 := (FractionalIdeal.mem_zero_iff (𝓞 K)⁰).mp hx
  simp [hx']

lemma completedFractionalIdeal_ne_bot {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) ≠ ⊥ := by
  intro h
  apply hI
  apply le_antisymm _ bot_le
  intro x hx
  have H : (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K) x ∈
      completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) := Submodule.subset_span ⟨x,hx,rfl⟩
  rw [h] at H
  have H' : (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K) x = 0 := H
  apply (FractionalIdeal.mem_zero_iff (𝓞 K)⁰).mpr
  exact (RingHom.injective (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K).toRingHom).eq_iff.mp (by simpa using H')

 

lemma completedFractionalIdeal_singleton_mul {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I : FractionalIdeal (𝓞 K)⁰ K) (a : K) :
    completedFractionalIdeal p (FractionalIdeal.spanSingleton (𝓞 K)⁰ a * I) =
      (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K) a •
        completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) := by
  unfold completedFractionalIdeal
  rw [← Submodule.span_smul]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_smul_set]
  constructor
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨z,hz,hyz⟩ := (FractionalIdeal.mem_singleton_mul).mp hy
    subst y
    exact ⟨_,⟨z,hz,rfl⟩,by simp [smul_eq_mul]⟩
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    refine ⟨a*z,?_,by simp [smul_eq_mul]⟩
    exact (FractionalIdeal.mem_singleton_mul).mpr ⟨z,hz,rfl⟩

lemma completedFractionalIdeal_nat_mul {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I : FractionalIdeal (𝓞 K)⁰ K) (q : ℕ) :
    completedFractionalIdeal p (FractionalIdeal.spanSingleton (𝓞 K)⁰ (q : K) * I) =
      (q : PadicInt p) • completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [completedFractionalIdeal_singleton_mul]
  ext x
  simp only [Submodule.mem_smul_pointwise_iff_exists, map_natCast,
    Nat.cast_smul_eq_nsmul]

 

theorem completedFractionalIdeal_principal {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) =
      (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K) a •
        completedFractionalIdeal p (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  let P : FractionalIdeal (𝓞 K)⁰ K := FractionalIdeal.spanSingleton (𝓞 K)⁰ (p : K) * I
  have hPI : P ≤ I := by
    apply FractionalIdeal.spanSingleton_mul_le_iff.mpr
    intro x hx
    have H := (I : Submodule (𝓞 K) K).toAddSubgroup.nsmul_mem hx p
    simp only [nsmul_eq_mul] at H
    exact H
  have hpn : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hP : P ≠ 0 := mul_ne_zero (FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr hpn) hI
  obtain ⟨a,ha⟩ := IsDedekindDomain.exists_add_spanSingleton_mul_eq
    (b := (1 : FractionalIdeal (𝓞 K)⁰ K)) hPI hP one_ne_zero
  rw [mul_one] at ha
  have hA : completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) =
      completedFractionalIdeal p (FractionalIdeal.spanSingleton (𝓞 K)⁰ a) := by
    have hle : completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) ≤
        completedFractionalIdeal p (FractionalIdeal.spanSingleton (𝓞 K)⁰ a) ⊔
        Ideal.span {(p : PadicInt p)} • completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [Submodule.ideal_span_singleton_smul, ← completedFractionalIdeal_nat_mul]
      rw [← completedFractionalIdeal_add, add_comm]
      exact (congrArg (completedFractionalIdeal p) ha).ge
    apply le_antisymm
    · apply Submodule.le_of_le_smul_of_le_jacobson_bot (completedFractionalIdeal_fg p I) _ hle
      rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top, PadicInt.maximalIdeal_eq_span_p]
    · apply completedFractionalIdeal_mono p
      rw [← ha]
      exact le_sup_right
  have ha0 : a ≠ 0 := by
    intro he
    rw [he,FractionalIdeal.spanSingleton_zero,completedFractionalIdeal_zero] at hA
    exact completedFractionalIdeal_ne_bot p hI hA
  refine ⟨a,ha0,?_⟩
  rw [hA, ← completedFractionalIdeal_singleton_mul,mul_one]

lemma completedFractionalIdeal_mul_mem {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I J : FractionalIdeal (𝓞 K)⁰ K)
    {x y : LocalAlgebra p K} (hx : x ∈ completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K))
    (hy : y ∈ completedFractionalIdeal p J) : x*y ∈ completedFractionalIdeal p (I*J) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a,ha,rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b,hb,rfl⟩ := hy
      rw [← map_mul]
      exact Submodule.subset_span ⟨a*b,FractionalIdeal.mul_mem_mul ha hb,rfl⟩
    | zero => simp
    | add x y hx hy ihx ihy =>
      rw [mul_add]
      exact Submodule.add_mem _ ihx ihy
    | smul c x hx ih =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ c ih
  | zero => simp
  | add x y hx hy ihx ihy =>
    rw [add_mul]
    exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c ih

lemma completedFractionalIdeal_mul {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I J : FractionalIdeal (𝓞 K)⁰ K) :
    completedFractionalIdeal p (I*J) = completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) * completedFractionalIdeal p J := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    refine FractionalIdeal.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [map_mul]
      exact Submodule.mul_mem_mul (Submodule.subset_span ⟨a,ha,rfl⟩)
        (Submodule.subset_span ⟨b,hb,rfl⟩)
    · intro x y hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  · exact Submodule.mul_le.mpr (fun _ hx _ hy => completedFractionalIdeal_mul_mem p I J hx hy)

 

def completedMaximalOrder {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] : Subalgebra (PadicInt p) (LocalAlgebra p K) where
  carrier := completedFractionalIdeal p (1 : FractionalIdeal (𝓞 K)⁰ K)
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  mul_mem' hx hy := by
    have H := completedFractionalIdeal_mul_mem p 1 1 hx hy
    simp only [one_mul] at H
    exact H
  algebraMap_mem' a := by
    have h1 : (1 : LocalAlgebra p K) ∈ completedFractionalIdeal p (1 : FractionalIdeal (𝓞 K)⁰ K) := by
      exact Submodule.subset_span ⟨1,(FractionalIdeal.mem_one_iff (𝓞 K)⁰).mpr ⟨1,map_one _⟩,map_one _⟩
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem (completedFractionalIdeal p (1 : FractionalIdeal (𝓞 K)⁰ K)) a h1

@[simp] lemma completedMaximalOrder_toSubmodule {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] :
    (completedMaximalOrder (K := K) p).toSubmodule = completedFractionalIdeal p (1 : FractionalIdeal (𝓞 K)⁰ K) := rfl

 
theorem completedMaximalOrder_unit_of_smul_eq {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (u : (LocalAlgebra p K)ˣ)
    (h : (u : LocalAlgebra p K) • (completedMaximalOrder (K := K) p).toSubmodule =
      (completedMaximalOrder (K := K) p).toSubmodule) :
    ∃ v : (completedMaximalOrder (K := K) p)ˣ,
      ((v : completedMaximalOrder (K := K) p) : LocalAlgebra p K) = u := by
  let R := completedMaximalOrder (K := K) p
  have hu : (u : LocalAlgebra p K) ∈ R := by
    rw [← Subalgebra.mem_toSubmodule,← h]
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨1,R.one_mem,by simp⟩
  have hui : (↑(u⁻¹) : LocalAlgebra p K) ∈ R := by
    obtain ⟨x,hx,hxu⟩ := (Submodule.mem_smul_pointwise_iff_exists 1 (↑u) R.toSubmodule).mp
      (h.symm ▸ R.one_mem)
    have he : x = (↑(u⁻¹) : LocalAlgebra p K) := by
      change (u : LocalAlgebra p K) * x = 1 at hxu
      have H := congrArg (fun y : LocalAlgebra p K => ↑(u⁻¹) * y) hxu
      simpa only [smul_eq_mul,← mul_assoc,Units.inv_mul,one_mul,mul_one] using H
    exact he ▸ hx
  refine ⟨⟨⟨u,hu⟩,⟨↑(u⁻¹),hui⟩,?_,?_⟩,rfl⟩ <;>
    apply Subtype.ext <;> simp

def saturationFractionalIdeal {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : FractionalIdeal (𝓞 K)⁰ K :=
  ⟨Submodule.span (𝓞 K) (M.carrier : Set K), FractionalIdeal.isFractional_of_fg <| by
    rw [← fullLattice_span_basis M, Submodule.span_span_of_tower]
    exact Submodule.fg_span (Set.finite_range _)⟩

lemma saturationFractionalIdeal_ne_zero {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : saturationFractionalIdeal M ≠ 0 := by
  intro h
  have hbot : M.carrier = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hx' : x ∈ saturationFractionalIdeal M := Submodule.subset_span hx
    simpa [h] using hx'
  have H : (⊥ : Submodule ℚ K) = ⊤ := by simpa [hbot] using M.spans
  exact bot_ne_top H

 
def fractionalIdealFullLattice {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : Module.finrank ℚ K = n) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FullLattice n K where
  carrier := (I : Submodule (𝓞 K) K).restrictScalars ℤ
  basis := (fractionalIdealBasis K I.1).reindex (Fintype.equivFinOfCardEq (by
    rw [← Module.finrank_eq_card_basis (basisOfFractionalIdeal K I)]
    exact hn))
  spans := by
    have h : ((I : Submodule (𝓞 K) K).restrictScalars ℤ : Set K) =
        (Submodule.span ℤ (Set.range (basisOfFractionalIdeal K I)) : Set K) := by
      ext x; exact (mem_span_basisOfFractionalIdeal (I := I) (x := x)).symm
    rw [h,Submodule.span_span_of_tower,(basisOfFractionalIdeal K I).span_eq]

@[simp] lemma completedLattice_fractionalIdealFullLattice
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : Module.finrank ℚ K = n) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℕ) [Fact p.Prime] :
    completedLattice p (fractionalIdealFullLattice hn I) = completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) := rfl

 
theorem completed_saturation {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime] :
    completedFractionalIdeal p (saturationFractionalIdeal M) =
      (completedMaximalOrder (K := K) p).toSubmodule * completedLattice p M := by
  let f : K →ₐ[ℚ] LocalAlgebra p K := Algebra.TensorProduct.includeRight
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    change x ∈ Submodule.span (𝓞 K) (M.carrier : Set K) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      have h1 : (1 : LocalAlgebra p K) ∈ (completedMaximalOrder (K := K) p).toSubmodule :=
        (completedMaximalOrder (K := K) p).one_mem
      have H := Submodule.mul_mem_mul h1
        (Submodule.subset_span ⟨x,hx,rfl⟩ : f x ∈ completedLattice p M)
      simp only [one_mul] at H
      exact H
    | zero => simp
    | add x y hx hy ihx ihy =>
      change f (x+y) ∈ _
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
    | smul a x hx ih =>
      change f ((a : K) * x) ∈ _
      rw [map_mul]
      have ha : f a ∈ completedFractionalIdeal p (1 : FractionalIdeal (𝓞 K)⁰ K) :=
        Submodule.subset_span ⟨a,(FractionalIdeal.mem_one_iff (𝓞 K)⁰).mpr ⟨a,rfl⟩,rfl⟩
      have H := Submodule.mul_mem_mul ha ih
      rw [← mul_assoc] at H
      have hR : (completedMaximalOrder (K := K) p).toSubmodule *
          (completedMaximalOrder (K := K) p).toSubmodule =
          (completedMaximalOrder (K := K) p).toSubmodule := by
        simp only [completedMaximalOrder_toSubmodule,← completedFractionalIdeal_mul,one_mul]
      rw [show completedFractionalIdeal p (1 : FractionalIdeal (𝓞 K)⁰ K) =
        (completedMaximalOrder (K := K) p).toSubmodule from rfl,hR] at H
      exact H
  · apply Submodule.mul_le.mpr
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a,ha,rfl⟩ := hx
      obtain ⟨a,rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 K)⁰).mp ha
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨b,hb,rfl⟩ := hy
        rw [← map_mul]
        exact Submodule.subset_span ⟨(a : K)*b,
          Submodule.smul_mem _ a (Submodule.subset_span hb),rfl⟩
      | zero => simp
      | add x y hx hy ihx ihy =>
        rw [mul_add]
        exact Submodule.add_mem _ ihx ihy
      | smul c x hx ih =>
        rw [mul_smul_comm]
        exact Submodule.smul_mem _ c ih
    | zero => simp
    | add x y hx hy ihx ihy =>
      rw [add_mul]
      exact Submodule.add_mem _ ihx ihy
    | smul c x hx ih =>
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ c ih

 
theorem fractionalIdeal_eq_of_completions_eq {K : Type*} [Field K] [NumberField K]
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (h : ∀ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩;
      completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) =
        completedFractionalIdeal p (J : FractionalIdeal (𝓞 K)⁰ K)) :
    (I : FractionalIdeal (𝓞 K)⁰ K) = J := by
  have H := fullLattice_carrier_eq_of_completions_eq
    (fractionalIdealFullLattice rfl I) (fractionalIdealFullLattice rfl J) rfl h
  exact FractionalIdeal.coeToSubmodule_injective (Submodule.ext (fun x =>
    show x ∈ (I : Submodule (𝓞 K) K) ↔ x ∈ (J : Submodule (𝓞 K) K) from
      Iff.of_eq (congrArg (fun A : Submodule ℤ K => x ∈ A) H)))

lemma completedMaximalOrder_unit_smul {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (v : (completedMaximalOrder (K := K) p)ˣ) :
    ((v : completedMaximalOrder (K := K) p) : LocalAlgebra p K) •
        (completedMaximalOrder (K := K) p).toSubmodule =
      (completedMaximalOrder (K := K) p).toSubmodule := by
  let R := completedMaximalOrder (K := K) p
  ext x
  constructor
  · intro hx
    obtain ⟨y,hy,rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    exact R.mul_mem (v : R).property hy
  · intro hx
    apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
    refine ⟨((v⁻¹ : Rˣ) : R) * x,R.mul_mem ((v⁻¹ : Rˣ) : R).property hx,?_⟩
    change (↑(v : R) : LocalAlgebra p K) * (↑(↑(v⁻¹) : R) * x) = x
    have hv : (↑(v : R) : LocalAlgebra p K) * (↑(↑(v⁻¹) : R) : LocalAlgebra p K) = 1 := by
      exact congrArg (fun r : R => (r : LocalAlgebra p K)) v.mul_inv
    rw [← mul_assoc, hv, one_mul]

lemma local_saturation_homothety {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (p : ℕ) [Fact p.Prime]
    (c : (LocalAlgebra p K)ˣ)
    (h : completedLattice p N = (c : LocalAlgebra p K) • completedLattice p M) :
    completedFractionalIdeal p (saturationFractionalIdeal N) =
      (c : LocalAlgebra p K) • completedFractionalIdeal p (saturationFractionalIdeal M) := by
  rw [completed_saturation,completed_saturation,h,mul_smul_comm]

 

theorem local_scalar_choice {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (p : ℕ) [Fact p.Prime]
    (i j c : (LocalAlgebra p K)ˣ)
    (hi : completedFractionalIdeal p (saturationFractionalIdeal N) =
      (i : LocalAlgebra p K) • (completedMaximalOrder (K := K) p).toSubmodule)
    (hj : completedFractionalIdeal p (saturationFractionalIdeal M) =
      (j : LocalAlgebra p K) • (completedMaximalOrder (K := K) p).toSubmodule)
    (h : completedLattice p N = (c : LocalAlgebra p K) • completedLattice p M) :
    ∃ z : (completedMaximalOrder (K := K) p)ˣ,
      completedLattice p N =
        ((i : LocalAlgebra p K) * ((z : completedMaximalOrder (K := K) p) : LocalAlgebra p K) *
          (↑(j⁻¹) : LocalAlgebra p K)) • completedLattice p M := by
  let u : (LocalAlgebra p K)ˣ := i⁻¹*c*j
  have hu : (u : LocalAlgebra p K) • (completedMaximalOrder (K := K) p).toSubmodule =
      (completedMaximalOrder (K := K) p).toSubmodule := by
    have H := local_saturation_homothety M N p c h
    rw [hi,hj,← mul_smul] at H
    calc
      (u : LocalAlgebra p K) • (completedMaximalOrder (K := K) p).toSubmodule =
          (↑(i⁻¹) : LocalAlgebra p K) •
            (((c : LocalAlgebra p K)*(j : LocalAlgebra p K)) •
              (completedMaximalOrder (K := K) p).toSubmodule) := by
            simp [u,mul_smul,mul_assoc]
      _ = (↑(i⁻¹) : LocalAlgebra p K) •
            ((i : LocalAlgebra p K) • (completedMaximalOrder (K := K) p).toSubmodule) := by rw [← H]
      _ = _ := by rw [← mul_smul,Units.inv_mul,one_smul]
  obtain ⟨z,hz⟩ := completedMaximalOrder_unit_of_smul_eq p u hu
  refine ⟨z,?_⟩
  rw [hz]
  have H : (i : LocalAlgebra p K) * (u : LocalAlgebra p K) * (↑(j⁻¹) : LocalAlgebra p K) = c := by
    simp [u,mul_assoc]
  rw [H]
  exact h

def saturation {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : Submodule ℤ K :=
  (Submodule.span (𝓞 K) (M.carrier : Set K)).restrictScalars ℤ

lemma le_saturation {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : M.carrier ≤ saturation M := by
  intro x hx
  exact Submodule.subset_span hx

lemma saturation_fg {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : (saturation M).FG := by
  apply Submodule.FG.restrictScalars
  rw [← fullLattice_span_basis M, Submodule.span_span_of_tower]
  exact Submodule.fg_span (Set.finite_range _)

 

lemma fullLattice_clear_denominator {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (x : K) : ∃ z : ℤ, z ≠ 0 ∧ z • x ∈ M.carrier := by
  have hx : x ∈ Submodule.span ℚ (M.carrier : Set K) := by rw [M.spans]; trivial
  obtain ⟨y, hy, z, hz⟩ := (IsLocalization.mem_span_iff (nonZeroDivisors ℤ)).mp hx
  rw [Submodule.span_eq] at hy
  refine ⟨z, mem_nonZeroDivisors_iff_ne_zero.mp z.property, ?_⟩
  rw [hz, ← IsScalarTower.algebraMap_smul ℚ, smul_smul,
    IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one, IsLocalization.mk'_self, one_smul]
  exact hy

 
def saturationIndex {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : ℕ := M.carrier.toAddSubgroup.relIndex (saturation M).toAddSubgroup

lemma saturationIndex_ne_zero {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : saturationIndex M ≠ 0 := by
  let S := (saturation M).toAddSubgroup
  let A := M.carrier.toAddSubgroup.addSubgroupOf S
  let : AddGroup.FG S := (AddGroup.fg_iff_addSubgroup_fg S).mpr
    (Submodule.fg_toAddSubgroup (saturation_fg M))
  have ht : Module.IsTorsion ℤ (S ⧸ A) := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      obtain ⟨z, hz, hzx⟩ := fullLattice_clear_denominator M (x : K)
      refine ⟨⟨z, mem_nonZeroDivisors_iff_ne_zero.mpr hz⟩, ?_⟩
      change z • (QuotientAddGroup.mk x : S ⧸ A) = 0
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff]
      exact hzx
  let : Finite (S ⧸ A) := Module.finite_of_fg_torsion _ ht
  exact Nat.card_pos.ne'

 
lemma saturationIndex_smul_mem {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) {x : K} (hx : x ∈ saturation M) :
    saturationIndex M • x ∈ M.carrier :=
  M.carrier.toAddSubgroup.nsmul_relIndex_mem hx

 

lemma exists_idealLocalGenerator {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ u : (LocalAlgebra p K)ˣ,
      completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) =
        (u : LocalAlgebra p K) • (completedMaximalOrder (K := K) p).toSubmodule := by
  have hI : (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := I.ne_zero
  obtain ⟨a,ha,h⟩ := completedFractionalIdeal_principal p
    (I : FractionalIdeal (𝓞 K)⁰ K) hI
  let u : Kˣ := Units.mk0 a ha
  let f : K →* LocalAlgebra p K :=
    (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K).toMonoidHom
  refine ⟨Units.map f u,?_⟩
  exact h

 

def idealLocalGenerator {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : (LocalAlgebra p K)ˣ :=
  (exists_idealLocalGenerator p I).choose

lemma idealLocalGenerator_spec {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) =
      (idealLocalGenerator p I : LocalAlgebra p K) •
        (completedMaximalOrder (K := K) p).toSubmodule :=
  (exists_idealLocalGenerator p I).choose_spec

 
def saturationIdealUnit {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (saturationFractionalIdeal M) (saturationFractionalIdeal_ne_zero M)

lemma saturationLocalGenerator_spec {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime] :
    completedFractionalIdeal p (saturationFractionalIdeal M) =
      (idealLocalGenerator p (saturationIdealUnit M) : LocalAlgebra p K) •
        (completedMaximalOrder (K := K) p).toSubmodule :=
  idealLocalGenerator_spec p (saturationIdealUnit M)

lemma local_smul_mono {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (a : LocalAlgebra p K)
    {L N : Submodule (PadicInt p) (LocalAlgebra p K)} (h : L ≤ N) :
    a • L ≤ a • N := by
  intro x hx
  obtain ⟨y,hy,rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
  exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨y,h hy,rfl⟩

 
def normalizedLocalModule {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime] :
    Submodule (PadicInt p) (LocalAlgebra p K) :=
  (↑((idealLocalGenerator p (saturationIdealUnit M))⁻¹) : LocalAlgebra p K) •
    completedLattice p M

lemma normalizedLocalModule_le {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime] :
    normalizedLocalModule M p ≤ (completedMaximalOrder (K := K) p).toSubmodule := by
  have h : completedLattice p M ≤ completedFractionalIdeal p (saturationIdealUnit M) :=
    Submodule.span_mono (Set.image_mono (fun x hx => Submodule.subset_span hx))
  have H := local_smul_mono p (↑((idealLocalGenerator p (saturationIdealUnit M))⁻¹) :
    LocalAlgebra p K) h
  rw [idealLocalGenerator_spec,← mul_smul,Units.inv_mul,one_smul] at H
  exact H

lemma normalizedLocalModule_saturation {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime] :
    (completedMaximalOrder (K := K) p).toSubmodule * normalizedLocalModule M p =
      (completedMaximalOrder (K := K) p).toSubmodule := by
  rw [normalizedLocalModule,mul_smul_comm,← completed_saturation,
    saturationLocalGenerator_spec,← mul_smul,Units.inv_mul,one_smul]

lemma normalizedLocalModule_saturationIndex_mem
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] {x : LocalAlgebra p K}
    (hx : x ∈ completedMaximalOrder (K := K) p) :
    (saturationIndex M : PadicInt p) • x ∈ normalizedLocalModule M p := by
  let j := idealLocalGenerator p (saturationIdealUnit M)
  have hjx : (j : LocalAlgebra p K) * x ∈
      completedLattice p (fractionalIdealFullLattice hn (saturationIdealUnit M)) := by
    rw [completedLattice_fractionalIdealFullLattice,idealLocalGenerator_spec]
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨x,hx,rfl⟩
  have H := completedLattice_smul_mem (saturationIndex M)
    (M := fractionalIdealFullLattice hn (saturationIdealUnit M)) (N := M)
    (fun a ha => by simpa only [natCast_zsmul] using saturationIndex_smul_mem M ha)
    p hjx
  apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
  refine ⟨(saturationIndex M : PadicInt p) • ((j : LocalAlgebra p K)*x),H,?_⟩
  change (↑(j⁻¹) : LocalAlgebra p K) * _ = _
  rw [mul_smul_comm,← mul_assoc,Units.inv_mul,one_mul]

 
def localModuleChoices {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℕ) [Fact p.Prime] : Set (Submodule (PadicInt p) (LocalAlgebra p K)) :=
  Set.range fun z : (completedMaximalOrder (K := K) p)ˣ =>
    ((idealLocalGenerator p I : LocalAlgebra p K) *
      ((z : completedMaximalOrder (K := K) p) : LocalAlgebra p K)) • normalizedLocalModule M p

lemma localModuleChoices_nonempty {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℕ) [Fact p.Prime] : (localModuleChoices M I p).Nonempty :=
  Set.range_nonempty _

lemma localModuleChoices_le {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℕ) [Fact p.Prime] {N : Submodule (PadicInt p) (LocalAlgebra p K)}
    (hN : N ∈ localModuleChoices M I p) : N ≤ completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) := by
  obtain ⟨z,rfl⟩ := hN
  dsimp only
  rw [mul_smul,idealLocalGenerator_spec]
  apply local_smul_mono
  calc
    _ ≤ (↑(z : completedMaximalOrder (K := K) p) : LocalAlgebra p K) •
        (completedMaximalOrder (K := K) p).toSubmodule :=
      local_smul_mono p _ (normalizedLocalModule_le M p)
    _ = _ := completedMaximalOrder_unit_smul p z

lemma localModuleChoices_saturation {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℕ) [Fact p.Prime] {N : Submodule (PadicInt p) (LocalAlgebra p K)}
    (hN : N ∈ localModuleChoices M I p) :
    (completedMaximalOrder (K := K) p).toSubmodule * N = completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) := by
  obtain ⟨z,rfl⟩ := hN
  dsimp only
  rw [mul_smul_comm,normalizedLocalModule_saturation,mul_smul,
    completedMaximalOrder_unit_smul,idealLocalGenerator_spec]

lemma localModuleChoices_saturationIndex_mem
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (p : ℕ) [Fact p.Prime]
    {N : Submodule (PadicInt p) (LocalAlgebra p K)} (hN : N ∈ localModuleChoices M I p)
    {x : LocalAlgebra p K} (hx : x ∈ completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K)) :
    (saturationIndex M : PadicInt p) • x ∈ N := by
  obtain ⟨z,rfl⟩ := hN
  dsimp only
  rw [idealLocalGenerator_spec] at hx
  obtain ⟨b,hb,rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
  let R := completedMaximalOrder (K := K) p
  have hz : ((z : R) : LocalAlgebra p K) * ((↑(z⁻¹) : R) : LocalAlgebra p K) = 1 :=
    congrArg (fun a : R => (a : LocalAlgebra p K)) z.mul_inv
  have hL := normalizedLocalModule_saturationIndex_mem M hn p
    (R.mul_mem (↑(z⁻¹) : R).property hb)
  apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
  refine ⟨(saturationIndex M : PadicInt p) •
    (((↑(z⁻¹) : R) : LocalAlgebra p K) * b),hL,?_⟩
  change ((idealLocalGenerator p I : LocalAlgebra p K) * ((z : R) : LocalAlgebra p K)) *
      ((saturationIndex M : PadicInt p) • _) = _
  rw [mul_smul_comm]
  congr 1
  change _ = (idealLocalGenerator p I : LocalAlgebra p K) * b
  calc
    _ = (idealLocalGenerator p I : LocalAlgebra p K) *
        ((((z : R) : LocalAlgebra p K) * ((↑(z⁻¹) : R) : LocalAlgebra p K)) * b) := by ring
    _ = _ := by rw [hz,one_mul]

lemma localModuleChoices_primePower_mem
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (p : ℕ) [Fact p.Prime]
    {N : Submodule (PadicInt p) (LocalAlgebra p K)} (hN : N ∈ localModuleChoices M I p)
    {x : LocalAlgebra p K} (hx : x ∈ completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K)) :
    (p : PadicInt p)^((saturationIndex M).factorization p) • x ∈ N := by
  let q := saturationIndex M
  let r := ordCompl[p] q
  have hc : Nat.Coprime p r := Nat.coprime_ordCompl Fact.out (saturationIndex_ne_zero M)
  obtain ⟨u,hu⟩ := PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hc)
  have H := N.smul_mem (↑(u⁻¹) : PadicInt p)
    (localModuleChoices_saturationIndex_mem M hn I p hN hx)
  have hqr : q = p^(q.factorization p)*r := (Nat.ordProj_mul_ordCompl_eq_self q p).symm
  change (↑(u⁻¹) : PadicInt p) • ((q : PadicInt p) • x) ∈ N at H
  rw [smul_smul,hqr,Nat.cast_mul,Nat.cast_pow,← hu] at H
  have he : (↑(u⁻¹) : PadicInt p) * ((p : PadicInt p)^(q.factorization p) * u) =
      (p : PadicInt p)^(q.factorization p) := by
    rw [mul_left_comm,Units.inv_mul,mul_one]
  rwa [he] at H

lemma localModuleChoices_eq_off
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (p : ℕ) [Fact p.Prime]
    (hp : ¬p ∣ saturationIndex M)
    {N : Submodule (PadicInt p) (LocalAlgebra p K)} (hN : N ∈ localModuleChoices M I p) :
    N = completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) := by
  apply le_antisymm (localModuleChoices_le M I p hN)
  intro x hx
  have H := localModuleChoices_primePower_mem M hn I p hN hx
  simpa only [Nat.factorization_eq_zero_of_not_dvd hp,pow_zero,one_smul] using H

 

theorem finite_completedModule_interval
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] (k : ℕ) :
    {N : Submodule (PadicInt p) (LocalAlgebra p K) |
      N ≤ completedLattice p M ∧ ∀ x ∈ completedLattice p M,
        (p : PadicInt p)^k • x ∈ N}.Finite := by
  classical
  let f : Submodule (PadicInt p) (LocalAlgebra p K) →
      AddSubgroup (Fin n → ZMod (p^k)) := fun N =>
    (N.comap (completedLattice p M).subtype).toAddSubgroup.map (completedReduction M hn p k)
  apply Set.Finite.of_finite_image (Set.toFinite (f '' _))
  intro L hL N hN he
  have hmem (P : Submodule (PadicInt p) (LocalAlgebra p K))
      (hP : ∀ x ∈ completedLattice p M, (p : PadicInt p)^k • x ∈ P)
      (x : completedLattice p M) :
      completedReduction M hn p k x ∈ f P ↔ (x : LocalAlgebra p K) ∈ P :=
    completedReduction_mem_image_iff M hn p k (P.comap (completedLattice p M).subtype)
      (fun y => hP y y.property) x
  ext x
  by_cases hx : x ∈ completedLattice p M
  · rw [← hmem L hL.2 ⟨x,hx⟩,← hmem N hN.2 ⟨x,hx⟩,he]
  · exact iff_of_false (fun h => hx (hL.1 h)) (fun h => hx (hN.1 h))

 
theorem localModuleChoices_finite
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (p : ℕ) [Fact p.Prime] :
    (localModuleChoices M I p).Finite := by
  apply (finite_completedModule_interval (fractionalIdealFullLattice hn I) hn p
    ((saturationIndex M).factorization p)).subset
  intro N hN
  exact ⟨localModuleChoices_le M I p hN,
    fun x hx => localModuleChoices_primePower_mem M hn I p hN hx⟩

lemma localModuleChoices_transport
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℕ) [Fact p.Prime] {N : Submodule (PadicInt p) (LocalAlgebra p K)}
    (hN : N ∈ localModuleChoices M I p) :
    (↑(idealLocalGenerator p J * (idealLocalGenerator p I)⁻¹) : LocalAlgebra p K) • N ∈
      localModuleChoices M J p := by
  obtain ⟨z,rfl⟩ := hN
  refine ⟨z,?_⟩
  simp only [Units.val_mul,← mul_smul,mul_assoc,Units.inv_mul_cancel_left]

 

def localModuleChoicesEquiv
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℕ) [Fact p.Prime] : localModuleChoices M I p ≃ localModuleChoices M J p where
  toFun N := ⟨(↑(idealLocalGenerator p J * (idealLocalGenerator p I)⁻¹) : LocalAlgebra p K) • N.1,
    localModuleChoices_transport M I J p N.2⟩
  invFun N := ⟨(↑(idealLocalGenerator p I * (idealLocalGenerator p J)⁻¹) : LocalAlgebra p K) • N.1,
    localModuleChoices_transport M J I p N.2⟩
  left_inv N := by
    apply Subtype.ext
    simp only [Units.val_mul,← mul_smul,mul_assoc,Units.inv_mul_cancel_left,Units.mul_inv,one_smul]
  right_inv N := by
    apply Subtype.ext
    simp only [Units.val_mul,← mul_smul,mul_assoc,Units.inv_mul_cancel_left,Units.mul_inv,one_smul]

lemma localModuleChoices_homothety
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℕ) [Fact p.Prime] {N : Submodule (PadicInt p) (LocalAlgebra p K)}
    (hN : N ∈ localModuleChoices M I p) :
    ∃ c : (LocalAlgebra p K)ˣ, N = (c : LocalAlgebra p K) • completedLattice p M := by
  obtain ⟨z,rfl⟩ := hN
  let v : (LocalAlgebra p K)ˣ := Units.map (completedMaximalOrder (K := K) p).subtype.toMonoidHom z
  refine ⟨idealLocalGenerator p I * v * (idealLocalGenerator p (saturationIdealUnit M))⁻¹,?_⟩
  simp only [normalizedLocalModule,← mul_smul,Units.val_mul]
  rfl

lemma completedLattice_mem_localModuleChoices
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hNI : saturationFractionalIdeal N = I) (hMN : LocallyHomothetic M N)
    (p : ℕ) [Fact p.Prime] : completedLattice p N ∈ localModuleChoices M I p := by
  obtain ⟨c,hc⟩ := hMN p Fact.out
  have h : completedLattice p N = (c : LocalAlgebra p K) • completedLattice p M :=
    SetLike.coe_injective hc
  have hi : completedFractionalIdeal p (saturationFractionalIdeal N) =
      (idealLocalGenerator p I : LocalAlgebra p K) •
        (completedMaximalOrder (K := K) p).toSubmodule := by
    rw [hNI,idealLocalGenerator_spec]
  obtain ⟨z,hz⟩ := local_scalar_choice M N p (idealLocalGenerator p I)
    (idealLocalGenerator p (saturationIdealUnit M)) c hi (saturationLocalGenerator_spec M p) h
  refine ⟨z,?_⟩
  simpa only [normalizedLocalModule,← mul_smul] using hz.symm

 
abbrev labelPrimes {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) := ↥(saturationIndex M).primeFactors

instance labelPrime_fact {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : labelPrimes M) : Fact p.val.Prime :=
  ⟨(Nat.mem_primeFactors.mp p.property).1⟩

 

theorem patch_localModuleChoices
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (N : ∀ p : labelPrimes M, Submodule (PadicInt p.val) (LocalAlgebra p.val K))
    (hN : ∀ p, N p ∈ localModuleChoices M I p.val) :
    ∃ L : FullLattice n K, LocallyHomothetic M L ∧
      saturationFractionalIdeal L = (I : FractionalIdeal (𝓞 K)⁰ K) ∧
      ∀ p : labelPrimes M, completedLattice p.val L = N p := by
  classical
  obtain ⟨L,hLI,hL,hLoff⟩ := patch_fullLattice_completions (fractionalIdealFullLattice hn I) hn
    (fun p : labelPrimes M => p.val) Subtype.val_injective
    (fun p => (saturationIndex M).factorization p.val) N
    (fun p => localModuleChoices_le M I p.val (hN p))
    (fun p x hx => localModuleChoices_primePower_mem M hn I p.val (hN p) hx)
  have hchoices (p : ℕ) (hp : p.Prime) : letI : Fact p.Prime := ⟨hp⟩;
      completedLattice p L ∈ localModuleChoices M I p := by
    let : Fact p.Prime := ⟨hp⟩
    by_cases hs : p ∈ (saturationIndex M).primeFactors
    · exact (hL ⟨p,hs⟩).symm ▸ hN ⟨p,hs⟩
    · have hnot : p ∉ Set.range (fun r : labelPrimes M => r.val) := by
        rintro ⟨r,hr⟩
        exact hs (hr ▸ r.property)
      have hpd : ¬p ∣ saturationIndex M := fun h =>
        hs (Nat.mem_primeFactors.mpr ⟨hp,h,saturationIndex_ne_zero M⟩)
      obtain ⟨A,hA⟩ := localModuleChoices_nonempty M I p
      rw [hLoff p hp hnot,completedLattice_fractionalIdealFullLattice,
        ← localModuleChoices_eq_off M hn I p hpd hA]
      exact hA
  refine ⟨L,?_,?_,hL⟩
  · intro p hp
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨c,hc⟩ := localModuleChoices_homothety M I p (hchoices p hp)
    refine ⟨c,?_⟩
    rw [hc]
    rfl
  · apply fractionalIdeal_eq_of_completions_eq (saturationIdealUnit L) I
    intro p hp
    let : Fact p.Prime := ⟨hp⟩
    change completedFractionalIdeal p (saturationFractionalIdeal L) = _
    rw [completed_saturation]
    exact localModuleChoices_saturation M I p (hchoices p hp)

 

def globalLabels {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Set (Submodule ℤ K) :=
  {P | ∃ N : FullLattice n K, N.carrier = P ∧ LocallyHomothetic M N ∧
    saturationFractionalIdeal N = (I : FractionalIdeal (𝓞 K)⁰ K)}

def globalLabelLattice {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (N : globalLabels M I) : FullLattice n K := N.property.choose

lemma globalLabelLattice_spec {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (N : globalLabels M I) : (globalLabelLattice M I N).carrier = N.val ∧
      LocallyHomothetic M (globalLabelLattice M I N) ∧
      saturationFractionalIdeal (globalLabelLattice M I N) = (I : FractionalIdeal (𝓞 K)⁰ K) :=
  N.property.choose_spec

def globalLabelCompletions {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (N : globalLabels M I) : ∀ p : labelPrimes M, localModuleChoices M I p.val :=
  fun p => ⟨completedLattice p.val (globalLabelLattice M I N),
    completedLattice_mem_localModuleChoices M (globalLabelLattice M I N) I
      (globalLabelLattice_spec M I N).2.2 (globalLabelLattice_spec M I N).2.1 p.val⟩

lemma globalLabelCompletions_injective {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Function.Injective (globalLabelCompletions M I) := by
  intro N N' he
  apply Subtype.ext
  rw [← (globalLabelLattice_spec M I N).1,← (globalLabelLattice_spec M I N').1]
  apply fullLattice_carrier_eq_of_completions_eq _ _ hn
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  by_cases hs : p ∈ (saturationIndex M).primeFactors
  · exact congrArg Subtype.val (congrFun he ⟨p,hs⟩)
  · have hpd : ¬p ∣ saturationIndex M := fun h =>
      hs (Nat.mem_primeFactors.mpr ⟨hp,h,saturationIndex_ne_zero M⟩)
    have h (A : globalLabels M I) : completedLattice p (globalLabelLattice M I A) =
        completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) :=
      localModuleChoices_eq_off M hn I p hpd
        (completedLattice_mem_localModuleChoices M (globalLabelLattice M I A) I
          (globalLabelLattice_spec M I A).2.2 (globalLabelLattice_spec M I A).2.1 p)
    exact (h N).trans (h N').symm

lemma globalLabelCompletions_surjective {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Function.Surjective (globalLabelCompletions M I) := by
  intro A
  obtain ⟨L,hML,hLI,hL⟩ := patch_localModuleChoices M hn I (fun p => (A p).val)
    (fun p => (A p).property)
  let N : globalLabels M I := ⟨L.carrier,⟨L,rfl,hML,hLI⟩⟩
  refine ⟨N,?_⟩
  funext p
  apply Subtype.ext
  change completedLattice p.val (globalLabelLattice M I N) = (A p).val
  have hc : (globalLabelLattice M I N).carrier = L.carrier := (globalLabelLattice_spec M I N).1
  rw [completedLattice,hc,← completedLattice]
  exact hL p

 

def globalLabelEquiv {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    globalLabels M I ≃ (∀ p : labelPrimes M, localModuleChoices M I p.val) :=
  Equiv.ofBijective (globalLabelCompletions M I)
    ⟨globalLabelCompletions_injective M hn I,globalLabelCompletions_surjective M hn I⟩

theorem globalLabels_finite {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : (globalLabels M I).Finite := by
  let (p : labelPrimes M) : Finite (localModuleChoices M I p.val) :=
    (localModuleChoices_finite M hn I p.val).to_subtype
  exact Set.finite_coe_iff.mp (Finite.of_injective _ (globalLabelCompletions_injective M hn I))

 
def globalLabelsEquiv {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : globalLabels M I ≃ globalLabels M J :=
  let e : (∀ p : labelPrimes M, localModuleChoices M I p.val) ≃
      (∀ p : labelPrimes M, localModuleChoices M J p.val) :=
    Equiv.piCongrRight (fun p : labelPrimes M => localModuleChoicesEquiv M I J p.val)
  (globalLabelEquiv M hn I).trans (e.trans (globalLabelEquiv M hn J).symm)

theorem globalLabels_ncard_eq {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : (globalLabels M I).ncard = (globalLabels M J).ncard := by
  exact Nat.card_congr (globalLabelsEquiv M hn I J)

 
abbrev localLatticeQuotient {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (p : ℕ) [Fact p.Prime] :=
  (completedLattice p M) ⧸
    ((completedLattice p N).comap (completedLattice p M).subtype).toAddSubgroup

def localLatticeQuotientMap {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (p : ℕ) [Fact p.Prime] :
    M.carrier →+ localLatticeQuotient M N p :=
  (QuotientAddGroup.mk'
    ((completedLattice p N).comap (completedLattice p M).subtype).toAddSubgroup).comp
    (completionEmbedding M p).toAddMonoidHom

 

theorem localLatticeQuotientMap_simultaneous_surjective
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (hn : Module.finrank ℚ K = n)
    {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ j, Fact (p j).Prime]
    (hp : Function.Injective p) (k : ι → ℕ)
    (hpow : ∀ j x, x ∈ completedLattice (p j) M →
      (p j : PadicInt (p j))^(k j) • x ∈ completedLattice (p j) N) :
    Function.Surjective (AddMonoidHom.pi (fun j => localLatticeQuotientMap M N (p j))) := by
  intro z
  choose y hy using fun j => QuotientAddGroup.mk'_surjective
    ((completedLattice (p j) N).comap (completedLattice (p j) M).subtype).toAddSubgroup (z j)
  obtain ⟨x,hx⟩ := completedReduction_simultaneous_surjective M hn p hp k
    (fun j => completedReduction M hn (p j) (k j) (y j))
  refine ⟨x,?_⟩
  funext j
  change QuotientAddGroup.mk (completionEmbedding M (p j) x) = z j
  rw [← hy j]
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  have hk : completionEmbedding M (p j) x - y j ∈ (completedReduction M hn (p j) (k j)).ker := by
    change completedReduction M hn (p j) (k j) (_ - _) = 0
    rw [map_sub,hx j,sub_self]
  obtain ⟨v,hv⟩ := (completedReduction_eq_zero_iff M hn (p j) (k j) _).mp hk
  change ((completionEmbedding M (p j) x - y j : completedLattice (p j) M) : LocalAlgebra (p j) K) ∈ completedLattice (p j) N
  rw [hv]
  exact hpow j v v.property

 

theorem fullLattice_relIndex_eq_prod_local
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (hn : Module.finrank ℚ K = n)
    {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ j, Fact (p j).Prime]
    (hp : Function.Injective p) (k : ι → ℕ)
    (hpow : ∀ j x, x ∈ completedLattice (p j) M →
      (p j : PadicInt (p j))^(k j) • x ∈ completedLattice (p j) N)
    (hoff : ∀ (r : ℕ) (hr : r.Prime), letI : Fact r.Prime := ⟨hr⟩;
      r ∉ Set.range p → completedLattice r N = completedLattice r M) :
    N.carrier.toAddSubgroup.relIndex M.carrier.toAddSubgroup =
      ∏ j, (completedLattice (p j) N).toAddSubgroup.relIndex
        (completedLattice (p j) M).toAddSubgroup := by
  classical
  let f := AddMonoidHom.pi (fun j => localLatticeQuotientMap M N (p j))
  have hf : Function.Surjective f := localLatticeQuotientMap_simultaneous_surjective M N hn p hp k hpow
  have hker : f.ker = (N.carrier.comap M.carrier.subtype).toAddSubgroup := by
    ext x
    change f x = 0 ↔ (x : K) ∈ N.carrier
    rw [mem_fullLattice_iff_forall_completed N hn]
    constructor
    · intro hx r hr
      let : Fact r.Prime := ⟨hr⟩
      by_cases hs : r ∈ Set.range p
      · obtain ⟨j,rfl⟩ := hs
        have H := congrFun hx j
        exact QuotientAddGroup.eq_zero_iff _ |>.mp H
      · rw [hoff r hr hs]
        exact (completionEmbedding M r x).property
    · intro hx
      funext j
      exact (QuotientAddGroup.eq_zero_iff _).mpr (hx (p j) Fact.out)
  change (N.carrier.comap M.carrier.subtype).toAddSubgroup.index = _
  rw [← hker,AddSubgroup.index_ker,AddMonoidHom.range_eq_top.mpr hf]
  rw [AddSubgroup.card_top,Nat.card_pi]
  rfl

lemma local_relIndex_smul
    {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (c : (LocalAlgebra p K)ˣ) (L R : Submodule (PadicInt p) (LocalAlgebra p K)) :
    ((c : LocalAlgebra p K) • L).toAddSubgroup.relIndex
      ((c : LocalAlgebra p K) • R).toAddSubgroup = L.toAddSubgroup.relIndex R.toAddSubgroup := by
  exact AddSubgroup.relIndex_pointwise_smul c L.toAddSubgroup R.toAddSubgroup

lemma saturation_completed_primePower_mem
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] {x : LocalAlgebra p K}
    (hx : x ∈ completedFractionalIdeal p (saturationFractionalIdeal M)) :
    (p : PadicInt p)^((saturationIndex M).factorization p) • x ∈ completedLattice p M := by
  apply completedLattice_primePower_mem (M := fractionalIdealFullLattice hn (saturationIdealUnit M))
    (saturationIndex M) _ p _ (ordCompl[p] (saturationIndex M))
    (Nat.ordProj_mul_ordCompl_eq_self (saturationIndex M) p).symm
    (Nat.coprime_ordCompl Fact.out (saturationIndex_ne_zero M)) hx
  intro y hy
  exact_mod_cast saturationIndex_smul_mem M hy

lemma saturation_completed_eq_off
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] (hp : ¬p ∣ saturationIndex M) :
    completedLattice p M = completedFractionalIdeal p (saturationFractionalIdeal M) := by
  apply le_antisymm
  · exact completedLattice_mono (M := M)
      (N := fractionalIdealFullLattice hn (saturationIdealUnit M)) (le_saturation M) p
  · intro x hx
    have H := saturation_completed_primePower_mem M hn p hx
    simpa only [Nat.factorization_eq_zero_of_not_dvd hp,pow_zero,one_smul] using H

 
theorem saturationIndex_eq_prod_local
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) :
    saturationIndex M = ∏ p : labelPrimes M,
      (completedLattice p.val M).toAddSubgroup.relIndex
        (completedFractionalIdeal p.val (saturationFractionalIdeal M)).toAddSubgroup := by
  apply fullLattice_relIndex_eq_prod_local (fractionalIdealFullLattice hn (saturationIdealUnit M)) M hn
    (fun p : labelPrimes M => p.val) Subtype.val_injective
    (fun p => (saturationIndex M).factorization p.val)
    (fun p x hx => saturation_completed_primePower_mem M hn p.val hx)
  intro p hp hnot
  let : Fact p.Prime := ⟨hp⟩
  apply saturation_completed_eq_off M hn p
  intro hd
  exact hnot ⟨⟨p,Nat.mem_primeFactors.mpr ⟨hp,hd,saturationIndex_ne_zero M⟩⟩,rfl⟩

 

theorem saturationIndex_eq_of_locallyHomothetic
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (hMN : LocallyHomothetic M N) : saturationIndex N = saturationIndex M := by
  have h (p : ℕ) (hp : p.Prime) : letI : Fact p.Prime := ⟨hp⟩;
      ∃ c : (LocalAlgebra p K)ˣ,
        completedLattice p N = (c : LocalAlgebra p K) • completedLattice p M ∧
        completedFractionalIdeal p (saturationFractionalIdeal N) =
          (c : LocalAlgebra p K) • completedFractionalIdeal p (saturationFractionalIdeal M) := by
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨c,hc⟩ := hMN p hp
    have hc' : completedLattice p N = (c : LocalAlgebra p K) • completedLattice p M :=
      SetLike.coe_injective hc
    exact ⟨c,hc',local_saturation_homothety M N p c hc'⟩
  have hpow (p : labelPrimes M) (x : LocalAlgebra p.val K)
      (hx : x ∈ completedFractionalIdeal p.val (saturationFractionalIdeal N)) :
      (p.val : PadicInt p.val)^((saturationIndex M).factorization p.val) • x ∈
        completedLattice p.val N := by
    obtain ⟨c,hc,hs⟩ := h p.val Fact.out
    rw [hs] at hx
    obtain ⟨y,hy,rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    rw [hc,smul_comm]
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
      ⟨_,saturation_completed_primePower_mem M hn p.val hy,rfl⟩
  have hoff (p : ℕ) (hp : p.Prime) : letI : Fact p.Prime := ⟨hp⟩;
      p ∉ Set.range (fun r : labelPrimes M => r.val) →
        completedLattice p N = completedFractionalIdeal p (saturationFractionalIdeal N) := by
    let : Fact p.Prime := ⟨hp⟩
    intro hnot
    obtain ⟨c,hc,hs⟩ := h p hp
    rw [hc,hs]
    congr 1
    apply saturation_completed_eq_off M hn p
    intro hd
    exact hnot ⟨⟨p,Nat.mem_primeFactors.mpr ⟨hp,hd,saturationIndex_ne_zero M⟩⟩,rfl⟩
  have hprod := fullLattice_relIndex_eq_prod_local
    (fractionalIdealFullLattice hn (saturationIdealUnit N)) N hn
    (fun p : labelPrimes M => p.val) Subtype.val_injective
    (fun p => (saturationIndex M).factorization p.val) hpow hoff
  change saturationIndex N = _ at hprod
  apply hprod.trans
  apply Eq.trans _ (saturationIndex_eq_prod_local M hn).symm
  apply Finset.prod_congr rfl
  intro p _
  obtain ⟨c,hc,hs⟩ := h p.val Fact.out
  change (completedLattice p.val N).toAddSubgroup.relIndex
    (completedFractionalIdeal p.val (saturationFractionalIdeal N)).toAddSubgroup = _
  rw [hc,hs]
  exact local_relIndex_smul p.val c _ _

 
theorem globalLabel_relIndex
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (N : globalLabels M I) :
    N.val.toAddSubgroup.relIndex
      ((I : Submodule (𝓞 K) K).restrictScalars ℤ).toAddSubgroup = saturationIndex M := by
  have hc : saturation (globalLabelLattice M I N) =
      (I : Submodule (𝓞 K) K).restrictScalars ℤ :=
    congrArg (fun J : FractionalIdeal (𝓞 K)⁰ K => (J : Submodule (𝓞 K) K).restrictScalars ℤ)
      (globalLabelLattice_spec M I N).2.2
  rw [← (globalLabelLattice_spec M I N).1,← hc]
  exact saturationIndex_eq_of_locallyHomothetic M (globalLabelLattice M I N) hn
    (globalLabelLattice_spec M I N).2.1

 

lemma globalLabel_contains_iff
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (N : globalLabels M I)
    (a : K) (ha : a ∈ (I : FractionalIdeal (𝓞 K)⁰ K)) :
    a ∈ N.val ↔ ∀ p : labelPrimes M,
      (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p.val K) a ∈
        (globalLabelCompletions M I N p).val := by
  rw [← (globalLabelLattice_spec M I N).1,
    mem_fullLattice_iff_forall_completed (globalLabelLattice M I N) hn]
  constructor
  · intro h p
    exact h p.val Fact.out
  · intro h p hp
    let : Fact p.Prime := ⟨hp⟩
    by_cases hs : p ∈ (saturationIndex M).primeFactors
    · exact h ⟨p,hs⟩
    · have hpd : ¬p ∣ saturationIndex M := fun h =>
        hs (Nat.mem_primeFactors.mpr ⟨hp,h,saturationIndex_ne_zero M⟩)
      have hN := completedLattice_mem_localModuleChoices M (globalLabelLattice M I N) I
        (globalLabelLattice_spec M I N).2.2 (globalLabelLattice_spec M I N).2.1 p
      rw [localModuleChoices_eq_off M hn I p hpd hN]
      exact Submodule.subset_span ⟨a,ha,rfl⟩

def localContainmentLabels {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℕ) [Fact p.Prime] (x : LocalAlgebra p K) :=
  {N : localModuleChoices M I p // x ∈ N.val}

 
def globalContainmentEquiv
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : K)
    (ha : a ∈ (I : FractionalIdeal (𝓞 K)⁰ K)) :
    {N : globalLabels M I // a ∈ N.val} ≃
      (∀ p : labelPrimes M, localContainmentLabels M I p.val
        ((Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p.val K) a)) :=
  let e : {N : globalLabels M I // a ∈ N.val} ≃
      {f : ∀ p : labelPrimes M, localModuleChoices M I p.val // ∀ p,
        (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p.val K) a ∈ (f p).val} :=
    Equiv.subtypeEquiv (globalLabelEquiv M hn I) (fun N => globalLabel_contains_iff M hn I N a ha)
  e.trans (Equiv.subtypePiEquivPi (p := fun (p : labelPrimes M)
    (L : localModuleChoices M I p.val) =>
      (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p.val K) a ∈ L.val))

theorem globalLabels_card_prod
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Nat.card (globalLabels M I) = ∏ p : labelPrimes M, Nat.card (localModuleChoices M I p.val) := by
  rw [Nat.card_congr (globalLabelEquiv M hn I),Nat.card_pi]

theorem globalLabels_card_pos
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : 0 < Nat.card (globalLabels M I) := by
  classical
  rw [globalLabels_card_prod M hn I]
  apply Finset.prod_pos
  intro p _
  let : Finite (localModuleChoices M I p.val) := (localModuleChoices_finite M hn I p.val).to_subtype
  let : Nonempty (localModuleChoices M I p.val) := (localModuleChoices_nonempty M I p.val).to_subtype
  exact Nat.card_pos

 

def localContainmentProbability
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℕ) [Fact p.Prime] (x : LocalAlgebra p K) : ℝ :=
  (Nat.card (localContainmentLabels M I p x) : ℝ) / Nat.card (localModuleChoices M I p)

 
theorem globalContainmentProbability_eq_prod
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : K)
    (ha : a ∈ (I : FractionalIdeal (𝓞 K)⁰ K)) :
    (Nat.card {N : globalLabels M I // a ∈ N.val} : ℝ) / Nat.card (globalLabels M I) =
      ∏ p : labelPrimes M, localContainmentProbability M I p.val
        ((Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p.val K) a) := by
  rw [Nat.card_congr (globalContainmentEquiv M hn I a ha),Nat.card_pi,globalLabels_card_prod M hn I]
  simp only [Nat.cast_prod,Finset.prod_div_distrib,localContainmentProbability]

open Topology
open scoped Pointwise
instance {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] :
    TopologicalSpace (LocalAlgebra p K) := moduleTopology (Padic p) (LocalAlgebra p K)
instance {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] :
    IsModuleTopology (Padic p) (LocalAlgebra p K) := ⟨rfl⟩
instance {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] :
    IsTopologicalRing (LocalAlgebra p K) := IsModuleTopology.isTopologicalRing (Padic p) (LocalAlgebra p K)
instance {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] :
    ContinuousSMul (Padic p) (LocalAlgebra p K) := IsModuleTopology.toContinuousSMul (Padic p) (LocalAlgebra p K)
def localAlgebraCoordinates {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
    (p : ℕ) [Fact p.Prime] (b : Basis ι ℚ K) : LocalAlgebra p K ≃L[Padic p] (ι → Padic p) where
  __ := (b.baseChange (Padic p)).equivFun
  continuous_toFun := IsModuleTopology.continuous_of_linearMap _
  continuous_invFun := IsModuleTopology.continuous_of_linearMap
    ((b.baseChange (Padic p)).equivFun.symm.toLinearMap)
instance {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] :
    T2Space (LocalAlgebra p K) := (localAlgebraCoordinates p (Module.Free.chooseBasis ℚ K)).toHomeomorph.isEmbedding.t2Space
instance {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] :
    LocallyCompactSpace (LocalAlgebra p K) := (localAlgebraCoordinates p (Module.Free.chooseBasis ℚ K)).toHomeomorph.isClosedEmbedding.locallyCompactSpace

 
def localIntegralSpan {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
    (p : ℕ) [Fact p.Prime] (b : Basis ι ℚ K) : Submodule (PadicInt p) (LocalAlgebra p K) :=
  Submodule.span (PadicInt p) (Set.range (fun i => (b.baseChange (Padic p)) i))

lemma localIntegralSpan_mem {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
    (p : ℕ) [Fact p.Prime] (b : Basis ι ℚ K) (x : LocalAlgebra p K) :
    x ∈ localIntegralSpan p b ↔ ∀ i, ‖localAlgebraCoordinates p b x i‖ ≤ 1 := by
  classical
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i,rfl⟩ := hy
      intro j
      change ‖(b.baseChange (Padic p)).repr ((b.baseChange (Padic p)) i) j‖ ≤ 1
      rw [Basis.repr_self]
      by_cases h : i = j
      · subst j; simp
      · simp [h]
    | zero => simp [localAlgebraCoordinates]
    | add x y hx hy ihx ihy =>
      intro i
      simpa using (Padic.nonarchimedean (localAlgebraCoordinates p b x i) (localAlgebraCoordinates p b y i)).trans
        (max_le (ihx i) (ihy i))
    | smul a x hx ih =>
      intro i
      have ha : ‖(a : Padic p)‖ ≤ 1 := a.property
      have hsm : localAlgebraCoordinates p b (a • x) i = (a : Padic p) * localAlgebraCoordinates p b x i := by
        change (b.baseChange (Padic p)).repr (a • x) i = _
        rw [← IsScalarTower.algebraMap_smul (Padic p) a x,map_smul]
        rfl
      rw [hsm,norm_mul]
      exact (mul_le_mul ha (ih i) (norm_nonneg _) zero_le_one).trans (by norm_num)
  · intro hx
    rw [← (b.baseChange (Padic p)).sum_repr x]
    apply Submodule.sum_mem
    intro i _
    let a : PadicInt p := ⟨localAlgebraCoordinates p b x i,hx i⟩
    have h := Submodule.smul_mem (localIntegralSpan p b) a
      (Submodule.subset_span (Set.mem_range_self i))
    rw [← IsScalarTower.algebraMap_smul (Padic p) a] at h
    exact h

lemma localIntegralSpan_compact {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
    (p : ℕ) [Fact p.Prime] (b : Basis ι ℚ K) :
    IsCompact (localIntegralSpan p b : Set (LocalAlgebra p K)) := by
  let f : (ι → PadicInt p) → LocalAlgebra p K := fun v => (localAlgebraCoordinates p b).symm (fun i => (v i : Padic p))
  have hf : Continuous f := (localAlgebraCoordinates p b).symm.continuous.comp
    (continuous_pi (fun i => PadicInt.isOpenEmbedding_coe.continuous.comp (continuous_apply i)))
  have he : (localIntegralSpan p b : Set (LocalAlgebra p K)) = Set.range f := by
    ext x
    rw [SetLike.mem_coe,localIntegralSpan_mem]
    constructor
    · intro hx
      refine ⟨fun i => ⟨localAlgebraCoordinates p b x i,hx i⟩,?_⟩
      exact (localAlgebraCoordinates p b).symm_apply_apply x
    · rintro ⟨v,rfl⟩
      intro i
      simpa [f] using (v i).property
  rw [he]
  exact isCompact_range hf

lemma localIntegralSpan_open {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
    (p : ℕ) [Fact p.Prime] (b : Basis ι ℚ K) :
    IsOpen (localIntegralSpan p b : Set (LocalAlgebra p K)) := by
  have he : (localIntegralSpan p b : Set (LocalAlgebra p K)) =
      ⋂ i, (fun x => localAlgebraCoordinates p b x i) ⁻¹' Set.range ((↑) : PadicInt p → Padic p) := by
    ext x
    rw [SetLike.mem_coe,localIntegralSpan_mem]
    simp only [Set.mem_iInter,Set.mem_preimage,Subtype.range_coe_subtype]
    rfl
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  exact PadicInt.isOpenEmbedding_coe.isOpen_range.preimage
    ((continuous_apply i).comp (localAlgebraCoordinates p b).continuous)

 

theorem isClosed_unit_smul_submodule_eq
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (P Q : Submodule R A) (hP : IsClosed (P : Set A)) (hQ : IsClosed (Q : Set A)) :
    IsClosed {u : Aˣ | (u : A) • P = Q} := by
  have he : {u : Aˣ | (u : A) • P = Q} =
      {u : Aˣ | ∀ x ∈ P, (u : A) * x ∈ Q} ∩
      {u : Aˣ | ∀ x ∈ Q, (↑(u⁻¹) : A) * x ∈ P} := by
    ext u
    constructor
    · intro h
      constructor
      · intro x hx
        rw [← h]
        exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨x,hx,rfl⟩
      · intro x hx
        rw [← h] at hx
        obtain ⟨y,hy,hye⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
        change (u : A) * y = x at hye
        rw [← hye,← mul_assoc,Units.inv_mul,one_mul]
        exact hy
    · rintro ⟨h1,h2⟩
      apply le_antisymm
      · intro x hx
        obtain ⟨y,hy,rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
        exact h1 y hy
      · intro x hx
        exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
          ⟨↑(u⁻¹) * x,h2 x hx,by simp [smul_eq_mul,← mul_assoc]⟩
  rw [he]
  simp only [Set.ofPred_forall]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro _
    exact hQ.preimage (Units.continuous_val.mul_const x)
  · apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro _
    exact hP.preimage ((Units.continuous_val.comp continuous_inv).mul_const x)

lemma completedLattice_compact {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (p : ℕ) [Fact p.Prime] :
    IsCompact (completedLattice p M : Set (LocalAlgebra p K)) := by
  have h := localIntegralSpan_compact p (fullLatticeRatBasis M hn)
  simpa [localIntegralSpan,completedLattice_eq_span_basis] using h

lemma completedLattice_open {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (p : ℕ) [Fact p.Prime] :
    IsOpen (completedLattice p M : Set (LocalAlgebra p K)) := by
  have h := localIntegralSpan_open p (fullLatticeRatBasis M hn)
  simpa [localIntegralSpan,completedLattice_eq_span_basis] using h

instance completedMaximalOrderCompactSpace {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] : CompactSpace (completedMaximalOrder (K := K) p) := by
  apply isCompact_iff_compactSpace.mp
  exact completedLattice_compact (fractionalIdealFullLattice rfl 1) rfl p

example {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] :
    CompactSpace (completedMaximalOrder (K := K) p)ˣ := inferInstance

instance localUnitsMeasurableSpace {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] : MeasurableSpace (completedMaximalOrder (K := K) p)ˣ := borel _
instance localUnitsBorelSpace {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] : BorelSpace (completedMaximalOrder (K := K) p)ˣ := ⟨rfl⟩

lemma compact_smul_submodule {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [TopologicalSpace A] [IsTopologicalRing A] (a : A)
    (N : Submodule R A) (hN : IsCompact (N : Set A)) : IsCompact (a • N : Set A) := by
  have he : (a • N : Set A) = (fun x : A => a * x) '' (N : Set A) := by
    ext x
    exact Submodule.mem_smul_pointwise_iff_exists _ _ _
  rw [he]
  exact hN.image (continuous_const.mul continuous_id)

lemma normalizedLocalModule_compact {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (p : ℕ) [Fact p.Prime] :
    IsCompact (normalizedLocalModule M p : Set (LocalAlgebra p K)) :=
  compact_smul_submodule _ _ (completedLattice_compact M hn p)

lemma localModuleChoices_compact {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (p : ℕ) [Fact p.Prime]
    (N : localModuleChoices M I p) : IsCompact (N.val : Set (LocalAlgebra p K)) := by
  obtain ⟨z,hz⟩ := N.property
  rw [← hz]
  exact compact_smul_submodule _ _ (normalizedLocalModule_compact M hn p)

open Filter in
 

lemma localModule_denominator {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (S : Submodule (PadicInt p) (LocalAlgebra p K))
    (hS : S.FG) : ∃ k : ℕ, ∀ x ∈ S,
      (p : PadicInt p)^k • x ∈ (completedMaximalOrder (K := K) p).toSubmodule := by
  let R := (completedMaximalOrder (K := K) p).toSubmodule
  have hRo : IsOpen (R : Set (LocalAlgebra p K)) := by
    exact completedLattice_open (fractionalIdealFullLattice (K := K) rfl 1) rfl p
  have hpow : Tendsto (fun k : ℕ => (p : Padic p)^k) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by
      rw [Padic.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt))
  have hx (x : LocalAlgebra p K) : ∀ᶠ k : ℕ in atTop, (p : PadicInt p)^k • x ∈ R := by
    have H : ∀ᶠ k : ℕ in atTop, (p : Padic p)^k • x ∈ R :=
      (hpow.smul tendsto_const_nhds).eventually
        (hRo.mem_nhds (show (0 : Padic p) • x ∈ R by simp))
    filter_upwards [H] with k hk
    rw [← IsScalarTower.algebraMap_smul (Padic p),map_pow,map_natCast]
    exact hk
  obtain ⟨t,ht⟩ := hS
  have ht' : ∀ᶠ k : ℕ in atTop, ∀ x ∈ t, (p : PadicInt p)^k • x ∈ R := by
    exact (Filter.eventually_all_finset t).mpr (fun x _ => hx x)
  obtain ⟨k,hk⟩ := ht'.exists
  refine ⟨k,?_⟩
  intro x hx
  rw [←ht] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hk x hx
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [smul_add] using R.add_mem ihx ihy
  | smul a x hx ih => simpa only [smul_comm ((p : PadicInt p)^k) a] using R.smul_mem a ih

def scaleFullLattice {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (a : Kˣ) : FullLattice n K where
  carrier := M.carrier.map ((LinearEquiv.smulOfUnit (M := K) a).restrictScalars ℤ).toLinearMap
  basis := M.basis.map (Submodule.equivMapOfInjective
    ((LinearEquiv.smulOfUnit (M := K) a).restrictScalars ℤ).toLinearMap
    ((LinearEquiv.smulOfUnit (M := K) a).restrictScalars ℤ).injective _)
  spans := by
    change Submodule.span ℚ (((LinearEquiv.smulOfUnit (M := K) a).restrictScalars ℚ).toLinearMap ''
      (M.carrier : Set K)) = ⊤
    rw [← Submodule.map_span, M.spans, Submodule.map_top, LinearEquiv.range]

@[simp] lemma scaleFullLattice_basis {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (a : Kˣ) (i : Fin n) :
    ((scaleFullLattice M a).basis i : K) = (a : K) * (M.basis i : K) := rfl

lemma scaleFullLattice_carrier {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (a : Kˣ) :
    ((scaleFullLattice M a).carrier : Set K) = (fun x => (a : K) * x) '' (M.carrier : Set K) := rfl

lemma completedLattice_scale {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (a : Kˣ) (p : ℕ) [Fact p.Prime] :
    completedLattice p (scaleFullLattice M a) =
      (completedLattice p M).map (LinearMap.mulLeft (PadicInt p)
        (Algebra.TensorProduct.includeRight (R := ℚ) (A := Padic p) (a : K))) := by
  unfold completedLattice
  rw [scaleFullLattice_carrier, Submodule.map_span, Set.image_image, Set.image_image]
  congr 1
  apply Set.image_congr
  intro x _
  exact map_mul _ _ _

lemma completedLattice_scale_rat {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (a : ℚˣ) (p : ℕ) [Fact p.Prime] :
    completedLattice p (scaleFullLattice M (Units.map (algebraMap ℚ K) a)) =
      (algebraMap ℚ (Padic p) (a : ℚ)) • completedLattice p M := by
  rw [completedLattice_scale, Submodule.pointwise_smul_def]
  congr 1
  ext x
  change (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K)
    (algebraMap ℚ K (a : ℚ)) * x = (algebraMap ℚ (Padic p) (a : ℚ)) • x
  rw [AlgHom.commutes,← IsScalarTower.algebraMap_smul (LocalAlgebra p K),
    IsScalarTower.algebraMap_apply ℚ (Padic p) (LocalAlgebra p K)]
  rfl

 

lemma patch_localOvermodule {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (S : Submodule (PadicInt p) (LocalAlgebra p K))
    (hS : S.FG) (hRS : (completedMaximalOrder (K := K) p).toSubmodule ≤ S) :
    ∃ L : FullLattice (Module.finrank ℚ K) K,
      completedLattice p L = S ∧
      ∀ (r : ℕ) (hr : r.Prime), letI : Fact r.Prime := ⟨hr⟩;
        r ≠ p → completedLattice r L = (completedMaximalOrder (K := K) r).toSubmodule := by
  classical
  obtain ⟨k,hk⟩ := localModule_denominator p S hS
  let M := fractionalIdealFullLattice (K := K) rfl (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  let N : Submodule (PadicInt p) (LocalAlgebra p K) := (p : Padic p)^k • S
  have hN : N ≤ completedLattice p M := by
    rintro x hx
    obtain ⟨y,hy,rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    have H := hk y hy
    rw [← IsScalarTower.algebraMap_smul (Padic p),map_pow,map_natCast] at H
    exact H
  have hpow (x : LocalAlgebra p K) (hx : x ∈ completedLattice p M) :
      (p : PadicInt p)^k • x ∈ N := by
    rw [← IsScalarTower.algebraMap_smul (Padic p),map_pow,map_natCast]
    exact Submodule.smul_mem_pointwise_smul x _ S (hRS hx)
  obtain ⟨L,hLM,hLp,hLoff⟩ := patch_fullLattice_completions M rfl
    (fun _ : Unit => p) (fun _ _ _ => Subsingleton.elim _ _) (fun _ => k) (fun _ => N)
    (fun _ => hN) (fun _ => hpow)
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  let a : ℚˣ := (Units.mk0 (p : ℚ) hp0)^(- (k : ℤ))
  have ha (r : ℕ) [Fact r.Prime] : algebraMap ℚ (Padic r) (a : ℚ) = ((p : Padic r)^k)⁻¹ := by
    simp [a, zpow_neg, zpow_natCast]
  refine ⟨scaleFullLattice L (Units.map (algebraMap ℚ K) a),?_,?_⟩
  · rw [completedLattice_scale_rat,ha,hLp ()]
    change ((p : Padic p)^k)⁻¹ • ((p : Padic p)^k • S) = S
    rw [inv_smul_smul₀ (pow_ne_zero k (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))]
  · intro r hr hrp
    let : Fact r.Prime := ⟨hr⟩
    rw [completedLattice_scale_rat,ha,hLoff r hr (by simpa using hrp)]
    have hc : r.Coprime p := (Nat.coprime_primes hr (Fact.out : p.Prime)).mpr hrp
    obtain ⟨u,hu⟩ := (PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hc))
    have he : ((p : Padic r)^k)⁻¹ =
        algebraMap (PadicInt r) (Padic r) ((↑(u⁻¹)^k : PadicInt r)) := by
      rw [map_pow,map_units_inv,hu,map_natCast,inv_pow]
    rw [he]
    have hs (b : PadicInt r) :
        (algebraMap (PadicInt r) (Padic r) b) • completedLattice r M = b • completedLattice r M := by
      simp only [Submodule.pointwise_smul_def]
      congr 1
    rw [hs]
    change ((↑(u⁻¹)^k : PadicInt r)) • (completedMaximalOrder (K := K) r).toSubmodule = _
    let R := (completedMaximalOrder (K := K) r).toSubmodule
    apply le_antisymm (Submodule.smul_le_self_of_tower _ _)
    intro x hx
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
      ⟨(u : PadicInt r)^k • x,R.smul_mem _ hx,?_⟩
    rw [smul_smul,← mul_pow,Units.inv_mul,one_pow,one_smul]

 

theorem completedMaximalOrder_maximal_finite {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (S : Subalgebra (PadicInt p) (LocalAlgebra p K))
    (hS : S.toSubmodule.FG) (hRS : completedMaximalOrder (K := K) p ≤ S) :
    S = completedMaximalOrder (K := K) p := by
  classical
  obtain ⟨L,hLp,hLoff⟩ := patch_localOvermodule p S.toSubmodule hS hRS
  have h1 : (1 : K) ∈ L.carrier := by
    rw [mem_fullLattice_iff_forall_completed L rfl]
    intro r hr
    let : Fact r.Prime := ⟨hr⟩
    rw [map_one]
    by_cases he : r = p
    · subst r
      rw [hLp]
      exact S.one_mem
    · rw [hLoff r hr he]
      exact (completedMaximalOrder (K := K) r).one_mem
  have hmul (x y : K) (hx : x ∈ L.carrier) (hy : y ∈ L.carrier) : x*y ∈ L.carrier := by
    rw [mem_fullLattice_iff_forall_completed L rfl] at hx hy ⊢
    intro r hr
    let : Fact r.Prime := ⟨hr⟩
    have hx' := hx r hr
    have hy' := hy r hr
    rw [map_mul]
    by_cases he : r = p
    · subst r
      rw [hLp] at hx' hy' ⊢
      exact S.mul_mem hx' hy'
    · rw [hLoff r hr he] at hx' hy' ⊢
      exact (completedMaximalOrder (K := K) r).mul_mem hx' hy'
  let T : Subalgebra ℤ K :=
    { carrier := L.carrier
      zero_mem' := L.carrier.zero_mem
      add_mem' := L.carrier.add_mem
      mul_mem' := hmul _ _
      algebraMap_mem' := fun z => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact L.carrier.smul_mem z h1 }
  have hTL : T.toSubmodule = L.carrier := by ext x; rfl
  have hfg : T.toSubmodule.FG := by
    rw [hTL]
    refine ⟨Finset.univ.image (fun i => (L.basis i : K)),?_⟩
    simpa only [Finset.coe_image,Finset.coe_univ,Set.image_univ] using fullLattice_span_basis L
  let M := fractionalIdealFullLattice (K := K) rfl (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  have hLM : L.carrier ≤ M.carrier := by
    intro x hx
    have hint := IsIntegral.of_mem_of_fg T hfg x hx
    change x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K)
    exact (FractionalIdeal.mem_one_iff (𝓞 K)⁰).mpr ⟨⟨x,hint⟩,rfl⟩
  have H := completedLattice_mono hLM p
  rw [hLp] at H
  exact le_antisymm H hRS

 

theorem mem_completedMaximalOrder_iff_isIntegral {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (x : LocalAlgebra p K) :
    x ∈ completedMaximalOrder (K := K) p ↔ IsIntegral (PadicInt p) x := by
  let R := completedMaximalOrder (K := K) p
  have hR : R.toSubmodule.FG := completedFractionalIdeal_fg p 1
  constructor
  · exact IsIntegral.of_mem_of_fg R hR x
  · intro hx
    let : Module.Finite (PadicInt p) R := Module.Finite.of_fg hR
    let T := Algebra.adjoin R ({x} : Set (LocalAlgebra p K))
    have hT : T.toSubmodule.FG := (hx.tower_top (A := R)).fg_adjoin_singleton
    have hRT : R ≤ T.restrictScalars (PadicInt p) := by
      intro y hy
      exact T.algebraMap_mem (⟨y,hy⟩ : R)
    have he := completedMaximalOrder_maximal_finite p (T.restrictScalars (PadicInt p))
      (hT.restrictScalars (R := PadicInt p)) hRT
    have hxT : x ∈ T := Algebra.subset_adjoin (Set.mem_singleton x)
    have hxT' : x ∈ T.restrictScalars (PadicInt p) := hxT
    exact he ▸ hxT' 

theorem completedMaximalOrder_eq_integralClosure {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] :
    completedMaximalOrder (K := K) p = integralClosure (PadicInt p) (LocalAlgebra p K) := by
  ext x
  exact mem_completedMaximalOrder_iff_isIntegral p x

open Polynomial

 

theorem isIntegral_padicInt_iff_spectralNorm_le_one
    (p : ℕ) [Fact p.Prime] (E : Type*) [Field E] [Algebra (Padic p) E]
    [FiniteDimensional (Padic p) E] [Algebra (PadicInt p) E]
    [IsScalarTower (PadicInt p) (Padic p) E] (x : E) :
    IsIntegral (PadicInt p) x ↔ spectralNorm (Padic p) E x ≤ 1 := by
  constructor
  · rintro ⟨f,hf,hfx⟩
    have hf' : (f.map (algebraMap (PadicInt p) (Padic p))).Monic := hf.map _
    have hr : aeval x (f.map (algebraMap (PadicInt p) (Padic p))) = 0 := by
      rw [aeval_map_algebraMap,aeval_def]
      exact hfx
    have hle : spectralValue (f.map (algebraMap (PadicInt p) (Padic p))) ≤ 1 := by
      apply (spectralValue_le_one_iff hf').mpr
      intro i
      rw [coeff_map]
      exact (f.coeff i).property
    exact (norm_root_le_spectralValue (f := spectralAlgNorm (Padic p) E)
      (spectralAlgNorm_isPowMul (K := Padic p) (L := E)) (isNonarchimedean_spectralNorm (K := Padic p) (L := E))
      hf' hr).trans hle
  · intro hx
    let f := minpoly (Padic p) x
    have hf : f.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
    have hcoeff : ∀ i : ℕ, ‖f.coeff i‖ ≤ 1 := (spectralValue_le_one_iff hf).mp hx
    let g : (PadicInt p)[X] := ∑ i ∈ f.support, monomial i (⟨f.coeff i,hcoeff i⟩ : PadicInt p)
    have hg : g.map (algebraMap (PadicInt p) (Padic p)) = f := by
      dsimp only [g]
      rw [Polynomial.map_sum]
      calc
        _ = ∑ i ∈ f.support, monomial i (f.coeff i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Polynomial.map_monomial (algebraMap (PadicInt p) (Padic p))
        _ = f := sum_monomial_eq f
    have hgm : g.Monic := Polynomial.monic_of_injective
      (FaithfulSMul.algebraMap_injective (PadicInt p) (Padic p)) (hg.symm ▸ hf)
    refine ⟨g,hgm,?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap (Padic p),hg]
    exact minpoly.aeval (Padic p) x

open scoped NNReal
section NormedIntegers
variable (E : Type*) [NontriviallyNormedField E] [IsUltrametricDist E]
local instance : Valued E ℝ≥0 := NormedField.toValued

lemma compactSpace_norm_integer [ProperSpace E] : CompactSpace (Valued.integer E) := by
  apply isCompact_iff_compactSpace.mp
  change IsCompact {x : E | ‖x‖₊ ≤ 1}
  convert isCompact_closedBall (0 : E) 1 using 1
  ext x
  simp only [Metric.mem_closedBall,dist_zero_right,Set.mem_ofPred_eq]
  exact NNReal.coe_le_coe

lemma dvr_norm_integer [ProperSpace E] : IsDiscreteValuationRing (Valued.integer E) := by
  let : CompactSpace (Valued.integer E) := compactSpace_norm_integer E
  let : (Valued.v (R := E) (Γ₀ := ℝ≥0)).IsNontrivial :=
    inferInstanceAs (NormedField.valuation (K := E)).IsNontrivial
  exact Valued.integer.isDiscreteValuationRing_of_compactSpace

lemma finite_residue_norm_integer [ProperSpace E] :
    Finite (IsLocalRing.ResidueField (Valued.integer E)) := by
  let : CompactSpace (Valued.integer E) := compactSpace_norm_integer E
  let : (Valued.v (R := E) (Γ₀ := ℝ≥0)).RankOne :=
    inferInstanceAs (NormedField.valuation (K := E)).RankOne
  exact (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp
    inferInstance).2.2

variable (p : ℕ) [Fact p.Prime] [NormedAlgebra (Padic p) E]
    [FiniteDimensional (Padic p) E] [Algebra (PadicInt p) E]
    [IsScalarTower (PadicInt p) (Padic p) E]

 
def integralClosureEquivInteger :
    integralClosure (PadicInt p) E ≃+* Valued.integer E :=
  RingEquiv.subringCongr (show (integralClosure (PadicInt p) E).toSubring =
      Valued.integer E from by
    ext x
    change IsIntegral (PadicInt p) x ↔ ‖x‖₊ ≤ 1
    rw [isIntegral_padicInt_iff_spectralNorm_le_one p E,
      ← NormedAlgebra.norm_eq_spectralNorm (Padic p)]
    exact_mod_cast (NNReal.coe_le_coe :
      (‖x‖₊ : ℝ) ≤ ((1 : ℝ≥0) : ℝ) ↔ ‖x‖₊ ≤ 1))

lemma compactSpace_integralClosure_padic [ProperSpace E] :
    CompactSpace (integralClosure (PadicInt p) E) := by
  apply isCompact_iff_compactSpace.mp
  change IsCompact {x : E | IsIntegral (PadicInt p) x}
  have heq : {x : E | IsIntegral (PadicInt p) x} = Metric.closedBall 0 1 := by
    ext x
    simp only [Set.mem_ofPred_eq,Metric.mem_closedBall,dist_zero_right,
      isIntegral_padicInt_iff_spectralNorm_le_one p E,
      NormedAlgebra.norm_eq_spectralNorm (Padic p)]
  rw [heq]
  exact isCompact_closedBall 0 1

end NormedIntegers

 

theorem integralClosure_padicInt_isDiscreteValuationRing
    (p : ℕ) [Fact p.Prime] (E : Type*) [Field E] [Algebra (Padic p) E]
    [FiniteDimensional (Padic p) E] [Algebra (PadicInt p) E]
    [IsScalarTower (PadicInt p) (Padic p) E] :
    IsDiscreteValuationRing (integralClosure (PadicInt p) E) := by
  let : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField (Padic p) E
  let : NormedAlgebra (Padic p) E := spectralNorm.normedAlgebra (Padic p) E
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra (Padic p)
  let : Valued E ℝ≥0 := NormedField.toValued
  let : ProperSpace E := FiniteDimensional.proper (Padic p) E
  let : IsDiscreteValuationRing (Valued.integer E) := dvr_norm_integer E
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (integralClosureEquivInteger E p).symm

instance integralClosure_padicInt_dvr
    (p : ℕ) [Fact p.Prime] (E : Type*) [Field E] [Algebra (Padic p) E]
    [FiniteDimensional (Padic p) E] [Algebra (PadicInt p) E]
    [IsScalarTower (PadicInt p) (Padic p) E] :
    IsDiscreteValuationRing (integralClosure (PadicInt p) E) :=
  integralClosure_padicInt_isDiscreteValuationRing p E

instance integralClosure_padicInt_finite_residue
    (p : ℕ) [Fact p.Prime] (E : Type*) [Field E] [Algebra (Padic p) E]
    [FiniteDimensional (Padic p) E] [Algebra (PadicInt p) E]
    [IsScalarTower (PadicInt p) (Padic p) E] :
    Finite (IsLocalRing.ResidueField (integralClosure (PadicInt p) E)) := by
  let : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField (Padic p) E
  let : NormedAlgebra (Padic p) E := spectralNorm.normedAlgebra (Padic p) E
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra (Padic p)
  let : Valued E ℝ≥0 := NormedField.toValued
  let : ProperSpace E := FiniteDimensional.proper (Padic p) E
  let : Finite (IsLocalRing.ResidueField (Valued.integer E)) := finite_residue_norm_integer E
  exact Finite.of_equiv _ (IsLocalRing.ResidueField.mapEquiv
    (integralClosureEquivInteger E p).symm).toEquiv

open Polynomial
open scoped BigOperators

lemma isIntegral_pi_iff {R : Type*} [CommRing R] {I : Type*} [Finite I]
    {A : I → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] (x : ∀ i, A i) :
    IsIntegral R x ↔ ∀ i, IsIntegral R (x i) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  constructor
  · intro hx i
    exact hx.map (Pi.evalAlgHom R A i)
  · intro h
    choose f hf hx using h
    refine ⟨∏ i, f i, monic_prod_of_monic _ _ (fun i _ => hf i), ?_⟩
    rw [← aeval_def]
    ext i
    rw [aeval_pi_apply₂,map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hx i)

 
def integralClosurePiEquiv {R : Type*} [CommRing R] {I : Type*} [Finite I]
    (A : I → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] :
    integralClosure R (∀ i, A i) ≃ₐ[R] ∀ i, integralClosure R (A i) where
  toFun x i := ⟨x.1 i,(isIntegral_pi_iff x.1).mp x.2 i⟩
  invFun y := ⟨fun i => (y i).1,(isIntegral_pi_iff _).mpr (fun i => (y i).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

 
def integralClosureEquiv {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) :
    integralClosure R A ≃ₐ[R] integralClosure R B where
  toFun x := ⟨e x.1,x.2.map e⟩
  invFun y := ⟨e.symm y.1,y.2.map e.symm⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)
  map_mul' x y := Subtype.ext (map_mul e x.1 y.1)
  map_add' x y := Subtype.ext (map_add e x.1 y.1)
  commutes' r := Subtype.ext (e.commutes r)

 
lemma localAlgebra_etale (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K] :
    Algebra.Etale (Padic p) (LocalAlgebra p K) := by
  let : Algebra.FormallyEtale ℚ K := Algebra.FormallyEtale.of_isSeparable ℚ K
  let : Algebra.Etale ℚ K :=
    { finitePresentation := Algebra.FinitePresentation.of_finiteType.mp inferInstance }
  infer_instance

 
theorem localAlgebra_exists_product (p : ℕ) [Fact p.Prime] (K : Type u)
    [Field K] [NumberField K] :
    ∃ (I : Type u) (_ : Finite I) (E : I → Type u) (_ : ∀ i, Field (E i))
      (_ : ∀ i, Algebra (Padic p) (E i))
      (_ : ∀ i, FiniteDimensional (Padic p) (E i)),
      Nonempty (LocalAlgebra p K ≃ₐ[Padic p] Π i, E i) := by
  let : Algebra.Etale (Padic p) (LocalAlgebra p K) := localAlgebra_etale p K
  obtain ⟨I,hI,E,hE,hA,e,hsep⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod (Padic p) (LocalAlgebra p K)).mp
      inferInstance
  let : FiniteDimensional (Padic p) (∀ i, E i) :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  have hdim (i : I) : FiniteDimensional (Padic p) (E i) :=
    Module.Finite.of_surjective (LinearMap.proj i) (Function.surjective_eval i)
  exact ⟨I,hI,E,hE,hA,hdim,⟨e⟩⟩

open IsDiscreteValuationRing IsLocalRing Module

 
lemma cardQuot_span_prime_of_free (p : ℕ) [Fact p.Prime]
    (R : Type*) [CommRing R] [Algebra (PadicInt p) R]
    [Module.Free (PadicInt p) R] [Module.Finite (PadicInt p) R] :
    (Ideal.span {(p : R)}).cardQuot = p ^ Module.finrank (PadicInt p) R := by
  classical
  let b := Module.Free.chooseBasis (PadicInt p) R
  let h : R →+ (Module.Free.ChooseBasisIndex (PadicInt p) R → ZMod p) :=
    { toFun := fun x i => PadicInt.toZMod (b.equivFun x i)
      map_zero' := by ext i; simp
      map_add' := by intro x y; ext i; simp }
  have hs : Function.Surjective h := by
    intro x
    choose y hy using fun i => ZMod.ringHom_surjective (PadicInt.toZMod (p := p)) (x i)
    refine ⟨b.equivFun.symm y,?_⟩
    ext i
    change PadicInt.toZMod (b.equivFun (b.equivFun.symm y) i) = x i
    rw [LinearEquiv.apply_symm_apply]
    exact hy i
  have hsm (x : R) : (p : R) * x = (p : PadicInt p) • x := by simp [Algebra.smul_def]
  have hk : h.ker = (Ideal.span {(p : R)}).toAddSubgroup := by
    ext x
    change h x = 0 ↔ x ∈ Ideal.span {(p : R)}
    rw [Ideal.mem_span_singleton]
    constructor
    · intro hx
      have hd (i) : (p : PadicInt p) ∣ b.equivFun x i := by
        have H := congrFun hx i
        change PadicInt.toZMod (b.equivFun x i) = 0 at H
        rw [← RingHom.mem_ker,PadicInt.ker_toZMod,PadicInt.maximalIdeal_eq_span_p,
          Ideal.mem_span_singleton] at H
        exact H
      choose y hy using hd
      refine ⟨b.equivFun.symm y,?_⟩
      change x = (p : R) * b.equivFun.symm y
      rw [hsm]
      apply b.equivFun.injective
      ext i
      simpa only [map_smul,LinearEquiv.apply_symm_apply,Pi.smul_apply,smul_eq_mul] using hy i
    · rintro ⟨y,rfl⟩
      ext i
      change PadicInt.toZMod (b.equivFun ((p : R) * y) i) = 0
      rw [hsm]
      simp only [map_smul,Pi.smul_apply,smul_eq_mul,map_mul,map_natCast,ZMod.natCast_self,zero_mul]
  change (Ideal.span {(p : R)}).toAddSubgroup.index = _
  rw [← hk,AddSubgroup.index_ker,AddMonoidHom.range_eq_top.mpr hs]
  simp [Module.finrank_eq_card_basis b]

 
theorem finite_padic_dvr_degree
    (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Algebra (PadicInt p) R]
    [Module.Finite (PadicInt p) R] [FaithfulSMul (PadicInt p) R]
    [Finite (ResidueField R)] :
    ∃ e f : ℕ, 0 < e ∧ 0 < f ∧ addVal R (algebraMap (PadicInt p) R p) = e ∧
      Nat.card (ResidueField R) = p^f ∧ e*f = Module.finrank (PadicInt p) R := by
  let h := (ResidueField.map (algebraMap (PadicInt p) R)).comp (PadicInt.residueField (p := p)).symm.toRingHom
  let : Algebra (ZMod p) (ResidueField R) := h.toAlgebra
  let : Module.Finite (ZMod p) (ResidueField R) := Module.Finite.of_finite
  let f := Module.finrank (ZMod p) (ResidueField R)
  have hf : 0 < f := Module.finrank_pos
  have hc : Nat.card (ResidueField R) = p^f := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p)]
    simp [f]
  have hp0 : (p : PadicInt p) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpR : algebraMap (PadicInt p) R p ≠ 0 := by
    intro H
    apply hp0
    apply FaithfulSMul.algebraMap_injective (PadicInt p) R
    simpa using H
  have hefin : addVal R (algebraMap (PadicInt p) R p) ≠ ⊤ := addVal_eq_top_iff.not.mpr hpR
  let e := (addVal R (algebraMap (PadicInt p) R p)).toNat
  have he : addVal R (algebraMap (PadicInt p) R p) = e := (ENat.natCast_toNat hefin).symm
  have hen : e ≠ 0 := by
    intro he0
    have hu : IsUnit (algebraMap (PadicInt p) R p) := addVal_eq_zero_iff.mp (by simpa [he0] using he)
    have hu' := (isUnit_map_iff (algebraMap (PadicInt p) R) (p : PadicInt p)).mp hu
    have : ‖(p : PadicInt p)‖ < 1 := by
      rw [PadicInt.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
    exact (ne_of_lt this) (PadicInt.isUnit_iff.mp hu')
  have hspan : Ideal.span {(p : R)} = IsLocalRing.maximalIdeal R ^ e := by
    obtain ⟨π,hπ⟩ := exists_irreducible R
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
    ext x
    rw [Ideal.mem_span_singleton,Ideal.mem_span_singleton,← addVal_le_iff_dvd,← addVal_le_iff_dvd,hπ.addVal_pow]
    rw [show addVal R (p : R) = (e : ℕ∞) by simpa only [map_natCast] using he]
  have hdim : e*f = Module.finrank (PadicInt p) R := by
    have H := cardQuot_span_prime_of_free p R
    rw [hspan,cardQuot_pow_of_prime (fun hz => IsDiscreteValuationRing.not_isField R
        (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hz)),Submodule.cardQuot_apply] at H
    change (Nat.card (ResidueField R)) ^ e = p ^ Module.finrank (PadicInt p) R at H
    rw [hc,← pow_mul,mul_comm f e] at H
    exact (Nat.pow_right_injective (Fact.out : p.Prime).one_lt) H
  exact ⟨e,f,Nat.pos_iff_ne_zero.mpr hen,hf,he,hc,hdim⟩

 

theorem completedMaximalOrder_exists_dvr_product
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K] :
    ∃ (I : Type u) (_ : Finite I) (R : I → Type u) (_ : ∀ i, CommRing (R i))
      (_ : ∀ i, IsDomain (R i)) (_ : ∀ i, IsDiscreteValuationRing (R i))
      (_ : ∀ i, Algebra (PadicInt p) (R i))
      (_ : ∀ i, Finite (IsLocalRing.ResidueField (R i))),
      Nonempty (completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] Π i, R i) := by
  obtain ⟨I,hI,E,hE,hA,hdim,⟨e⟩⟩ := localAlgebra_exists_product p K
  let (i : I) : Algebra (PadicInt p) (E i) :=
    ((algebraMap (Padic p) (E i)).comp (algebraMap (PadicInt p) (Padic p))).toAlgebra
  let (i : I) : IsScalarTower (PadicInt p) (Padic p) (E i) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let R (i : I) : Type u := integralClosure (PadicInt p) (E i)
  refine ⟨I,hI,R,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,?_⟩
  refine ⟨(Subalgebra.equivOfEq _ _ (completedMaximalOrder_eq_integralClosure p)).trans ?_⟩
  exact (integralClosureEquiv (e.restrictScalars (PadicInt p))).trans
    (integralClosurePiEquiv E)

 
def completedLocalIntegralEquiv
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K]
    {I : Type u} [Finite I] (E : I → Type u) [∀ i, Field (E i)]
    [∀ i, Algebra (Padic p) (E i)] [∀ i, Algebra (PadicInt p) (E i)]
    [∀ i, IsScalarTower (PadicInt p) (Padic p) (E i)]
    (e : LocalAlgebra p K ≃ₐ[Padic p] Π i, E i) :
    completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] Π i, integralClosure (PadicInt p) (E i) :=
  (Subalgebra.equivOfEq _ _ (completedMaximalOrder_eq_integralClosure p)).trans
    ((integralClosureEquiv (e.restrictScalars (PadicInt p))).trans
      (integralClosurePiEquiv E))

lemma continuous_completedLocalIntegralEquiv
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K]
    {I : Type u} [Finite I] (E : I → Type u) [∀ i, NormedField (E i)]
    [∀ i, NormedAlgebra (Padic p) (E i)] [∀ i, Algebra (PadicInt p) (E i)]
    [∀ i, IsScalarTower (PadicInt p) (Padic p) (E i)]
    (e : LocalAlgebra p K ≃ₐ[Padic p] Π i, E i) :
    Continuous (completedLocalIntegralEquiv p K E e) := by
  have hc : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  apply continuous_pi
  intro i
  exact ((continuous_apply i).comp (hc.comp continuous_subtype_val)).subtype_mk _

lemma continuous_completedLocalIntegralEquiv_symm
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K]
    {I : Type u} [Finite I] (E : I → Type u) [∀ i, NormedField (E i)]
    [∀ i, NormedAlgebra (Padic p) (E i)] [∀ i, Algebra (PadicInt p) (E i)]
    [∀ i, IsScalarTower (PadicInt p) (Padic p) (E i)]
    [∀ i, FiniteDimensional (Padic p) (E i)]
    (e : LocalAlgebra p K ≃ₐ[Padic p] Π i, E i) :
    Continuous (completedLocalIntegralEquiv p K E e).symm := by
  let : Fintype I := Fintype.ofFinite I
  let (i : I) : IsModuleTopology (Padic p) (E i) := isModuleTopologyOfFiniteDimensional
  have hc : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  exact (hc.comp (continuous_pi (fun i => continuous_subtype_val.comp (continuous_apply i)))).subtype_mk _

instance completedMaximalOrderModuleFinite
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K] :
    Module.Finite (PadicInt p) (completedMaximalOrder (K := K) p) :=
  Module.Finite.of_fg (completedFractionalIdeal_fg p (1 : FractionalIdeal (𝓞 K)⁰ K))

lemma completedMaximalOrder_finrank
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K] :
    Module.finrank (PadicInt p) (completedMaximalOrder (K := K) p) = Module.finrank ℚ K := by
  let M := fractionalIdealFullLattice (K := K) rfl (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  let e : completedLattice p M ≃ₗ[PadicInt p] completedMaximalOrder (K := K) p :=
    { toFun := fun x => ⟨x.val, x.property⟩
      invFun := fun x => ⟨x.val, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  simpa only [Fintype.card_fin] using
    Module.finrank_eq_card_basis ((completedLatticeBasis M rfl p).map e)

 

theorem completedMaximalOrder_exists_topological_dvr_product
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K] :
    ∃ (I : Type u) (_ : Finite I) (R : I → Type u) (_ : ∀ i, CommRing (R i))
      (_ : ∀ i, IsDomain (R i)) (_ : ∀ i, IsDiscreteValuationRing (R i))
      (_ : ∀ i, Algebra (PadicInt p) (R i))
      (_ : ∀ i, Finite (IsLocalRing.ResidueField (R i)))
      (_ : ∀ i, TopologicalSpace (R i)) (_ : ∀ i, IsTopologicalRing (R i))
      (_ : ∀ i, CompactSpace (R i)) (_ : ∀ i, T2Space (R i))
      (_ : ∀ i, SecondCountableTopology (R i))
      (_ : ∀ i, Module.Finite (PadicInt p) (R i))
      (_ : ∀ i, FaithfulSMul (PadicInt p) (R i))
      (e : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] Π i, R i),
      Continuous e ∧ Continuous e.symm := by
  obtain ⟨I,hI,E,hE,hA,hdim,⟨e⟩⟩ := localAlgebra_exists_product p K
  let (i : I) : Algebra (PadicInt p) (E i) :=
    ((algebraMap (Padic p) (E i)).comp (algebraMap (PadicInt p) (Padic p))).toAlgebra
  let (i : I) : IsScalarTower (PadicInt p) (Padic p) (E i) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let (i : I) : NontriviallyNormedField (E i) := spectralNorm.nontriviallyNormedField (Padic p) (E i)
  let (i : I) : NormedAlgebra (Padic p) (E i) := spectralNorm.normedAlgebra (Padic p) (E i)
  let (i : I) : IsUltrametricDist (E i) := IsUltrametricDist.of_normedAlgebra (Padic p)
  let (i : I) : ProperSpace (E i) := FiniteDimensional.proper (Padic p) (E i)
  let (i : I) : SecondCountableTopology (E i) := by
    let b := Module.Free.chooseBasis (Padic p) (E i)
    let h : (E i) ≃L[Padic p] (Module.Free.ChooseBasisIndex (Padic p) (E i) → Padic p) :=
      b.equivFun.toContinuousLinearEquiv
    exact h.toHomeomorph.secondCountableTopology
  let R (i : I) : Type u := integralClosure (PadicInt p) (E i)
  let (i : I) : CompactSpace (R i) := compactSpace_integralClosure_padic (E i) p
  let eR := completedLocalIntegralEquiv p K E e
  let (i : I) : Module.Finite (PadicInt p) (R i) := by
    let h : completedMaximalOrder (K := K) p →ₗ[PadicInt p] R i :=
      (LinearMap.proj i).comp eR.toLinearMap
    apply Module.Finite.of_surjective h
    intro x
    classical
    exact ⟨eR.symm (Function.update (fun _ => 0) i x), by simp [h]⟩
  let (i : I) : FaithfulSMul (PadicInt p) (R i) := by
    apply (faithfulSMul_iff_algebraMap_injective _ _).mpr
    intro x y hxy
    have hxy' := congrArg (fun x : R i => (x : E i)) hxy
    change algebraMap (PadicInt p) (E i) x = algebraMap (PadicInt p) (E i) y at hxy'
    exact Subtype.coe_injective ((algebraMap (Padic p) (E i)).injective hxy')
  refine ⟨I,hI,R,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,
    inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,
    completedLocalIntegralEquiv p K E e,?_,?_⟩
  · exact continuous_completedLocalIntegralEquiv p K E e
  · exact continuous_completedLocalIntegralEquiv_symm p K E e

 

theorem completedMaximalOrder_exists_full_local_model
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K] :
    ∃ (I : Type u) (_ : Fintype I) (R : I → Type u) (_ : ∀ i, CommRing (R i))
      (_ : ∀ i, IsDomain (R i)) (_ : ∀ i, IsDiscreteValuationRing (R i))
      (_ : ∀ i, Algebra (PadicInt p) (R i))
      (_ : ∀ i, Finite (IsLocalRing.ResidueField (R i)))
      (_ : ∀ i, TopologicalSpace (R i)) (_ : ∀ i, IsTopologicalRing (R i))
      (_ : ∀ i, CompactSpace (R i)) (_ : ∀ i, T2Space (R i))
      (_ : ∀ i, SecondCountableTopology (R i))
      (E : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] Π i, R i)
      (e f : I → ℕ), Continuous E ∧ Continuous E.symm ∧
      (∀ i, 0 < e i) ∧ (∀ i, 0 < f i) ∧
      (∀ i, addVal (R i) (algebraMap (PadicInt p) (R i) p) = e i) ∧
      (∀ i, Nat.card (IsLocalRing.ResidueField (R i)) = p ^ f i) ∧
      ∑ i, f i * e i = Module.finrank ℚ K := by
  obtain ⟨I,hI,R,hR,hd,hDVR,hA,hk,hT,hTR,hc,ht,hsc,hfin,hfaith,E,hE,hE'⟩ :=
    completedMaximalOrder_exists_topological_dvr_product p K
  let : Fintype I := Fintype.ofFinite I
  choose e f he hf hv hk' hef using fun i => finite_padic_dvr_degree p (R i)
  refine ⟨I,inferInstance,R,hR,hd,hDVR,hA,hk,hT,hTR,hc,ht,hsc,E,e,f,hE,hE',he,hf,hv,hk',?_⟩
  calc
    ∑ i, f i * e i = ∑ i, Module.finrank (PadicInt p) (R i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Nat.mul_comm _ _).trans (hef i)
    _ = Module.finrank (PadicInt p) (Π i, R i) := (Module.finrank_pi_fintype _).symm
    _ = Module.finrank (PadicInt p) (completedMaximalOrder (K := K) p) := E.toLinearEquiv.finrank_eq.symm
    _ = Module.finrank ℚ K := completedMaximalOrder_finrank p K

 
lemma ideal_span_comap_top_of_mul {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (A : Subalgebra R B) (L : Submodule R B) (hL : L ≤ A.toSubmodule)
    (hsat : A.toSubmodule * L = A.toSubmodule) :
    Ideal.span ((L.comap A.val.toLinearMap) : Set A) = ⊤ := by
  let J := Ideal.span ((L.comap A.val.toLinearMap) : Set A)
  have hmul : A.toSubmodule * L ≤ (J.restrictScalars R).map A.val.toLinearMap := by
    apply Submodule.mul_le.mpr
    intro a ha b hb
    refine ⟨(⟨a,ha⟩ : A) * ⟨b,hL hb⟩, ?_, rfl⟩
    exact J.mul_mem_left _ (Ideal.subset_span hb)
  rw [hsat] at hmul
  obtain ⟨x,hx,hxv⟩ := hmul (show (1 : B) ∈ A.toSubmodule from A.one_mem)
  apply (Ideal.eq_top_iff_one _).mpr
  have hx1 : x = 1 := Subtype.ext hxv
  exact hx1 ▸ hx

 
lemma ideal_span_map_equiv_top {S R T : Type*} [CommRing S] [CommRing R] [CommRing T]
    [Algebra S R] [Algebra S T] (e : R ≃ₐ[S] T)
    (L : Submodule S R) (hL : Ideal.span (L : Set R) = ⊤) :
    Ideal.span (L.map e.toLinearMap : Set T) = ⊤ := by
  rw [Submodule.map_coe]
  change Ideal.span (e.toRingHom '' (L : Set R)) = ⊤
  rw [← Ideal.map_span, hL, Ideal.map_top]

lemma cardQuot_map_equiv {S R T : Type*} [CommRing S] [AddCommGroup R] [AddCommGroup T]
    [Module S R] [Module S T] (e : R ≃ₗ[S] T) (L : Submodule S R) :
    (L.map e.toLinearMap).cardQuot = L.cardQuot := by
  exact Nat.card_congr (Submodule.Quotient.equiv L (L.map e.toLinearMap) e rfl).symm.toEquiv

 
def integralNormalizedModule {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime] :
    Submodule (PadicInt p) (completedMaximalOrder (K := K) p) :=
  (normalizedLocalModule M p).comap (completedMaximalOrder (K := K) p).val.toLinearMap

lemma integralNormalizedModule_saturated {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime] :
    Ideal.span (integralNormalizedModule M p : Set (completedMaximalOrder (K := K) p)) = ⊤ :=
  ideal_span_comap_top_of_mul _ _ (normalizedLocalModule_le M p)
    (normalizedLocalModule_saturation M p)

lemma integralNormalizedModule_open {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (p : ℕ) [Fact p.Prime] :
    IsOpen (integralNormalizedModule M p : Set (completedMaximalOrder (K := K) p)) := by
  change IsOpen (Subtype.val ⁻¹' (normalizedLocalModule M p : Set (LocalAlgebra p K)))
  apply IsOpen.preimage continuous_subtype_val
  unfold normalizedLocalModule
  rw [Submodule.coe_pointwise_smul]
  exact (completedLattice_open M hn p).smul (idealLocalGenerator p (saturationIdealUnit M))⁻¹

lemma integralNormalizedModule_finiteQuotient {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (p : ℕ) [Fact p.Prime] :
    Finite (completedMaximalOrder (K := K) p ⧸ integralNormalizedModule M p) :=
  AddSubgroup.quotient_finite_of_isOpen (integralNormalizedModule M p).toAddSubgroup
    (integralNormalizedModule_open M hn p)

lemma integralNormalizedModule_cardQuot {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime] :
    (integralNormalizedModule M p).cardQuot =
      (completedLattice p M).toAddSubgroup.relIndex
        (completedFractionalIdeal p (saturationFractionalIdeal M)).toAddSubgroup := by
  change (normalizedLocalModule M p).toAddSubgroup.relIndex
    (completedMaximalOrder (K := K) p).toSubmodule.toAddSubgroup = _
  have H := local_relIndex_smul p (idealLocalGenerator p (saturationIdealUnit M))⁻¹
    (completedLattice p M) (completedFractionalIdeal p (saturationFractionalIdeal M))
  rw [saturationLocalGenerator_spec, ← mul_smul, Units.inv_mul, one_smul] at H
  rw [saturationLocalGenerator_spec]
  exact H

lemma saturationIndex_eq_prod_integralNormalizedModule {n : ℕ} {K : Type*}
    [Field K] [NumberField K] (M : FullLattice n K) (hn : Module.finrank ℚ K = n) :
    saturationIndex M = ∏ p : labelPrimes M, (integralNormalizedModule M p.val).cardQuot := by
  apply (saturationIndex_eq_prod_local M hn).trans
  apply Finset.prod_congr rfl
  intro p _
  exact (integralNormalizedModule_cardQuot M p.val).symm

 

def modelLocalModule {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime]
    {R : Type*} [CommRing R] [Algebra (PadicInt p) R]
    (E : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] R) : Submodule (PadicInt p) R :=
  (integralNormalizedModule M p).map E.toLinearMap

lemma modelLocalModule_saturated {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime]
    {R : Type*} [CommRing R] [Algebra (PadicInt p) R]
    (E : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] R) :
    Ideal.span (modelLocalModule M p E : Set R) = ⊤ :=
  ideal_span_map_equiv_top E _ (integralNormalizedModule_saturated M p)

lemma modelLocalModule_open {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (p : ℕ) [Fact p.Prime]
    {R : Type*} [CommRing R] [Algebra (PadicInt p) R] [TopologicalSpace R]
    (E : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] R) (hE : Continuous E.symm) :
    IsOpen (modelLocalModule M p E : Set R) := by
  rw [modelLocalModule, Submodule.map_equiv_eq_comap_symm E.toLinearEquiv]
  exact (integralNormalizedModule_open M hn p).preimage hE

lemma modelLocalModule_finiteQuotient {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (p : ℕ) [Fact p.Prime]
    {R : Type*} [CommRing R] [Algebra (PadicInt p) R]
    (E : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] R) :
    Finite (R ⧸ modelLocalModule M p E) := by
  let := integralNormalizedModule_finiteQuotient M hn p
  exact Finite.of_equiv _ (Submodule.Quotient.equiv _ _ E.toLinearEquiv rfl).toEquiv

lemma modelLocalModule_cardQuot {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime]
    {R : Type*} [CommRing R] [Algebra (PadicInt p) R]
    (E : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] R) :
    (modelLocalModule M p E).cardQuot = (integralNormalizedModule M p).cardQuot :=
  cardQuot_map_equiv E.toLinearEquiv _

open MeasureTheory
open scoped ENNReal
 
theorem haar_stabilizer_eq_inv_card {G α : Type*} [Group G] [MulAction G α]
    [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (x : α) [Finite (MulAction.orbit G x)]
    (hx : MeasurableSet (MulAction.stabilizer G x : Set G)) :
    μ (MulAction.stabilizer G x : Set G) = (Nat.card (MulAction.orbit G x) : ℝ≥0∞)⁻¹ := by
  let : Nonempty (MulAction.orbit G x) := ⟨⟨x,MulAction.mem_orbit_self x⟩⟩
  let e := MulAction.orbitEquivQuotientStabilizer G x
  let : Finite (G ⧸ MulAction.stabilizer G x) := Finite.of_equiv _ e
  let : (MulAction.stabilizer G x).FiniteIndex := ⟨Nat.card_pos.ne'⟩
  have hc : (Nat.card (MulAction.orbit G x) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have he : (MulAction.stabilizer G x).index = Nat.card (MulAction.orbit G x) :=
    (Nat.card_congr e).symm
  rw [← one_div (Nat.card (MulAction.orbit G x) : ℝ≥0∞)]
  apply (ENNReal.eq_div_iff hc (by simp)).mpr
  simpa only [he, measure_univ] using (MulAction.stabilizer G x).index_mul_measure hx μ

 
theorem haar_orbit_fiber {G α : Type*} [Group G] [MulAction G α]
    [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (x y : α) [Finite (MulAction.orbit G x)]
    (hx : MeasurableSet (MulAction.stabilizer G x : Set G))
    (hy : y ∈ MulAction.orbit G x) :
    μ {g : G | g • x = y} = (Nat.card (MulAction.orbit G x) : ℝ≥0∞)⁻¹ := by
  obtain ⟨a,rfl⟩ := hy
  have he : {g : G | g • x = a • x} =
      (fun g : G => a⁻¹ * g) ⁻¹' (MulAction.stabilizer G x : Set G) := by
    ext g
    change (g • x = a • x) ↔ (a⁻¹ * g) • x = x
    rw [mul_smul,inv_smul_eq_iff]
  rw [he,measure_preimage_mul,haar_stabilizer_eq_inv_card μ x hx]

lemma measurable_orbit_fiber {G α : Type*} [Group G] [MulAction G α]
    [MeasurableSpace G] [MeasurableMul G]
    (x y : α) (hx : MeasurableSet (MulAction.stabilizer G x : Set G))
    (hy : y ∈ MulAction.orbit G x) : MeasurableSet {g : G | g • x = y} := by
  obtain ⟨a,rfl⟩ := hy
  have he : {g : G | g • x = a • x} =
      (fun g : G => a⁻¹ * g) ⁻¹' (MulAction.stabilizer G x : Set G) := by
    ext g
    change (g • x = a • x) ↔ (a⁻¹ * g) • x = x
    rw [mul_smul,inv_smul_eq_iff]
  rw [he]
  exact hx.preimage (measurable_const_mul _)

 
theorem haar_orbit_subset {G α : Type*} [Group G] [MulAction G α]
    [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (x : α) [Finite (MulAction.orbit G x)]
    (hx : MeasurableSet (MulAction.stabilizer G x : Set G)) (S : Set α) :
    μ {g : G | g • x ∈ S} =
      (Nat.card {y : MulAction.orbit G x // y.val ∈ S} : ℝ≥0∞) /
        Nat.card (MulAction.orbit G x) := by
  classical
  let β := {y : MulAction.orbit G x // y.val ∈ S}
  let : Fintype β := Fintype.ofFinite β
  have he : {g : G | g • x ∈ S} = ⋃ y : β, {g : G | g • x = y.val.val} := by
    ext g
    constructor
    · intro hg
      exact Set.mem_iUnion.mpr ⟨⟨⟨g • x,⟨g,rfl⟩⟩,hg⟩,rfl⟩
    · intro hg
      obtain ⟨y,hy⟩ := Set.mem_iUnion.mp hg
      change g • x = y.val.val at hy
      change g • x ∈ S
      rw [hy]
      exact y.property
  rw [he,measure_iUnion]
  · simp only [haar_orbit_fiber μ x _ hx (Subtype.property _),tsum_fintype,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Nat.card_eq_fintype_card,div_eq_mul_inv]
    rfl
  · intro a b hab
    apply Set.disjoint_left.mpr
    intro g ha hb
    apply hab
    apply Subtype.ext
    apply Subtype.ext
    exact ha.symm.trans hb
  · intro y
    exact measurable_orbit_fiber x y.val hx y.val.property

 
def localChoiceBase {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℕ) [Fact p.Prime] : Submodule (PadicInt p) (LocalAlgebra p K) :=
  (idealLocalGenerator p I : LocalAlgebra p K) • normalizedLocalModule M p

lemma localUnit_smul_base {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℕ) [Fact p.Prime] (z : (completedMaximalOrder (K := K) p)ˣ) :
    z • localChoiceBase M I p =
      ((idealLocalGenerator p I : LocalAlgebra p K) *
        ((z : completedMaximalOrder (K := K) p) : LocalAlgebra p K)) • normalizedLocalModule M p := by
  change ((z : completedMaximalOrder (K := K) p) : LocalAlgebra p K) •
    ((idealLocalGenerator p I : LocalAlgebra p K) • normalizedLocalModule M p) = _
  rw [smul_smul,mul_comm]

lemma localModuleChoices_eq_orbit {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℕ) [Fact p.Prime] :
    MulAction.orbit (completedMaximalOrder (K := K) p)ˣ (localChoiceBase M I p) =
      localModuleChoices M I p := by
  ext N
  simp only [MulAction.mem_orbit_iff,localModuleChoices,Set.mem_range,localUnit_smul_base]

lemma localChoiceStabilizer_measurable {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (p : ℕ) [Fact p.Prime] :
    MeasurableSet (MulAction.stabilizer (completedMaximalOrder (K := K) p)ˣ
      (localChoiceBase M I p) : Set (completedMaximalOrder (K := K) p)ˣ) := by
  let N := localChoiceBase M I p
  have hN : IsClosed (N : Set (LocalAlgebra p K)) :=
    (compact_smul_submodule _ _ (normalizedLocalModule_compact M hn p)).isClosed
  let f : completedMaximalOrder (K := K) p →* LocalAlgebra p K :=
    (completedMaximalOrder (K := K) p).val.toMonoidHom
  have hf : Continuous f := continuous_subtype_val
  have h := (isClosed_unit_smul_submodule_eq N N hN hN).preimage
    (Units.continuous_map (f := f) hf)
  exact h.measurableSet

 
def localUnitHaarProbability {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] : Measure (completedMaximalOrder (K := K) p)ˣ :=
  Measure.haarMeasure (⟨⟨Set.univ,isCompact_univ⟩,by simp⟩ :
    TopologicalSpace.PositiveCompacts (completedMaximalOrder (K := K) p)ˣ)

instance localUnitHaarProbability_isProbability {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] : IsProbabilityMeasure (localUnitHaarProbability (K := K) p) := by
  constructor
  exact Measure.haarMeasure_self

instance localUnitHaarProbability_isHaar {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] : (localUnitHaarProbability (K := K) p).IsHaarMeasure :=
  inferInstanceAs (Measure.haarMeasure _).IsHaarMeasure

 

theorem localUnitHaarProbability_fiber {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (p : ℕ) [Fact p.Prime]
    (N : localModuleChoices M I p) :
    localUnitHaarProbability p {z : (completedMaximalOrder (K := K) p)ˣ |
      ((idealLocalGenerator p I : LocalAlgebra p K) *
        ((z : completedMaximalOrder (K := K) p) : LocalAlgebra p K)) • normalizedLocalModule M p = N.val} =
      (Nat.card (localModuleChoices M I p) : ℝ≥0∞)⁻¹ := by
  let G := (completedMaximalOrder (K := K) p)ˣ
  let : Finite (MulAction.orbit G (localChoiceBase M I p)) := by
    rw [localModuleChoices_eq_orbit]
    exact (localModuleChoices_finite M hn I p).to_subtype
  have hN : N.val ∈ MulAction.orbit G (localChoiceBase M I p) := by
    rw [localModuleChoices_eq_orbit]; exact N.property
  have h := haar_orbit_fiber (localUnitHaarProbability p) (localChoiceBase M I p) N.val
    (localChoiceStabilizer_measurable M hn I p) hN
  simpa only [localUnit_smul_base,localModuleChoices_eq_orbit] using h

 

theorem localUnitHaarProbability_containment {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (p : ℕ) [Fact p.Prime] (x : LocalAlgebra p K) :
    localUnitHaarProbability p {z : (completedMaximalOrder (K := K) p)ˣ |
      x ∈ ((idealLocalGenerator p I : LocalAlgebra p K) *
        ((z : completedMaximalOrder (K := K) p) : LocalAlgebra p K)) • normalizedLocalModule M p} =
      (Nat.card (localContainmentLabels M I p x) : ℝ≥0∞) / Nat.card (localModuleChoices M I p) := by
  let G := (completedMaximalOrder (K := K) p)ˣ
  let : Finite (MulAction.orbit G (localChoiceBase M I p)) := by
    rw [localModuleChoices_eq_orbit]
    exact (localModuleChoices_finite M hn I p).to_subtype
  have h := haar_orbit_subset (localUnitHaarProbability p) (localChoiceBase M I p)
    (localChoiceStabilizer_measurable M hn I p) {N | x ∈ N}
  have hc : Nat.card {y : MulAction.orbit G (localChoiceBase M I p) // x ∈ y.val} =
      Nat.card (localContainmentLabels M I p x) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (Set.equivOfEq (localModuleChoices_eq_orbit M I p))
      (fun _ => Iff.rfl)
  simp only [Set.mem_ofPred_eq] at h
  rw [hc] at h
  simpa only [localUnit_smul_base,localModuleChoices_eq_orbit] using h

lemma haar_smul_containment {G A : Type*} [Group G] [MulAction G A]
    [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (L : Set A) (u : G) (x : A) :
    μ {z : G | u • x ∈ z • L} = μ {z : G | x ∈ z • L} := by
  have he : {z : G | u • x ∈ z • L} =
      (fun z : G => u⁻¹ * z) ⁻¹' {z : G | x ∈ z • L} := by
    ext z
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,Set.mem_smul_set_iff_inv_smul_mem,
      mul_inv_rev,inv_inv,mul_smul]
  rw [he,measure_preimage_mul]

 
lemma local_generators_associated {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (u v : (LocalAlgebra p K)ˣ)
    (h : (u : LocalAlgebra p K) • (completedMaximalOrder (K := K) p).toSubmodule =
      (v : LocalAlgebra p K) • (completedMaximalOrder (K := K) p).toSubmodule) :
    ∃ z : (completedMaximalOrder (K := K) p)ˣ,
      (u : LocalAlgebra p K) =
        ((z : completedMaximalOrder (K := K) p) : LocalAlgebra p K) * v := by
  have hr : ((v⁻¹*u : (LocalAlgebra p K)ˣ) : LocalAlgebra p K) •
      (completedMaximalOrder (K := K) p).toSubmodule =
        (completedMaximalOrder (K := K) p).toSubmodule := by
    rw [Units.val_mul,← smul_smul,h,smul_smul,Units.inv_mul,one_smul]
  obtain ⟨z,hz⟩ := completedMaximalOrder_unit_of_smul_eq p (v⁻¹*u) hr
  refine ⟨z,?_⟩
  rw [hz,Units.val_mul,mul_right_comm,Units.inv_mul,one_mul]

lemma completedFractionalIdeal_generator_mul {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedFractionalIdeal p ((I*J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      ((idealLocalGenerator p I : LocalAlgebra p K) * idealLocalGenerator p J) •
        (completedMaximalOrder (K := K) p).toSubmodule := by
  rw [Units.val_mul,completedFractionalIdeal_mul,idealLocalGenerator_spec,idealLocalGenerator_spec]
  rw [← mul_smul_mul_comm]
  rw [(completedMaximalOrder (K := K) p).isIdempotentElem_toSubmodule.eq]

 

def localIdealWeight {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime]
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℝ≥0∞ :=
  localUnitHaarProbability p {z : (completedMaximalOrder (K := K) p)ˣ |
    (idealLocalGenerator p J : LocalAlgebra p K) ∈
      ((z : completedMaximalOrder (K := K) p) : LocalAlgebra p K) • normalizedLocalModule M p}

lemma localIdealWeight_eq_of_generator {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime]
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : (LocalAlgebra p K)ˣ)
    (hu : completedFractionalIdeal p (J : FractionalIdeal (𝓞 K)⁰ K) =
      (u : LocalAlgebra p K) • (completedMaximalOrder (K := K) p).toSubmodule) :
    localIdealWeight M p J =
      localUnitHaarProbability p {z : (completedMaximalOrder (K := K) p)ˣ |
        (u : LocalAlgebra p K) ∈
          ((z : completedMaximalOrder (K := K) p) : LocalAlgebra p K) • normalizedLocalModule M p} := by
  obtain ⟨v,hv⟩ := local_generators_associated p (idealLocalGenerator p J) u
    ((idealLocalGenerator_spec p J).symm.trans hu)
  unfold localIdealWeight
  rw [hv]
  exact haar_smul_containment (localUnitHaarProbability p)
    (normalizedLocalModule M p : Set (LocalAlgebra p K)) v u

 
def relativeElementIdeal {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : Kˣ) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  toPrincipalIdeal (𝓞 K) K a * I⁻¹

lemma relativeElementIdeal_generator {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : Kˣ) :
    completedFractionalIdeal p (relativeElementIdeal I a : FractionalIdeal (𝓞 K)⁰ K) =
      (((Units.map (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K).toMonoidHom a) *
        (idealLocalGenerator p I)⁻¹ : (LocalAlgebra p K)ˣ) : LocalAlgebra p K) •
          (completedMaximalOrder (K := K) p).toSubmodule := by
  let J := relativeElementIdeal I a
  let i := idealLocalGenerator p I
  let j := idealLocalGenerator p J
  let b := Units.map (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K).toMonoidHom a
  have hJI : J*I = toPrincipalIdeal (𝓞 K) K a := by dsimp [J,relativeElementIdeal]; simp
  have h : (j : LocalAlgebra p K) • ((i : LocalAlgebra p K) •
      (completedMaximalOrder (K := K) p).toSubmodule) = (b : LocalAlgebra p K) •
        (completedMaximalOrder (K := K) p).toSubmodule := by
    rw [smul_smul,← completedFractionalIdeal_generator_mul,hJI,coe_toPrincipalIdeal]
    change completedFractionalIdeal p (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)) =
      (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K) (a : K) •
        completedFractionalIdeal p 1
    simpa only [mul_one] using completedFractionalIdeal_singleton_mul p 1 (a : K)
  have H := congrArg (fun N : Submodule (PadicInt p) (LocalAlgebra p K) =>
    (↑(i⁻¹) : LocalAlgebra p K) • N) h
  rw [smul_smul,smul_smul,mul_right_comm,Units.inv_mul,one_mul] at H
  rw [idealLocalGenerator_spec]
  change (j : LocalAlgebra p K) • _ = _
  rw [H,smul_smul,mul_comm]
  rfl

 

theorem localContainment_eq_relativeIdealWeight
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : Kˣ) :
    (Nat.card (localContainmentLabels M I p
      ((Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K) (a : K))) : ℝ≥0∞) /
        Nat.card (localModuleChoices M I p) = localIdealWeight M p (relativeElementIdeal I a) := by
  rw [← localUnitHaarProbability_containment M hn I p]
  rw [localIdealWeight_eq_of_generator M p _ _ (relativeElementIdeal_generator p I a)]
  congr 1
  ext z
  let b : (LocalAlgebra p K)ˣ :=
    Units.map (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K).toMonoidHom a
  let i := idealLocalGenerator p I
  let R := completedMaximalOrder (K := K) p
  change (b : LocalAlgebra p K) ∈ ((i : LocalAlgebra p K) * ((z : R) : LocalAlgebra p K)) •
      normalizedLocalModule M p ↔
    ((b*i⁻¹ : (LocalAlgebra p K)ˣ) : LocalAlgebra p K) ∈
      ((z : R) : LocalAlgebra p K) • normalizedLocalModule M p
  rw [← smul_smul]
  change (b : LocalAlgebra p K) ∈ i • (((z : R) : LocalAlgebra p K) •
      (normalizedLocalModule M p : Set (LocalAlgebra p K))) ↔ _
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  change (↑(i⁻¹) : LocalAlgebra p K) * b ∈ _ ↔ _
  rw [Units.val_mul,mul_comm]
  rfl

 
def globalIdealWeight {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℝ≥0∞ :=
  ∏ p : labelPrimes M, localIdealWeight M p.val J

lemma localIdealWeight_le_one {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime]
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : localIdealWeight M p J ≤ 1 :=
  prob_le_one

lemma globalIdealWeight_le_one {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : globalIdealWeight M J ≤ 1 := by
  apply Finset.prod_le_one
  intro prime _
  exact localIdealWeight_le_one M prime.val J

 
theorem globalContainment_eq_relativeIdealWeight
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : Kˣ)
    (ha : (a : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K)) :
    (Nat.card {N : globalLabels M I // (a : K) ∈ N.val} : ℝ≥0∞) / Nat.card (globalLabels M I) =
      globalIdealWeight M (relativeElementIdeal I a) := by
  have hleft : (Nat.card {N : globalLabels M I // (a : K) ∈ N.val} : ℝ≥0∞) /
      Nat.card (globalLabels M I) ≠ ⊤ := by
    apply ENNReal.div_ne_top (by simp)
    exact_mod_cast (globalLabels_card_pos M hn I).ne'
  have hright : globalIdealWeight M (relativeElementIdeal I a) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (globalIdealWeight_le_one M _)
  apply (ENNReal.toReal_eq_toReal_iff' hleft hright).mp
  simp only [ENNReal.toReal_div,ENNReal.toReal_natCast,globalIdealWeight,ENNReal.toReal_prod]
  rw [globalContainmentProbability_eq_prod M hn I a ha]
  apply Finset.prod_congr rfl
  intro p _
  have h := congrArg ENNReal.toReal (localContainment_eq_relativeIdealWeight M hn p.val I a)
  simpa only [ENNReal.toReal_div,ENNReal.toReal_natCast,localContainmentProbability] using h

end PrimeDegreePackets
end
end

end OAI
