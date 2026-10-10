import OAI.Analysis.CharacterCriterion.BalancedSystem

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder


namespace KirchbergRordam

open scoped Matrix Kronecker ComplexOrder

abbrev M2 := CStarMatrix (Fin 2) (Fin 2) ℂ
abbrev M3 := CStarMatrix (Fin 3) (Fin 3) ℂ
abbrev M6 := CStarMatrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ


def leftMatrixAlgebra : Matrix (Fin 2) (Fin 2) ℂ →⋆ₐ[ℂ]
    Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ where
  toFun a := a ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)
  map_zero' := Matrix.zero_kronecker _
  map_one' := Matrix.one_kronecker_one
  map_add' a b := Matrix.add_kronecker _ _ _
  map_mul' a b := by
    simpa only [mul_one] using Matrix.mul_kronecker_mul a b
      (1 : Matrix (Fin 3) (Fin 3) ℂ) (1 : Matrix (Fin 3) (Fin 3) ℂ)
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.smul_kronecker,
      Matrix.one_kronecker_one]
  map_star' a := by
    change aᴴ ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ) = (a ⊗ₖ 1)ᴴ
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]


def rightMatrixAlgebra : Matrix (Fin 3) (Fin 3) ℂ →⋆ₐ[ℂ]
    Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ where
  toFun a := (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ a
  map_zero' := Matrix.kronecker_zero _
  map_one' := Matrix.one_kronecker_one
  map_add' a b := Matrix.kronecker_add _ _ _
  map_mul' a b := by
    simpa only [mul_one] using Matrix.mul_kronecker_mul
      (1 : Matrix (Fin 2) (Fin 2) ℂ) (1 : Matrix (Fin 2) (Fin 2) ℂ) a b
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.kronecker_smul,
      Matrix.one_kronecker_one]
  map_star' a := by
    change (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ aᴴ = (1 ⊗ₖ a)ᴴ
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]


def leftMatrix : M2 →⋆ₐ[ℂ] M6 :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    (leftMatrixAlgebra.comp CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom)


def rightMatrix : M3 →⋆ₐ[ℂ] M6 :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    (rightMatrixAlgebra.comp CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom)


def matrixEval (t : unitInterval) : C(unitInterval, M6) →⋆ₐ[ℂ] M6 where
  toFun f := f t
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl


def dimensionDropSubalgebra : StarSubalgebra ℂ C(unitInterval, M6) :=
  leftMatrix.range.comap (matrixEval 0) ⊓ rightMatrix.range.comap (matrixEval 1)

instance : FiniteDimensional ℂ M6 :=
  inferInstanceAs (FiniteDimensional ℂ (Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ))

instance dimensionDropClosed : IsClosed
    (dimensionDropSubalgebra : Set C(unitInterval, M6)) := by
  change IsClosed ((fun f : C(unitInterval, M6) => f 0) ⁻¹' (leftMatrix.range : Set M6) ∩
    (fun f : C(unitInterval, M6) => f 1) ⁻¹' (rightMatrix.range : Set M6))
  exact ((leftMatrix.range.toSubalgebra.toSubmodule.closed_of_finiteDimensional).preimage
    (continuous_eval_const (0 : unitInterval))).inter
    ((rightMatrix.range.toSubalgebra.toSubmodule.closed_of_finiteDimensional).preimage
    (continuous_eval_const (1 : unitInterval)))


abbrev DimensionDrop23 := dimensionDropSubalgebra

instance dropSubringClass : SubringClass
    (StarSubalgebra ℂ C(unitInterval, M6)) C(unitInterval, M6) :=
  StarSubalgebra.subringClass (R := ℂ) (A := C(unitInterval, M6))

instance : CStarAlgebra DimensionDrop23 :=
  StarSubalgebra.cstarAlgebra dimensionDropSubalgebra
example : Nontrivial DimensionDrop23 := inferInstance


def dropCoordinate : DimensionDrop23 :=
  ⟨⟨fun t => ((t : ℝ) : ℂ) • (1 : M6), by fun_prop⟩,
    by
      constructor
      · change ∃ a : M2, leftMatrix a = ((0 : unitInterval) : ℝ) • (1 : M6)
        exact ⟨0, by simp⟩
      · change ∃ a : M3, rightMatrix a = ((1 : unitInterval) : ℝ) • (1 : M6)
        exact ⟨1, by simp⟩⟩


def leftCone (a : M2) : DimensionDrop23 :=
  ⟨⟨fun t => (1 - ((t : ℝ) : ℂ)) • leftMatrix a, by fun_prop⟩,
    by
      constructor
      · refine ⟨a, ?_⟩
        change leftMatrix a = (1 - (((0 : unitInterval) : ℝ) : ℂ)) • leftMatrix a
        simp
      · refine ⟨0, ?_⟩
        change rightMatrix 0 = (1 - (((1 : unitInterval) : ℝ) : ℂ)) • leftMatrix a
        simp⟩


def rightCone (a : M3) : DimensionDrop23 :=
  ⟨⟨fun t => ((t : ℝ) : ℂ) • rightMatrix a, by fun_prop⟩,
    by
      constructor
      · refine ⟨0, ?_⟩
        change leftMatrix 0 = (((0 : unitInterval) : ℝ) : ℂ) • rightMatrix a
        simp
      · refine ⟨a, ?_⟩
        change rightMatrix a = (((1 : unitInterval) : ℝ) : ℂ) • rightMatrix a
        simp⟩


def matrixUnit {n : ℕ} (i j : Fin n) : CStarMatrix (Fin n) (Fin n) ℂ :=
  CStarMatrix.ofMatrixStarAlgEquiv (Matrix.single i j 1)

@[ext]
theorem drop_ext {f g : DimensionDrop23}
    (h : ∀ t, (f : C(unitInterval, M6)) t = (g : C(unitInterval, M6)) t) : f = g := by
  apply Subtype.ext
  exact ContinuousMap.ext h

@[simp]
theorem matrixUnit_mul {n : ℕ} (i j k : Fin n) :
    matrixUnit i j * matrixUnit j k = matrixUnit i k := by
  unfold matrixUnit
  rw [← map_mul]
  simp only [Matrix.single_mul_single_same, mul_one]

theorem matrixUnit_mul_self {n : ℕ} (i j : Fin n) (h : i ≠ j) :
    matrixUnit i j * matrixUnit i j = 0 := by
  unfold matrixUnit
  rw [← map_mul, Matrix.single_mul_single_of_ne (1 : ℂ) i j i h.symm (1 : ℂ), map_zero]

theorem leftCone_mul_self (a : M2) (ha : a * a = 0) :
    leftCone a * leftCone a = 0 := by
  apply drop_ext
  intro t
  change ((1 - ((t : ℝ) : ℂ)) • leftMatrix a) *
    ((1 - ((t : ℝ) : ℂ)) • leftMatrix a) = 0
  rw [smul_mul_smul, ← map_mul, ha, map_zero, smul_zero]

theorem rightCone_mul_self (a : M3) (ha : a * a = 0) :
    rightCone a * rightCone a = 0 := by
  apply drop_ext
  intro t
  change (((t : ℝ) : ℂ) • rightMatrix a) *
    (((t : ℝ) : ℂ) • rightMatrix a) = 0
  rw [smul_mul_smul, ← map_mul, ha, map_zero, smul_zero]

theorem matrixUnit_two_diagonal :
    matrixUnit (0 : Fin 2) 0 + matrixUnit 1 1 = 1 := by
  apply CStarMatrix.ext
  intro i j
  change Matrix.single (0 : Fin 2) 0 (1 : ℂ) i j + Matrix.single 1 1 1 i j =
    (1 : Matrix (Fin 2) (Fin 2) ℂ) i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.single]

theorem matrixUnit_three_diagonal :
    matrixUnit (0 : Fin 3) 0 + matrixUnit 1 1 + matrixUnit 2 2 = 1 := by
  apply CStarMatrix.ext
  intro i j
  change Matrix.single (0 : Fin 3) 0 (1 : ℂ) i j + Matrix.single 1 1 1 i j +
    Matrix.single 2 2 1 i j = (1 : Matrix (Fin 3) (Fin 3) ℂ) i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.single]

theorem drop_left_identity :
    leftCone (matrixUnit 0 1) * leftCone (matrixUnit 1 0) +
      leftCone (matrixUnit 1 0) * leftCone (matrixUnit 0 1) = (1 - dropCoordinate) ^ 2 := by
  apply drop_ext
  intro t
  let z : ℂ := (t : ℝ)
  change ((1-z) • leftMatrix (matrixUnit 0 1)) * ((1-z) • leftMatrix (matrixUnit 1 0)) +
    ((1-z) • leftMatrix (matrixUnit 1 0)) * ((1-z) • leftMatrix (matrixUnit 0 1)) =
      ((1 : M6) - z • 1) ^ 2
  rw [smul_mul_smul, smul_mul_smul, ← map_mul, ← map_mul,
    matrixUnit_mul, matrixUnit_mul, ← smul_add, ← map_add,
    matrixUnit_two_diagonal, map_one]
  have h : (1 : M6) - z • 1 = (1-z) • (1 : M6) := by rw [sub_smul, one_smul]
  rw [h, pow_two, smul_mul_smul, mul_one]

theorem drop_right_identity :
    rightCone (matrixUnit 0 1) * rightCone (matrixUnit 1 0) +
      rightCone (matrixUnit 1 0) * rightCone (matrixUnit 0 1) +
      rightCone (matrixUnit 2 0) * rightCone (matrixUnit 0 2) = dropCoordinate ^ 2 := by
  apply drop_ext
  intro t
  let z : ℂ := (t : ℝ)
  change (z • rightMatrix (matrixUnit 0 1)) * (z • rightMatrix (matrixUnit 1 0)) +
    (z • rightMatrix (matrixUnit 1 0)) * (z • rightMatrix (matrixUnit 0 1)) +
    (z • rightMatrix (matrixUnit 2 0)) * (z • rightMatrix (matrixUnit 0 2)) =
      (z • (1 : M6)) ^ 2
  rw [smul_mul_smul, smul_mul_smul, smul_mul_smul, ← map_mul, ← map_mul, ← map_mul,
    matrixUnit_mul, matrixUnit_mul, matrixUnit_mul, ← smul_add, ← smul_add,
    ← map_add, ← map_add, matrixUnit_three_diagonal, map_one,
    pow_two, smul_mul_smul, mul_one]


theorem dimensionDrop23_no_ringhom : IsEmpty (DimensionDrop23 →+* ℂ) := by
  refine ⟨fun f => ?_⟩
  have kill {x : DimensionDrop23} (hx : x * x = 0) : f x = 0 := by
    apply eq_zero_of_mul_self_eq_zero
    rw [← map_mul, hx, map_zero]
  have hL (i j : Fin 2) (h : i ≠ j) : f (leftCone (matrixUnit i j)) = 0 :=
    kill (leftCone_mul_self _ (matrixUnit_mul_self i j h))
  have hR (i j : Fin 3) (h : i ≠ j) : f (rightCone (matrixUnit i j)) = 0 :=
    kill (rightCone_mul_self _ (matrixUnit_mul_self i j h))
  have hl : f (1 - dropCoordinate) = 0 := by
    apply eq_zero_of_pow_eq_zero (n := 2)
    rw [← map_pow, ← drop_left_identity]
    simp only [map_add, map_mul, hL 0 1 (by decide), hL 1 0 (by decide), zero_mul, add_zero]
  have hr : f dropCoordinate = 0 := by
    apply eq_zero_of_pow_eq_zero (n := 2)
    rw [← map_pow, ← drop_right_identity]
    simp only [map_add, map_mul, hR 0 1 (by decide), hR 1 0 (by decide),
      hR 2 0 (by decide), zero_mul, add_zero]
  apply one_ne_zero (α := ℂ)
  simpa only [map_sub, map_one, hr, sub_zero] using hl


theorem dimensionDrop23_no_character : IsEmpty (DimensionDrop23 →⋆ₐ[ℂ] ℂ) := by
  exact ⟨fun f => dimensionDrop23_no_ringhom.false f.toRingHom⟩

end KirchbergRordam


namespace KirchbergRordam.BalancedDropLimit
open BalancedDropMultiplicity
open scoped ComplexOrder CStarAlgebra

abbrev Stage (n : ℕ) : Type := PrimeDimensionDrop.Algebra (stage n) (stage n+1)
instance (n : ℕ) : NeZero (stage n) := ⟨by have := stage_two n; omega⟩
instance (n : ℕ) : Nontrivial (Stage n) := inferInstance
instance (n : ℕ) : TopologicalSpace.SeparableSpace (Stage n) := inferInstance

def chain : CStarInductiveLimit.Chain where
  obj := Stage
  step n := BalancedDropSystem.step (stage n) (stage_two n)
  norm_step n x := BalancedDropSystem.step_norm (stage n) (stage_two n) x

abbrev system := chain.system
instance (n : ℕ) : Nontrivial (system.obj n) := by
  change Nontrivial (Stage n)
  infer_instance
instance (n : ℕ) : TopologicalSpace.SeparableSpace (system.obj n) := by
  change TopologicalSpace.SeparableSpace (Stage n)
  infer_instance

abbrev Algebra := CStarInductiveLimit.Algebra system
instance : CStarAlgebra Algebra := inferInstance
instance : Nontrivial Algebra := inferInstance
instance : TopologicalSpace.SeparableSpace Algebra := inferInstance

def inclusion (n : ℕ) : Stage n →⋆ₐ[ℂ] Algebra := CStarInductiveLimit.of system n
lemma norm_inclusion (n : ℕ) (x : Stage n) : ‖inclusion n x‖ = ‖x‖ :=
  CStarInductiveLimit.norm_of system n x
lemma inclusion_isometry (n : ℕ) : Isometry (inclusion n) :=
  CStarInductiveLimit.of_isometry system n
lemma inclusion_step (n : ℕ) (x : Stage n) :
    inclusion (n+1) (BalancedDropSystem.step (stage n) (stage_two n) x) = inclusion n x := by
  have hx := CStarInductiveLimit.of_map system n (n+1) (Nat.le_succ n) x
  change CStarInductiveLimit.of system (n+1) (chain.map n (n+1) _ x) = _ at hx
  have hm : chain.map n (n+1) (Nat.le_succ n) = chain.step n := by
    rw [chain.map_succ n n le_rfl, chain.map_self]
    rfl
  rw [hm] at hx
  exact hx


def initial : DimensionDrop23 →⋆ₐ[ℂ] Algebra := inclusion 0

theorem no_character : IsEmpty (Algebra →⋆ₐ[ℂ] ℂ) :=
  ⟨fun χ => dimensionDrop23_no_character.false (χ.comp initial)⟩

lemma denseRange_inclusion : DenseRange (fun x : Σ n, Stage n => inclusion x.1 x.2) :=
  CStarInductiveLimit.denseRange_of system

end KirchbergRordam.BalancedDropLimit


namespace KirchbergRordam.CStarInductiveLimit
open Filter Topology
open scoped CStarAlgebra
variable {B : Type*} [CStarAlgebra B]

lemma quotient_eq_of_eventuallyEq (ω : Ultrafilter ℕ)
    {x y : NormUltrapower.BoundedSeq B}
    (h : ∀ᶠ m in (ω : Filter ℕ), x m=y m) :
    NormUltrapower.quotientMap ω x=NormUltrapower.quotientMap ω y := by
  apply (NormUltrapower.quotient_eq_iff ω x y).mpr
  apply tendsto_const_nhds.congr'
  filter_upwards [h] with m hm
  simp only [hm,sub_self,norm_zero]

def stageSeq (S : System) (φ : ∀ n, S.obj n →⋆ₐ[ℂ] B)
    (n : ℕ) (x : S.obj n) : NormUltrapower.BoundedSeq B :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun m => if h : n ≤ m then φ m (S.map n m h x) else 0)
    ‖x‖ (fun m => by
      split_ifs with h
      · exact (NonUnitalStarAlgHom.norm_apply_le (φ m) _).trans_eq (S.norm_map n m h x)
      · exact (norm_zero (E:=B)).le.trans (norm_nonneg x))

lemma stageSeq_apply (S : System) (φ : ∀ n, S.obj n →⋆ₐ[ℂ] B)
    (n m : ℕ) (h : n ≤ m) (x : S.obj n) :
    stageSeq S φ n x m=φ m (S.map n m h x) := dite_eq_left h

def stageHom (S : System) (φ : ∀ n, S.obj n →⋆ₐ[ℂ] B)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤Filter.atTop) (n : ℕ) :
    S.obj n →⋆ₐ[ℂ] NormUltrapower.Algebra B ω where
  toFun x := NormUltrapower.quotientMap ω (stageSeq S φ n x)
  map_add' x y := by
    rw [← map_add]
    apply quotient_eq_of_eventuallyEq
    filter_upwards [hω (eventually_ge_atTop n)] with m hm
    simp only [BoundedContinuousFunction.add_apply,stageSeq_apply S φ n m hm,map_add]
  map_mul' x y := by
    rw [← map_mul]
    apply quotient_eq_of_eventuallyEq
    filter_upwards [hω (eventually_ge_atTop n)] with m hm
    simp only [BoundedContinuousFunction.mul_apply,stageSeq_apply S φ n m hm,map_mul]
  map_zero' := by
    rw [← map_zero (NormUltrapower.quotientMap ω)]
    apply quotient_eq_of_eventuallyEq
    filter_upwards [hω (eventually_ge_atTop n)] with m hm
    simp only [stageSeq_apply S φ n m hm,map_zero]
    rfl
  map_one' := by
    rw [← map_one (NormUltrapower.quotientMap ω)]
    apply quotient_eq_of_eventuallyEq
    filter_upwards [hω (eventually_ge_atTop n)] with m hm
    simp only [stageSeq_apply S φ n m hm,map_one]
    rfl
  commutes' z := by
    rw [← (NormUltrapower.quotientMap ω).commutes]
    apply quotient_eq_of_eventuallyEq
    filter_upwards [hω (eventually_ge_atTop n)] with m hm
    rw [stageSeq_apply S φ n m hm]
    exact (congrArg (φ m) ((S.map n m hm).commutes z)).trans ((φ m).commutes z)
  map_star' x := by
    rw [← map_star]
    apply quotient_eq_of_eventuallyEq
    filter_upwards [hω (eventually_ge_atTop n)] with m hm
    simp only [BoundedContinuousFunction.star_apply,stageSeq_apply S φ n m hm,map_star]

lemma stageHom_map (S : System) (φ : ∀ n, S.obj n →⋆ₐ[ℂ] B)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤Filter.atTop)
    (i j : ℕ) (hij : i ≤ j) (x : S.obj i) :
    stageHom S φ ω hω j (S.map i j hij x)=stageHom S φ ω hω i x := by
  apply quotient_eq_of_eventuallyEq
  filter_upwards [hω (eventually_ge_atTop j)] with m hm
  rw [stageSeq_apply S φ j m hm,stageSeq_apply S φ i m (hij.trans hm),S.map_map]


def toUltrapower (S : System) (φ : ∀ n, S.obj n →⋆ₐ[ℂ] B)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤Filter.atTop) :
    Algebra S →⋆ₐ[ℂ] NormUltrapower.Algebra B ω :=
  lift S (stageHom S φ ω hω) (stageHom_map S φ ω hω)

lemma toUltrapower_of (S : System) (φ : ∀ n, S.obj n →⋆ₐ[ℂ] B)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤Filter.atTop) (n : ℕ) (x : S.obj n) :
    toUltrapower S φ ω hω (of S n x)=stageHom S φ ω hω n x := lift_of _ _ _ _ _


theorem exists_toCentral (S : System) [∀ n, TopologicalSpace.SeparableSpace (S.obj n)]
    {A : Type*} [CStarAlgebra A] [TopologicalSpace.SeparableSpace A]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤cofinite)
    (φ : ∀ n, S.obj n →⋆ₐ[ℂ] NormUltrapower.CentralAlgebra A ω) :
    Nonempty (Algebra S →⋆ₐ[ℂ] NormUltrapower.CentralAlgebra A ω) := by
  have hfree : (ω : Filter ℕ) ≤ atTop := by simpa only [Nat.cofinite_eq_atTop] using hω
  obtain ⟨θ,_⟩ := NormUltrapower.iterated_central_collapse ω hω (toUltrapower S φ ω hfree)
  exact ⟨θ⟩
end KirchbergRordam.CStarInductiveLimit


namespace KirchbergRordam.BalancedDropMultiplicity
lemma stage_power (n : ℕ) : stage n = 2^(3^n) := by
  induction n with
  | zero => simp [stage]
  | succ n ih =>
    rw [stage_succ, next, ih, pow_succ, pow_mul]
    ring
lemma stage_power_successor (n : ℕ) : stage n = 2^((3^n-1)+1) := by
  have hp : 1 ≤ 3^n := Nat.one_le_pow n 3 (by decide)
  rw [Nat.sub_add_cancel hp]
  exact stage_power n
end KirchbergRordam.BalancedDropMultiplicity

namespace KirchbergRordam.BalancedDropLimit
open TopologicalSpace


theorem stage_to_central (A : Type*) [CStarAlgebra A] [Nontrivial A]
    [SeparableSpace A] (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (hF : IsEmpty (NormUltrapower.CentralAlgebra A ω →⋆ₐ[ℂ] ℂ)) (n : ℕ) :
    Nonempty (Stage n →⋆ₐ[ℂ] NormUltrapower.CentralAlgebra A ω) := by
  change Nonempty (PrimeDimensionDrop.Algebra
    (BalancedDropMultiplicity.stage n) (BalancedDropMultiplicity.stage n+1) →⋆ₐ[ℂ] _)
  rw [BalancedDropMultiplicity.stage_power_successor n]
  exact central_prime_power_drop A ω hω hF (3^n-1)


theorem to_central (A : Type*) [CStarAlgebra A] [Nontrivial A]
    [SeparableSpace A] (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (hF : IsEmpty (NormUltrapower.CentralAlgebra A ω →⋆ₐ[ℂ] ℂ)) :
    Nonempty (Algebra →⋆ₐ[ℂ] NormUltrapower.CentralAlgebra A ω) := by
  let φ := fun n => (stage_to_central A ω hω hF n).some
  exact CStarInductiveLimit.exists_toCentral system ω hω φ
end KirchbergRordam.BalancedDropLimit


end

end OAI
