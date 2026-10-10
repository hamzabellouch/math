import Mathlib
import OAI.Analysis.LaughlinGap.Occupation
import OAI.Analysis.LaughlinGap.SpectralBound

namespace OAI

/-! Pair Energy. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators Topology
open Filter

noncomputable def localPair (n Q p : ℕ) : Module.End ℂ (Hilbert n) :=
  pairAnnihilator (fun x y => (sphericalExteriorPairCoefficient Q p x.val y.val : ℂ))

noncomputable def localPairStar (n p : ℕ) : Module.End ℂ (Hilbert n) :=
  pairAnnihilator (fun x y => (limitingExteriorPairCoefficient p x.val y.val : ℂ))

noncomputable def localDelta (n Q : ℕ) : Hilbert n →L[ℂ] Hilbert n :=
  diagonalCLM (fun x => orbitalDiagonalFactor Q x.val)

noncomputable def localDeltaInv (n Q : ℕ) : Hilbert n →L[ℂ] Hilbert n :=
  diagonalCLM (fun x => (orbitalDiagonalFactor Q x.val)⁻¹)

lemma localPair_eq_factored {n Q p : ℕ} (hQ : 0 < Q) (hp : p ≤ 2*Q-2) :
    localPair n Q p = pairAnnihilator (fun x y : Fin n =>
      (pairRescalingFactor Q p : ℂ) *
        ((orbitalDiagonalFactor Q x.val * orbitalDiagonalFactor Q y.val : ℝ) *
          (limitingExteriorPairCoefficient p x.val y.val : ℂ))) := by
  unfold localPair
  congr 1
  funext x y
  rw [sphericalExteriorPairCoefficient_factor hQ hp]
  push_cast
  ring

theorem localPair_conjugation {n Q p : ℕ} (hQ : 0 < Q) (hn : n ≤ Q+1)
    (hp : p ≤ 2*Q-2) :
    localPair n Q p = (pairRescalingFactor Q p : ℂ) •
      ((localDeltaInv n Q).toLinearMap * localPairStar n p * (localDelta n Q).toLinearMap) := by
  rw [localPair_eq_factored hQ hp]
  apply pairAnnihilator_conjugation
  intro j
  exact ne_of_gt (orbitalDiagonalFactor_pos hQ (by have := j.is_lt; omega))

theorem localFour_conjugation {n Q p : ℕ} (hQ : 0 < Q) (hn : n ≤ Q+1)
    (hp : p ≤ 2*Q-2) (j k : Fin n) :
    annihilation k * annihilation j * localPair n Q p =
      ((pairRescalingFactor Q p / (orbitalDiagonalFactor Q j.val *
        orbitalDiagonalFactor Q k.val) : ℝ) : ℂ) •
      ((localDeltaInv n Q).toLinearMap *
        (annihilation k * annihilation j * localPairStar n p) * (localDelta n Q).toLinearMap) := by
  rw [localPair_eq_factored hQ hp]
  apply fourAnnihilator_conjugation
  intro j
  exact ne_of_gt (orbitalDiagonalFactor_pos hQ (by have := j.is_lt; omega))

theorem localDelta_norm_le (n Q : ℕ) (x : Hilbert n) : ‖localDelta n Q x‖ ≤ ‖x‖ :=
  diagonal_norm_le (fun j => orbitalDiagonalFactor_nonneg Q j.val)
    (fun j => orbitalDiagonalFactor_le_one Q j.val) x

theorem localDelta_tendsto (n : ℕ) :
    Tendsto (localDelta n) atTop (𝓝 1) := by
  change Tendsto (fun Q => diagonalCLM (fun j : Fin n => orbitalDiagonalFactor Q j.val)) atTop (𝓝 1)
  simpa only [diagonalCLM_one] using
    diagonalCLM_tendsto (fun j : Fin n => orbitalDiagonalFactor_tendsto j.val)

theorem localDeltaInv_tendsto (n : ℕ) :
    Tendsto (localDeltaInv n) atTop (𝓝 1) :=
  diagonalCLM_inv_tendsto_one (fun j => orbitalDiagonalFactor_tendsto j.val)

theorem localDelta_mul_inv {n Q : ℕ} (hQ : 0 < Q) (hn : n ≤ Q+1) :
    localDelta n Q * localDeltaInv n Q = 1 := by
  have h := diagonal_comp_inv (fun j : Fin n => orbitalDiagonalFactor Q j.val)
    (fun j => ne_of_gt (orbitalDiagonalFactor_pos hQ (by have := j.is_lt; omega)))
  ext x A
  exact congrArg (fun z : Hilbert n => z A) (LinearMap.congr_fun h x)

noncomputable def localPairEnergyStar (n L : ℕ) (x : Hilbert n) : ℝ :=
  ∑ p : Fin L, ‖localPairStar n p.val x‖ ^ 2

noncomputable def localPairEnergy (n L Q : ℕ) (x : Hilbert n) : ℝ :=
  ∑ p : Fin L, ‖localPair n Q p.val x‖ ^ 2

theorem localPairEnergy_transfer {n L Q : ℕ} (hQ : 0 < Q) (hL : L ≤ 2*Q-1)
    (x : Hilbert n) :
    localPairEnergyStar n L (localDelta n Q x) ≤ localPairEnergy n L Q x := by
  apply Finset.sum_le_sum
  intro p _
  have hp : p.val ≤ 2*Q-2 := by have := p.is_lt; omega
  rw [localPair_eq_factored hQ hp]
  exact pairAnnihilator_energy_transfer _
    (fun j => orbitalDiagonalFactor_nonneg Q j.val)
    (fun j => orbitalDiagonalFactor_le_one Q j.val) _ (one_le_pairRescalingFactor hp) x

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

def joinEquiv (n m : ℕ) : (Finset (Fin n) × Finset (Fin m)) ≃ Finset (Fin (n+m)) :=
  Finset.sumEquiv.toEquiv.symm.trans finSumFinEquiv.finsetCongr

def join {n m : ℕ} (A : Finset (Fin n)) (R : Finset (Fin m)) : Finset (Fin (n+m)) :=
  joinEquiv n m (A,R)

lemma join_eq_map {n m : ℕ} (A : Finset (Fin n)) (R : Finset (Fin m)) :
    join A R = Finset.map finSumFinEquiv.toEmbedding (A.disjSum R) := rfl

@[simp] lemma mem_join_left {n m : ℕ} (j : Fin n) (A : Finset (Fin n)) (R : Finset (Fin m)) :
    Fin.castAdd m j ∈ join A R ↔ j ∈ A := by
  rw [join_eq_map, ← finSumFinEquiv_apply_left]
  simp

@[simp] lemma mem_join_right {n m : ℕ} (j : Fin m) (A : Finset (Fin n)) (R : Finset (Fin m)) :
    Fin.natAdd n j ∈ join A R ↔ j ∈ R := by
  rw [join_eq_map, ← finSumFinEquiv_apply_right]
  simp

@[simp] lemma join_card {n m : ℕ} (A : Finset (Fin n)) (R : Finset (Fin m)) :
    (join A R).card = A.card + R.card := by simp [join_eq_map]

lemma prefix_ne_suffix {n m : ℕ} (i : Fin n) (j : Fin m) :
    Fin.castAdd m i ≠ Fin.natAdd n j := by
  intro h
  have hv := congrArg Fin.val h
  have := i.is_lt
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

lemma join_erase_left {n m : ℕ} (j : Fin n) (A : Finset (Fin n)) (R : Finset (Fin m)) :
    join (A.erase j) R = (join A R).erase (Fin.castAdd m j) := by
  ext x
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
  cases x with
  | inl i => simp
  | inr i => simp [Ne.symm (prefix_ne_suffix j i)]

lemma join_insert_left {n m : ℕ} (j : Fin n) (A : Finset (Fin n)) (R : Finset (Fin m)) :
    join (insert j A) R = insert (Fin.castAdd m j) (join A R) := by
  ext x
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
  cases x with
  | inl i => simp
  | inr i => simp [Ne.symm (prefix_ne_suffix j i)]

lemma join_flip_left {n m : ℕ} (j : Fin n) (A : Finset (Fin n)) (R : Finset (Fin m)) :
    join (flip j A) R = flip (Fin.castAdd m j) (join A R) := by
  by_cases hi : j ∈ A
  · simp [hi, join_erase_left]
  · simp [hi, join_insert_left]

lemma join_filter_prefix {n m : ℕ} (j : Fin n) (A : Finset (Fin n)) (R : Finset (Fin m)) :
    (join A R).filter (fun k => k < Fin.castAdd m j) =
      join (A.filter (fun k => k < j)) (∅ : Finset (Fin m)) := by
  ext x
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
  cases x with
  | inl i =>
    simp only [finSumFinEquiv_apply_left, Finset.mem_filter, mem_join_left]
    rfl
  | inr i =>
    have h : ¬ Fin.natAdd n i < Fin.castAdd m j := by
      simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd]
      have := j.is_lt
      omega
    simp [h]

theorem sign_join_left {n m : ℕ} (j : Fin n) (A : Finset (Fin n)) (R : Finset (Fin m)) :
    sign (Fin.castAdd m j) (join A R) = sign j A := by
  simp [sign, join_filter_prefix]

noncomputable def slice {n m : ℕ} (R : Finset (Fin m)) : Hilbert (n+m) →ₗ[ℂ] Hilbert n where
  toFun x := WithLp.toLp 2 (fun A => x (join A R))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma slice_apply {n m : ℕ} (R : Finset (Fin m)) (x : Hilbert (n+m))
    (A : Finset (Fin n)) : slice R x A = x (join A R) := rfl

theorem norm_sq_eq_sum_slice {n m : ℕ} (x : Hilbert (n+m)) :
    ‖x‖ ^ 2 = ∑ R : Finset (Fin m), ‖slice R x‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, slice_apply]
  rw [← Equiv.sum_comp (joinEquiv n m) (fun A => ‖x A‖ ^ 2), Fintype.sum_prod_type,
    Finset.sum_comm]
  rfl

lemma inner_eq_sum_slice {n m : ℕ} (x y : Hilbert (n+m)) :
    inner ℂ x y = ∑ R : Finset (Fin m), inner ℂ (slice R x) (slice R y) := by
  simp only [PiLp.inner_apply, slice_apply]
  rw [← Equiv.sum_comp (joinEquiv n m) (fun A => inner ℂ (x A) (y A)), Fintype.sum_prod_type,
    Finset.sum_comm]
  rfl

theorem slice_transition {n m : ℕ} (R : Finset (Fin m)) (j : Fin n) (ε : Bool)
    (x : Hilbert (n+m)) :
    slice R (transition (Fin.castAdd m j) ε x) = transition j ε (slice R x) := by
  ext A
  simp [transition_apply, slice_apply, sign_join_left, ← join_flip_left]

noncomputable def extendLocal {n m : ℕ} (T : Module.End ℂ (Hilbert n)) :
    Module.End ℂ (Hilbert (n+m)) where
  toFun x := WithLp.toLp 2 (fun S =>
    T (slice ((joinEquiv n m).symm S).2 x) ((joinEquiv n m).symm S).1)
  map_add' x y := by ext S; simp
  map_smul' c x := by ext S; simp

@[simp] lemma slice_extendLocal {n m : ℕ} (R : Finset (Fin m)) (T : Module.End ℂ (Hilbert n))
    (x : Hilbert (n+m)) : slice R (extendLocal T x) = T (slice R x) := by
  ext A
  simp [slice_apply, extendLocal, join]

lemma eq_of_slice_eq {n m : ℕ} {x y : Hilbert (n+m)}
    (h : ∀ R : Finset (Fin m), slice R x = slice R y) : x = y := by
  ext S
  obtain ⟨⟨A,R⟩, rfl⟩ := (joinEquiv n m).surjective S
  exact congrArg (fun z : Hilbert n => z A) (h R)

@[simp] theorem extendLocal_transition {n m : ℕ} (j : Fin n) (ε : Bool) :
    extendLocal (m := m) (transition j ε) = transition (Fin.castAdd m j) ε := by
  apply LinearMap.ext
  intro x
  apply eq_of_slice_eq
  intro R
  rw [slice_extendLocal, slice_transition]

@[simp] theorem extendLocal_one {n m : ℕ} :
    extendLocal (m := m) (1 : Module.End ℂ (Hilbert n)) = 1 := by
  apply LinearMap.ext
  intro x
  apply eq_of_slice_eq
  intro R
  simp

@[simp] theorem extendLocal_add {n m : ℕ} (T S : Module.End ℂ (Hilbert n)) :
    extendLocal (m := m) (T + S) = extendLocal T + extendLocal S := by
  apply LinearMap.ext
  intro x
  apply eq_of_slice_eq
  intro R
  simp

@[simp] theorem extendLocal_mul {n m : ℕ} (T S : Module.End ℂ (Hilbert n)) :
    extendLocal (m := m) (T * S) = extendLocal T * extendLocal S := by
  apply LinearMap.ext
  intro x
  apply eq_of_slice_eq
  intro R
  simp only [Module.End.mul_apply, slice_extendLocal]

theorem extendLocal_quadraticForm_le {n m : ℕ} (T S : Module.End ℂ (Hilbert n))
    (h : ∀ x, (inner ℂ x (T x)).re ≤ (inner ℂ x (S x)).re) (x : Hilbert (n+m)) :
    (inner ℂ x (extendLocal T x)).re ≤ (inner ℂ x (extendLocal S x)).re := by
  rw [inner_eq_sum_slice, inner_eq_sum_slice]
  simp only [Complex.re_sum, slice_extendLocal]
  exact Finset.sum_le_sum (fun R _ => h (slice R x))

theorem extendLocal_energy_le {n m : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → Module.End ℂ (Hilbert n)) (B : κ → Module.End ℂ (Hilbert n)) (c : ℝ)
    (h : ∀ x, (∑ a, ‖A a x‖ ^ 2) ≤ c * (∑ b, ‖B b x‖ ^ 2)) (x : Hilbert (n+m)) :
    (∑ a, ‖extendLocal (A a) x‖ ^ 2) ≤ c * (∑ b, ‖extendLocal (B b) x‖ ^ 2) := by
  simp_rw [norm_sq_eq_sum_slice, slice_extendLocal]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun (b : κ) (R : Finset (Fin m)) => ‖B b (slice R x)‖ ^ 2), Finset.mul_sum]
  exact Finset.sum_le_sum (fun R _ => h (slice R x))

@[simp] theorem extendLocal_zero {n m : ℕ} :
    extendLocal (m := m) (0 : Module.End ℂ (Hilbert n)) = 0 := by
  apply LinearMap.ext
  intro x
  apply eq_of_slice_eq
  intro R
  simp

@[simp] theorem extendLocal_smul {n m : ℕ} (c : ℂ) (T : Module.End ℂ (Hilbert n)) :
    extendLocal (m := m) (c • T) = c • extendLocal T := by
  apply LinearMap.ext
  intro x
  apply eq_of_slice_eq
  intro R
  simp

@[simp] theorem extendLocal_adjoint {n m : ℕ} (T : Module.End ℂ (Hilbert n)) :
    (extendLocal (m := m) T).adjoint = extendLocal T.adjoint := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  rw [inner_eq_sum_slice, inner_eq_sum_slice]
  simp only [slice_extendLocal, LinearMap.adjoint_inner_left]

noncomputable def extendLocalHom (n m : ℕ) :
    Module.End ℂ (Hilbert n) →⋆ₐ[ℂ] Module.End ℂ (Hilbert (n+m)) where
  toFun := extendLocal
  map_one' := extendLocal_one
  map_mul' := extendLocal_mul
  map_zero' := extendLocal_zero
  map_add' := extendLocal_add
  commutes' c := by
    change extendLocal (m := m) (c • (1 : Module.End ℂ (Hilbert n))) = c • 1
    rw [extendLocal_smul, extendLocal_one]
  map_star' T := (extendLocal_adjoint T).symm

theorem extendLocal_positive {n m : ℕ} {T : Module.End ℂ (Hilbert n)}
    (hT : T.IsPositive) : (extendLocal (m := m) T).IsPositive := by
  refine ⟨?_, fun x => ?_⟩
  · intro x y
    rw [inner_eq_sum_slice, inner_eq_sum_slice]
    simp only [slice_extendLocal]
    exact Finset.sum_congr rfl (fun R _ => hT.isSymmetric _ _)
  · rw [inner_eq_sum_slice]
    simp only [slice_extendLocal, map_sum]
    exact Finset.sum_nonneg (fun R _ => hT.re_inner_nonneg_left (slice R x))

end LaughlinGap.Occupation

namespace LaughlinGap
open scoped BigOperators InnerProduct ComplexOrder

section PositiveLifting
variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

noncomputable def matrixLift (B : ι → Module.End ℂ E) :
    Matrix ι ι ℂ →ₗ[ℂ] Module.End ℂ E where
  toFun M := ∑ i, ∑ j, M i j • ((B i).adjoint * B j)
  map_add' M N := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c M := by simp [Finset.smul_sum, smul_smul]

noncomputable def contractCombination (B : ι → Module.End ℂ E) (v : ι → ℂ) :
    Module.End ℂ E := ∑ i, star (v i) • B i

theorem matrixLift_rankOne (B : ι → Module.End ℂ E) (v w : ι → ℂ) :
    matrixLift B (Matrix.vecMulVec v (star w)) =
      (contractCombination B v).adjoint * contractCombination B w := by
  simp only [matrixLift, LinearMap.coe_mk, AddHom.coe_mk, Matrix.vecMulVec_apply,
    Pi.star_apply, contractCombination, map_sum, map_smulₛₗ,
    Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    Complex.star_def, Complex.conj_conj, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem matrixLift_positive (B : ι → Module.End ℂ E) {M : Matrix ι ι ℂ}
    (hM : M.PosSemidef) : (matrixLift B M).IsPositive := by
  classical
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hM
  rw [map_sum]
  apply LinearMap.isPositive_sum
  intro i _
  rw [matrixLift_rankOne]
  exact LinearMap.isPositive_adjoint_comp_self _

theorem matrixLift_columns {κ : Type*} [Fintype κ]
    (B : ι → Module.End ℂ E) (W : Matrix ι κ ℂ) (C : Matrix κ κ ℂ) :
    matrixLift B (W * C * W.conjTranspose) =
      matrixLift (fun r => contractCombination B (fun i => W i r)) C := by
  classical
  have hm : W * C * W.conjTranspose =
      ∑ r, ∑ s, C r s • Matrix.vecMulVec (fun i => W i r) (star (fun i => W i s)) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hm]
  simp only [map_sum, map_smul, matrixLift_rankOne]
  rfl

theorem matrixLift_gram_positive {κ : Type*} [Fintype κ] [DecidableEq κ]
    [DecidableEq ι] (B : ι → Module.End ℂ E) (W : Matrix ι κ ℂ)
    (C : Matrix κ κ ℂ) (hC : C.IsHermitian)
    (hG : ((W.conjTranspose * W) * C * (W.conjTranspose * W)).PosSemidef) :
    (matrixLift (fun r => contractCombination B (fun i => W i r)) C).IsPositive := by
  rw [← matrixLift_columns]
  apply matrixLift_positive
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  rw [← Matrix.isPositive_toEuclideanLin_iff] at hG
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint] at hG ⊢
  exact (gram_compression_positive_iff W.toEuclideanLin C.toEuclideanLin
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hC)).mp hG

end PositiveLifting

namespace Occupation

abbrev BasisLabel (n k : ℕ) := {A : Finset (Fin n) // A.card = k}

abbrev ExteriorCoordinates (n k : ℕ) := EuclideanSpace ℂ (BasisLabel n k)

noncomputable def basisContraction {n k : ℕ} (A : BasisLabel n k) :
    Module.End ℂ (Hilbert n) := word (A.val.sort (· ≤ ·))

noncomputable def exteriorContraction {n k : ℕ} (v : ExteriorCoordinates n k) :
    Module.End ℂ (Hilbert n) := contractCombination basisContraction v

noncomputable def exteriorLift {n k : ℕ} :
    Matrix (BasisLabel n k) (BasisLabel n k) ℂ →ₗ[ℂ] Module.End ℂ (Hilbert n) :=
  matrixLift basisContraction

theorem exteriorLift_rankOne {n k : ℕ} (v w : ExteriorCoordinates n k) :
    exteriorLift (Matrix.vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp w))) =
      (exteriorContraction v).adjoint * exteriorContraction w :=
  matrixLift_rankOne basisContraction v w

theorem exteriorLift_positive {n k : ℕ}
    {M : Matrix (BasisLabel n k) (BasisLabel n k) ℂ} (hM : M.PosSemidef) :
    (exteriorLift M).IsPositive := matrixLift_positive basisContraction hM

end Occupation
end LaughlinGap

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

def Homogeneous {n : ℕ} (k : ℕ) (x : Hilbert n) : Prop :=
  ∀ A, A.card ≠ k → x A = 0

lemma annihilation_homogeneous {n k : ℕ} {x : Hilbert n} (hx : Homogeneous (k+1) x)
    (j : Fin n) : Homogeneous k (annihilation j x) := by
  intro A hA
  by_cases hj : j ∈ A
  · simp [transition_apply, hj]
  · rw [transition_apply]
    simp only [hj, decide_false, ite_true, flip_of_not_mem hj]
    rw [hx (insert j A) (by rw [Finset.card_insert_of_notMem hj]; omega), mul_zero]

lemma annihilation_eq_zero_of_degree_zero {n : ℕ} {x : Hilbert n}
    (hx : Homogeneous 0 x) (j : Fin n) : annihilation j x = 0 := by
  ext A
  by_cases hj : j ∈ A
  · simp [transition_apply, hj]
  · simp only [transition_apply, hj, decide_false, ite_true,
      flip_of_not_mem hj]
    rw [hx (insert j A) (by simp), mul_zero]
    rfl

lemma word_homogeneous {n k : ℕ} (js : List (Fin n)) {x : Hilbert n}
    (hx : Homogeneous (k + js.length) x) : Homogeneous k (word js x) := by
  induction js generalizing x with
  | nil => simpa only [word, List.length_nil, Nat.add_zero, LinearMap.id_apply] using hx
  | cons j js ih =>
    exact ih (annihilation_homogeneous (by simpa only [List.length_cons, Nat.add_assoc] using hx) j)

lemma word_eq_zero_of_degree_lt {n k : ℕ} (js : List (Fin n)) {x : Hilbert n}
    (hx : Homogeneous k x) (hk : k < js.length) : word js x = 0 := by
  induction js generalizing k x with
  | nil => simp at hk
  | cons j js ih =>
    cases k with
    | zero => simp only [word, LinearMap.comp_apply, annihilation_eq_zero_of_degree_zero hx, map_zero]
    | succ k =>
      exact ih (annihilation_homogeneous hx j) (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hk)

lemma word_apply_empty_sorted {n : ℕ} (js : List (Fin n))
    (hs : js.Pairwise (· < ·)) (x : Hilbert n) : word js x ∅ = x js.toFinset := by
  induction js generalizing x with
  | nil => rfl
  | cons j js ih =>
    obtain ⟨hj, hs⟩ := List.pairwise_cons.mp hs
    change word js (annihilation j x) ∅ = _
    rw [ih hs]
    have hj' : j ∉ js.toFinset := by
      intro h
      exact lt_irrefl j (hj j (List.mem_toFinset.mp h))
    have he : (js.toFinset.filter (fun k => k < j)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i hi hij
      exact not_lt_of_gt (hj i (List.mem_toFinset.mp hi)) hij
    simp [transition_apply, hj', sign, he]

@[simp] lemma basisContraction_apply_empty {n k : ℕ} (A : BasisLabel n k) (x : Hilbert n) :
    basisContraction A x ∅ = x A.val := by
  simpa only [basisContraction, Finset.sort_toFinset] using
    word_apply_empty_sorted (A.val.sort (· ≤ ·)) A.val.sortedLT_sort.pairwise x

noncomputable def vacuum (n : ℕ) : Hilbert n := EuclideanSpace.single ∅ 1

@[simp] lemma vacuum_apply (n : ℕ) (A : Finset (Fin n)) :
    vacuum n A = if A = ∅ then 1 else 0 := by
  simp only [vacuum, PiLp.single_apply]

@[simp] lemma vacuum_norm (n : ℕ) : ‖vacuum n‖ = 1 := by
  simp [vacuum]

lemma degree_zero_eq_vacuum {n : ℕ} {x : Hilbert n} (hx : Homogeneous 0 x) :
    x = x ∅ • vacuum n := by
  ext A
  by_cases h : A = ∅
  · simp [h]
  · have hc : A.card ≠ 0 := by simpa using h
    simp [vacuum_apply, h, hx A hc]

lemma basisContraction_degree {n k : ℕ} {x : Hilbert n} (hx : Homogeneous k x)
    (A : BasisLabel n k) : basisContraction A x = x A.val • vacuum n := by
  have hd : Homogeneous 0 (basisContraction A x) :=
    word_homogeneous (A.val.sort (· ≤ ·)) (by simpa only [Finset.length_sort, A.property, Nat.zero_add] using hx)
  rw [degree_zero_eq_vacuum hd, basisContraction_apply_empty]

lemma basisContraction_eq_zero_of_degree_lt {n j k : ℕ} {x : Hilbert n}
    (hx : Homogeneous j x) (hjk : j < k) (A : BasisLabel n k) : basisContraction A x = 0 :=
  word_eq_zero_of_degree_lt (A.val.sort (· ≤ ·)) hx (by simpa only [Finset.length_sort, A.property] using hjk)

noncomputable def sectorInclusion (n k : ℕ) : ExteriorCoordinates n k →ₗ[ℂ] Hilbert n where
  toFun x := WithLp.toLp 2 (fun A => if h : A.card = k then x ⟨A,h⟩ else 0)
  map_add' x y := by
    ext A
    by_cases h : A.card = k <;> simp [h]
  map_smul' c x := by
    ext A
    by_cases h : A.card = k <;> simp [h]

@[simp] lemma sectorInclusion_apply {n k : ℕ} (x : ExteriorCoordinates n k)
    (A : Finset (Fin n)) :
    sectorInclusion n k x A = if h : A.card = k then x ⟨A,h⟩ else 0 := rfl

@[simp] lemma sectorInclusion_apply_label {n k : ℕ} (x : ExteriorCoordinates n k)
    (A : BasisLabel n k) : sectorInclusion n k x A.val = x A := by
  simp only [sectorInclusion_apply, A.property, ↓reduceDIte]

lemma sectorInclusion_homogeneous {n k : ℕ} (x : ExteriorCoordinates n k) :
    Homogeneous k (sectorInclusion n k x) := fun A h => by simp [h]

@[simp] lemma basisContraction_sectorInclusion {n k : ℕ} (x : ExteriorCoordinates n k)
    (A : BasisLabel n k) : basisContraction A (sectorInclusion n k x) = x A • vacuum n := by
  rw [basisContraction_degree (sectorInclusion_homogeneous x), sectorInclusion_apply_label]

theorem exteriorContraction_sectorInclusion {n k : ℕ} (v x : ExteriorCoordinates n k) :
    exteriorContraction v (sectorInclusion n k x) = inner ℂ v x • vacuum n := by
  simp only [exteriorContraction, contractCombination, LinearMap.sum_apply,
    LinearMap.smul_apply, basisContraction_sectorInclusion, smul_smul,
    PiLp.inner_apply, RCLike.inner_apply, ← Finset.sum_smul]
  simp only [Complex.star_def, mul_comm]

theorem exteriorContraction_eq_zero_of_degree_lt {n j k : ℕ} {x : Hilbert n}
    (hx : Homogeneous j x) (hjk : j < k) (v : ExteriorCoordinates n k) :
    exteriorContraction v x = 0 := by
  simp only [exteriorContraction, contractCombination, LinearMap.sum_apply,
    LinearMap.smul_apply, basisContraction_eq_zero_of_degree_lt hx hjk,
    smul_zero, Finset.sum_const_zero]

theorem exteriorLift_eq_zero_of_degree_lt {n j k : ℕ} {x : Hilbert n}
    (hx : Homogeneous j x) (hjk : j < k) (M : Matrix (BasisLabel n k) (BasisLabel n k) ℂ) :
    exteriorLift M x = 0 := by
  simp only [exteriorLift, matrixLift, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply,
    LinearMap.smul_apply, Module.End.mul_apply, basisContraction_eq_zero_of_degree_lt hx hjk,
    map_zero, smul_zero, Finset.sum_const_zero]

theorem exteriorLift_inner_sector {n k : ℕ}
    (M : Matrix (BasisLabel n k) (BasisLabel n k) ℂ) (x y : ExteriorCoordinates n k) :
    inner ℂ (sectorInclusion n k x) (exteriorLift M (sectorInclusion n k y)) =
      inner ℂ x (M.toEuclideanLin y) := by
  classical
  simp only [exteriorLift, matrixLift, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply,
    LinearMap.smul_apply, Module.End.mul_apply, inner_sum, inner_smul_right,
    LinearMap.adjoint_inner_right, basisContraction_sectorInclusion,
    inner_smul_left]
  simp only [inner_self_eq_norm_sq_to_K, vacuum_norm, RCLike.ofReal_one,
    one_pow, mul_one]
  simp only [PiLp.inner_apply, RCLike.inner_apply, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro B _
  ring

end LaughlinGap.Occupation

end

end OAI
