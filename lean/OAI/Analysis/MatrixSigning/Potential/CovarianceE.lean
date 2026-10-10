import Mathlib

namespace OAI

open Matrix

namespace CurrentKS.Covariance
noncomputable section
open scoped BigOperators
open Matrix

local instance : InnerProductSpace ℝ ℝ := RCLike.innerProductSpace

abbrev E (m : ℕ) := EuclideanSpace ℝ (Fin m)
abbrev Mat (m : ℕ) := Matrix (Fin m) (Fin m) ℝ

variable {m : ℕ}

local instance : LocallyConvexSpace ℝ (Mat m) :=
  inferInstanceAs (LocallyConvexSpace ℝ (Fin m → Fin m → ℝ))

def projectionMatrix (G : Submodule ℝ (E m)) : Mat m :=
  LinearMap.toMatrix (EuclideanSpace.basisFun _ ℝ).toBasis
    (EuclideanSpace.basisFun _ ℝ).toBasis G.starProjection.toLinearMap

theorem projectionMatrix_toEuclideanLin (G : Submodule ℝ (E m)) :
    Matrix.toEuclideanLin (projectionMatrix G) = G.starProjection.toLinearMap := by
  simp [projectionMatrix, Matrix.toEuclideanLin_eq_toLin_orthonormal]

theorem projectionMatrix_posSemidef (G : Submodule ℝ (E m)) :
    (projectionMatrix G).PosSemidef := by
  rw [← Matrix.isPositive_toEuclideanLin_iff, projectionMatrix_toEuclideanLin]
  exact ⟨G.starProjection_isSymmetric, G.re_inner_starProjection_nonneg⟩

theorem projectionMatrix_range (G : Submodule ℝ (E m)) :
    LinearMap.range (Matrix.toEuclideanLin (projectionMatrix G)) = G := by
  rw [projectionMatrix_toEuclideanLin]
  exact G.range_starProjection

theorem projectionMatrix_trace (G : Submodule ℝ (E m)) :
    (projectionMatrix G).trace = Module.finrank ℝ G := by
  rw [projectionMatrix, ← LinearMap.trace_eq_matrix_trace]
  have hp : LinearMap.IsProj G G.starProjection.toLinearMap :=
    ⟨G.starProjection_apply_mem, fun x hx => G.starProjection_eq_self_iff.mpr hx⟩
  exact hp.trace

theorem projectionMatrix_add_orthogonal (G : Submodule ℝ (E m)) :
    projectionMatrix G + projectionMatrix Gᗮ = 1 := by
  apply Matrix.toEuclideanLin.injective
  rw [map_add, projectionMatrix_toEuclideanLin, projectionMatrix_toEuclideanLin]
  rw [Matrix.toLpLin_one]
  ext w i
  have h := G.starProjection_add_starProjection_orthogonal w
  exact congrArg (fun v : E m => v i) h

theorem projectionMatrix_diag_le_one (G : Submodule ℝ (E m)) (i : Fin m) :
    projectionMatrix G i i ≤ 1 := by
  have hp := (projectionMatrix_posSemidef Gᗮ).diag_nonneg (i := i)
  have he := congrFun (congrFun (projectionMatrix_add_orthogonal G) i) i
  simp only [Matrix.add_apply, Matrix.one_apply_eq] at he
  linarith

theorem abs_entry_le_trace {A : Mat m} (hA : A.PosSemidef) (i j : Fin m) :
    |A i j| ≤ A.trace := by
  have hi : A i i ≤ A.trace :=
    Finset.single_le_sum (fun k _ => hA.diag_nonneg (i := k)) (Finset.mem_univ i)
  have hj : A j j ≤ A.trace :=
    Finset.single_le_sum (fun k _ => hA.diag_nonneg (i := k)) (Finset.mem_univ j)
  have hsym : A j i = A i j := by simpa using hA.isHermitian.apply i j
  have hp := hA.2 (Finsupp.single i 1 + Finsupp.single j 1)
  have hm := hA.2 (Finsupp.single i 1 + Finsupp.single j (-1))
  simp [Finsupp.sum_add_index, mul_add, add_mul, hsym, -Finsupp.single_neg] at hp hm
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem isClosed_psd : IsClosed {A : Mat m | A.PosSemidef} := by
  simp only [Matrix.posSemidef_iff_dotProduct_mulVec, Set.ofPred_and, Set.ofPred_forall]
  refine IsClosed.inter ?_ (isClosed_iInter fun x => ?_)
  · exact isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  · exact isClosed_le continuous_const
      (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const))

def psdTraceBound (B : ℝ) : Set (Mat m) :=
  {A | A.PosSemidef ∧ A.trace ≤ B}

theorem isClosed_psdTraceBound (B : ℝ) : IsClosed (psdTraceBound (m := m) B) :=
  isClosed_psd.inter (isClosed_le continuous_id.matrix_trace continuous_const)

theorem isCompact_psdTraceBound (B : ℝ) : IsCompact (psdTraceBound (m := m) B) := by
  refine (isCompact_Icc : IsCompact
    (Set.Icc (fun (_ : Fin m) (_ : Fin m) => -B) (fun _ _ => B))).of_isClosed_subset
      (isClosed_psdTraceBound B) ?_
  intro A hA
  constructor
  · intro i j
    exact (abs_le.mp ((abs_entry_le_trace hA.1 i j).trans hA.2)).1
  · intro i j
    exact (abs_le.mp ((abs_entry_le_trace hA.1 i j).trans hA.2)).2

theorem convex_psdTraceBound (B : ℝ) : Convex ℝ (psdTraceBound (m := m) B) := by
  intro A hA C hC a b ha hb hab
  refine ⟨(hA.1.smul ha).add (hC.1.smul hb), ?_⟩
  simp only [Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  calc
    a * A.trace + b * C.trace ≤ a * B + b * B :=
      add_le_add (mul_le_mul_of_nonneg_left hA.2 ha) (mul_le_mul_of_nonneg_left hC.2 hb)
    _ = B := by rw [← add_mul, hab, one_mul]

def Supported (G : Submodule ℝ (E m)) (A : Mat m) : Prop :=
  ∀ x, Matrix.toEuclideanLin A x ∈ G

def feasible (G : Submodule ℝ (E m)) : Set (Mat m) :=
  {A | A.PosSemidef ∧ Supported G A ∧ ∀ i, A i i ≤ 1}

theorem isClosed_supported (G : Submodule ℝ (E m)) :
    IsClosed {A : Mat m | Supported G A} := by
  let : ContinuousSMul ℝ (E m) := IsBoundedSMul.continuousSMul
  simp only [Supported, Set.ofPred_forall]
  apply isClosed_iInter
  intro x
  let f : Mat m →ₗ[ℝ] E m :=
    (LinearMap.applyₗ x).comp Matrix.toEuclideanLin.toLinearMap
  exact G.closed_of_finiteDimensional.preimage f.continuous_of_finiteDimensional

theorem isClosed_feasible (G : Submodule ℝ (E m)) : IsClosed (feasible G) := by
  unfold feasible
  simp only [Set.ofPred_and, Set.ofPred_forall]
  exact isClosed_psd.inter ((isClosed_supported G).inter
    (isClosed_iInter fun i => isClosed_le (continuous_id.matrix_elem i i) continuous_const))

theorem feasible_trace_le (G : Submodule ℝ (E m)) {A : Mat m} (hA : A ∈ feasible G) :
    A.trace ≤ m := by
  calc
    A.trace ≤ ∑ _i : Fin m, (1 : ℝ) := Finset.sum_le_sum fun i _ => hA.2.2 i
    _ = m := by simp

theorem isCompact_feasible (G : Submodule ℝ (E m)) : IsCompact (feasible G) := by
  exact (isCompact_psdTraceBound (m : ℝ)).of_isClosed_subset (isClosed_feasible G)
    (fun A hA => ⟨hA.1, feasible_trace_le G hA⟩)

theorem convex_feasible (G : Submodule ℝ (E m)) : Convex ℝ (feasible G) := by
  intro A hA B hB a b ha hb hab
  refine ⟨(hA.1.smul ha).add (hB.1.smul hb), ?_, ?_⟩
  · intro x
    simpa only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
      using G.add_mem (G.smul_mem a (hA.2.1 x)) (G.smul_mem b (hB.2.1 x))
  · intro i
    change a * A i i + b * B i i ≤ 1
    calc
      _ ≤ a * 1 + b * 1 := add_le_add
        (mul_le_mul_of_nonneg_left (hA.2.2 i) ha)
        (mul_le_mul_of_nonneg_left (hB.2.2 i) hb)
      _ = 1 := by simpa using hab

theorem zero_mem_feasible (G : Submodule ℝ (E m)) : (0 : Mat m) ∈ feasible G := by
  refine ⟨Matrix.PosSemidef.zero, ?_, ?_⟩
  · intro x
    simpa only [map_zero, LinearMap.zero_apply] using G.zero_mem
  · intro i
    norm_num

theorem projectionMatrix_mem_feasible {G W : Submodule ℝ (E m)} (hWG : W ≤ G) :
    projectionMatrix W ∈ feasible G := by
  refine ⟨projectionMatrix_posSemidef W, ?_, projectionMatrix_diag_le_one W⟩
  intro x
  rw [projectionMatrix_toEuclideanLin]
  exact hWG (W.starProjection_apply_mem x)

theorem entry_sq_le_diag_mul {A : Mat m} (hA : A.PosSemidef) (i j : Fin m) :
    (A i j) ^ 2 ≤ A i i * A j j := by
  have hsym : A j i = A i j := by simpa using hA.isHermitian.apply i j
  have hq : ∀ t : ℝ, 0 ≤ A i i * (t * t) + (2 * A i j) * t + A j j := by
    intro t
    have hp := hA.2 (Finsupp.single i t + Finsupp.single j 1)
    simp [Finsupp.sum_add_index, mul_add, add_mul, hsym] at hp
    nlinarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith

theorem entry_eq_zero_of_diag_eq_zero {A : Mat m} (hA : A.PosSemidef)
    (i j : Fin m) (hi : A i i = 0) : A i j = 0 := by
  have h := entry_sq_le_diag_mul hA i j
  rw [hi, zero_mul] at h
  nlinarith [sq_nonneg (A i j)]

def sqrtDiagonal (A : Mat m) : Mat m := Matrix.diagonal fun i => Real.sqrt (A i i)

def whiten (A : Mat m) : Mat m :=
  let D := Matrix.diagonal fun i => (Real.sqrt (A i i))⁻¹
  D * A * D

theorem whiten_posSemidef {A : Mat m} (hA : A.PosSemidef) :
    (whiten A).PosSemidef := by
  simpa only [whiten, Matrix.diagonal_conjTranspose, star_trivial] using
    hA.mul_mul_conjTranspose_same (Matrix.diagonal fun i => (Real.sqrt (A i i))⁻¹)

theorem whiten_apply (A : Mat m) (i j : Fin m) :
    whiten A i j = (Real.sqrt (A i i))⁻¹ * A i j * (Real.sqrt (A j j))⁻¹ := by
  simp [whiten, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem whiten_diag_le_one {A : Mat m} (hA : A.PosSemidef) (i : Fin m) :
    whiten A i i ≤ 1 := by
  rw [whiten_apply]
  by_cases hi : A i i = 0
  · simp [hi]
  · have hs : Real.sqrt (A i i) ≠ 0 := Real.sqrt_ne_zero'.mpr <|
      lt_of_le_of_ne hA.diag_nonneg (Ne.symm hi)
    have he : (Real.sqrt (A i i))⁻¹ * A i i * (Real.sqrt (A i i))⁻¹ = 1 := by
      calc
        _ = (Real.sqrt (A i i))⁻¹ * (Real.sqrt (A i i)) ^ 2 *
            (Real.sqrt (A i i))⁻¹ := by rw [Real.sq_sqrt hA.diag_nonneg]
        _ = 1 := by field_simp
    exact he.le

theorem whiten_trace_le {A : Mat m} (hA : A.PosSemidef) : (whiten A).trace ≤ m := by
  calc
    (whiten A).trace ≤ ∑ _i : Fin m, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ => whiten_diag_le_one hA i
    _ = m := by simp

theorem reconstruct_whiten {A : Mat m} (hA : A.PosSemidef) :
    sqrtDiagonal A * whiten A * sqrtDiagonal A = A := by
  ext i j
  simp only [sqrtDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal, whiten_apply]
  by_cases hi : A i i = 0
  · simp [hi, entry_eq_zero_of_diag_eq_zero hA i j hi]
  by_cases hj : A j j = 0
  · have hz : A i j = 0 := by
      have hsym : A j i = A i j := by simpa using hA.isHermitian.apply i j
      rw [← hsym]
      exact entry_eq_zero_of_diag_eq_zero hA j i hj
    simp [hz]
  have hsi : Real.sqrt (A i i) ≠ 0 := Real.sqrt_ne_zero'.mpr <|
    lt_of_le_of_ne hA.diag_nonneg (Ne.symm hi)
  have hsj : Real.sqrt (A j j) ≠ 0 := Real.sqrt_ne_zero'.mpr <|
    lt_of_le_of_ne hA.diag_nonneg (Ne.symm hj)
  field_simp

theorem sqrtDiagonal_sq {A : Mat m} (hA : A.PosSemidef) :
    sqrtDiagonal A * sqrtDiagonal A = Matrix.diagonal (Matrix.diag A) := by
  rw [sqrtDiagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact Real.mul_self_sqrt hA.diag_nonneg

theorem toEuclideanLin_mul (A B : Mat m) :
    Matrix.toEuclideanLin (A * B) = Matrix.toEuclideanLin A ∘ₗ Matrix.toEuclideanLin B :=
  Matrix.toLpLin_mul 2 2 2 A B

def quad (A : Mat m) (x : E m) : ℝ := inner ℝ x (Matrix.toEuclideanLin A x)

theorem quad_add (A B : Mat m) (x : E m) :
    quad (A + B) x = quad A x + quad B x := by
  simp only [quad, map_add, LinearMap.add_apply]
  exact inner_add_right _ _ _

theorem quad_sub (A B : Mat m) (x : E m) :
    quad (A - B) x = quad A x - quad B x := by
  simp only [quad, map_sub, LinearMap.sub_apply]
  exact inner_sub_right _ _ _

theorem quad_smul (r : ℝ) (A : Mat m) (x : E m) :
    quad (r • A) x = r * quad A x := by
  simp only [quad, map_smul, LinearMap.smul_apply]
  exact real_inner_smul_right _ _ _

theorem quad_congr (A B : Mat m) (hB : B.IsHermitian) (x : E m) :
    quad (B * A * B) x = quad A (Matrix.toEuclideanLin B x) := by
  simp only [quad, toEuclideanLin_mul, LinearMap.comp_apply]
  exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB _ _).symm

theorem posSemidef_iff_quad_nonneg {A : Mat m} (hA : A.IsHermitian) :
    A.PosSemidef ↔ ∀ x, 0 ≤ quad A x := by
  rw [← Matrix.isPositive_toEuclideanLin_iff, LinearMap.IsPositive]
  simp only [Matrix.isSymmetric_toEuclideanLin_iff, hA, true_and, quad,
    RCLike.re_to_real]
  exact forall_congr' (fun x => by rw [real_inner_comm x])

theorem eigenvector_toEuclideanLin {A : Mat m} (hA : A.IsHermitian) (i : Fin m) :
    Matrix.toEuclideanLin A (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
  apply PiLp.ext
  intro j
  exact congrFun (hA.mulVec_eigenvectorBasis i) j

theorem quad_eq_sum_eigenvalues {A : Mat m} (hA : A.IsHermitian) (x : E m) :
    quad A x = ∑ i, hA.eigenvalues i * (inner ℝ (hA.eigenvectorBasis i) x) ^ 2 := by
  unfold quad
  rw [← hA.eigenvectorBasis.sum_inner_mul_inner x (Matrix.toEuclideanLin A x)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Matrix.isSymmetric_toEuclideanLin_iff.mpr hA, eigenvector_toEuclideanLin,
    real_inner_smul_left, real_inner_comm (hA.eigenvectorBasis i) x]
  ring

theorem inner_self_eq_sum_eigenbasis {A : Mat m} (hA : A.IsHermitian) (x : E m) :
    inner ℝ x x = ∑ i, (inner ℝ (hA.eigenvectorBasis i) x) ^ 2 := by
  rw [← hA.eigenvectorBasis.sum_inner_mul_inner x x]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm (hA.eigenvectorBasis i) x, pow_two]

theorem low_eigen_quad_le {A : Mat m} (hA : A.IsHermitian) (κ : ℝ) (x : E m)
    (hx : ∀ i, κ < hA.eigenvalues i → inner ℝ (hA.eigenvectorBasis i) x = 0) :
    quad A x ≤ κ * inner ℝ x x := by
  rw [quad_eq_sum_eigenvalues hA, inner_self_eq_sum_eigenbasis hA, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : κ < hA.eigenvalues i
  · simp [hx i hi]
  · exact mul_le_mul_of_nonneg_right (le_of_not_gt hi) (sq_nonneg _)

abbrev High {A : Mat m} (hA : A.IsHermitian) (κ : ℝ) :=
  {i : Fin m // κ < hA.eigenvalues i}

theorem high_count_mul_le_trace {A : Mat m} (hA : A.PosSemidef) (κ : ℝ) :
    (Fintype.card (High hA.isHermitian κ) : ℝ) * κ ≤ A.trace := by
  classical
  let s : Finset (Fin m) := Finset.univ.filter (fun i => κ < hA.isHermitian.eigenvalues i)
  have hc : Fintype.card (High hA.isHermitian κ) = s.card := by
    simp [High, s, Fintype.card_subtype]
  rw [hc, hA.isHermitian.trace_eq_sum_eigenvalues]
  calc
    (s.card : ℝ) * κ = ∑ _i ∈ s, κ := by simp
    _ ≤ ∑ i ∈ s, hA.isHermitian.eigenvalues i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Finset.mem_filter.mp hi).2.le
    _ ≤ ∑ i, hA.isHermitian.eigenvalues i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
        (fun i _ _ => hA.eigenvalues_nonneg i)

def highCoordinates {A : Mat m} (hA : A.IsHermitian) (κ : ℝ) :
    E m →ₗ[ℝ] (High hA κ → ℝ) where
  toFun x i := inner ℝ (hA.eigenvectorBasis i) x
  map_add' x y := by ext i; exact inner_add_right _ _ _
  map_smul' r x := by ext i; exact real_inner_smul_right _ _ _

theorem finrank_inf_ker_add {ι : Type*} [Fintype ι]
    (G : Submodule ℝ (E m)) (F : E m →ₗ[ℝ] (ι → ℝ)) :
    Module.finrank ℝ G ≤ Module.finrank ℝ (G ⊓ F.ker : Submodule ℝ (E m)) + Fintype.card ι := by
  have hr := F.finrank_range_add_finrank_ker
  have hi := G.finrank_sup_add_finrank_inf_eq F.ker
  have hs := Submodule.finrank_le (G ⊔ F.ker)
  have hf := Submodule.finrank_le F.range
  simp only [finrank_euclideanSpace, Fintype.card_fin, Module.finrank_fintype_fun_eq_card] at *
  omega

theorem sqrtDiagonal_isHermitian (A : Mat m) : (sqrtDiagonal A).IsHermitian := by
  simp [sqrtDiagonal, Matrix.IsHermitian]

theorem quad_diag_eq {A : Mat m} (hA : A.PosSemidef) (x : E m) :
    quad (Matrix.diagonal (Matrix.diag A)) x =
      inner ℝ (Matrix.toEuclideanLin (sqrtDiagonal A) x)
        (Matrix.toEuclideanLin (sqrtDiagonal A) x) := by
  rw [← sqrtDiagonal_sq hA]
  simp only [quad, toEuclideanLin_mul, LinearMap.comp_apply]
  exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr (sqrtDiagonal_isHermitian A) _ _).symm

theorem quad_whiten_eq {A : Mat m} (hA : A.PosSemidef) (x : E m) :
    quad A x = quad (whiten A) (Matrix.toEuclideanLin (sqrtDiagonal A) x) := by
  calc
    quad A x = quad (sqrtDiagonal A * whiten A * sqrtDiagonal A) x :=
      congrArg (fun B => quad B x) (reconstruct_whiten hA).symm
    _ = _ := quad_congr _ _ (sqrtDiagonal_isHermitian A) x

theorem exists_good_subspace (G : Submodule ℝ (E m)) {A : Mat m}
    (hA : A.PosSemidef) {κ : ℝ} (hκ : 0 < κ) :
    ∃ W : Submodule ℝ (E m), W ≤ G ∧
      (Module.finrank ℝ G : ℝ) - (m : ℝ) / κ ≤ Module.finrank ℝ W ∧
      ∀ x ∈ W, 0 ≤ quad (κ • Matrix.diagonal (Matrix.diag A) - A) x := by
  classical
  let C := whiten A
  have hC : C.PosSemidef := whiten_posSemidef hA
  let F := (highCoordinates hC.isHermitian κ).comp
    (Matrix.toEuclideanLin (sqrtDiagonal A))
  let W := G ⊓ F.ker
  refine ⟨W, inf_le_left, ?_, ?_⟩
  · have hd := finrank_inf_ker_add G F
    have hc : (Fintype.card (High hC.isHermitian κ) : ℝ) ≤ (m : ℝ) / κ := by
      apply (le_div_iff₀ hκ).mpr
      exact (high_count_mul_le_trace hC κ).trans (whiten_trace_le hA)
    have hdr : (Module.finrank ℝ G : ℝ) ≤
        Module.finrank ℝ W + (Fintype.card (High hC.isHermitian κ) : ℝ) := by
      exact_mod_cast hd
    linarith
  · intro x hx
    have hx0 : F x = 0 := hx.2
    have hl : ∀ i, κ < hC.isHermitian.eigenvalues i →
        inner ℝ (hC.isHermitian.eigenvectorBasis i)
          (Matrix.toEuclideanLin (sqrtDiagonal A) x) = 0 := by
      intro i hi
      exact congrFun hx0 ⟨i, hi⟩
    have hq := low_eigen_quad_le hC.isHermitian κ _ hl
    rw [quad_sub, quad_smul, quad_diag_eq hA, quad_whiten_eq hA]
    exact sub_nonneg.mpr hq

theorem linearFunctional_expansion (f : Mat m →ₗ[ℝ] ℝ) (A : Mat m) :
    f A = ∑ i, ∑ j, A i j * f (Matrix.single i j 1) := by
  calc
    f A = f (∑ i, ∑ j, A i j • Matrix.single i j 1) := by
      congr 1
      simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using
        Matrix.matrix_eq_sum_single A
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]

def rawDualMatrix (f : Mat m →ₗ[ℝ] ℝ) : Mat m := fun i j => f (Matrix.single j i 1)

theorem rawDualMatrix_trace (f : Mat m →ₗ[ℝ] ℝ) (A : Mat m) :
    (rawDualMatrix f * A).trace = f A := by
  rw [linearFunctional_expansion f A]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, rawDualMatrix]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

def dualMatrix (f : Mat m →ₗ[ℝ] ℝ) : Mat m :=
  (1 / 2 : ℝ) • (rawDualMatrix f + (rawDualMatrix f).transpose)

theorem dualMatrix_isHermitian (f : Mat m →ₗ[ℝ] ℝ) : (dualMatrix f).IsHermitian := by
  ext i j
  simp [dualMatrix, rawDualMatrix, add_comm, mul_add]

theorem transpose_eq_of_isHermitian {A : Mat m} (hA : A.IsHermitian) : A.transpose = A := by
  ext i j
  exact hA.apply i j

theorem dualMatrix_trace (f : Mat m →ₗ[ℝ] ℝ) {A : Mat m} (hA : A.IsHermitian) :
    (dualMatrix f * A).trace = f A := by
  have ht : ((rawDualMatrix f).transpose * A).trace = (rawDualMatrix f * A).trace := by
    rw [← Matrix.trace_transpose ((rawDualMatrix f).transpose * A), Matrix.transpose_mul,
      Matrix.transpose_transpose, transpose_eq_of_isHermitian hA, Matrix.trace_mul_comm]
  simp only [dualMatrix, Matrix.smul_mul, Matrix.add_mul, Matrix.trace_smul,
    Matrix.trace_add, smul_eq_mul, ht, rawDualMatrix_trace]
  ring

theorem trace_mul_vecMulVec (A : Mat m) (x : E m) :
    (A * Matrix.vecMulVec (fun i => x i) (fun i => x i)).trace = quad A x := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, quad]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  rfl

theorem dualMatrix_posSemidef (f : Mat m →ₗ[ℝ] ℝ)
    (hf : ∀ A : Mat m, A.PosSemidef → 0 ≤ f A) : (dualMatrix f).PosSemidef := by
  apply (posSemidef_iff_quad_nonneg (dualMatrix_isHermitian f)).mpr
  intro x
  rw [← trace_mul_vecMulVec]
  have hp : (Matrix.vecMulVec (fun i => x i) (fun i => x i)).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (fun i => x i)
  rw [dualMatrix_trace f hp.isHermitian]
  exact hf _ hp

theorem projectionMatrix_mul_self (G : Submodule ℝ (E m)) :
    projectionMatrix G * projectionMatrix G = projectionMatrix G := by
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_mul, projectionMatrix_toEuclideanLin]
  ext x i
  exact congrArg (fun y : E m => y i)
    (G.starProjection_eq_self_iff.mpr (G.starProjection_apply_mem x))

theorem trace_mul_projection_nonneg {A : Mat m} (hA : A.IsHermitian)
    (W : Submodule ℝ (E m)) (hW : ∀ x ∈ W, 0 ≤ quad A x) :
    0 ≤ (A * projectionMatrix W).trace := by
  let P := projectionMatrix W
  have hP : P.IsHermitian := (projectionMatrix_posSemidef W).isHermitian
  have hPA : (P * A * P).IsHermitian := by
    simpa only [hP.eq] using Matrix.isHermitian_conjTranspose_mul_mul P hA
  have hp : (P * A * P).PosSemidef := by
    apply (posSemidef_iff_quad_nonneg hPA).mpr
    intro x
    rw [quad_congr A P hP]
    apply hW
    rw [projectionMatrix_toEuclideanLin]
    exact W.starProjection_apply_mem x
  have ht : (P * A * P).trace = (A * P).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, projectionMatrix_mul_self,
      Matrix.trace_mul_comm]
  rw [← ht]
  exact hp.trace_nonneg

theorem exists_dual_projection (G : Submodule ℝ (E m)) {A : Mat m}
    (hA : A.PosSemidef) {κ ζ : ℝ} (hκ : 0 < κ)
    (hdim : ((1 / κ + ζ) * m) ≤ Module.finrank ℝ G) :
    ∃ P ∈ feasible G, ζ * m ≤ P.trace ∧
      0 ≤ ((κ • Matrix.diagonal (Matrix.diag A) - A) * P).trace := by
  obtain ⟨W, hWG, hd, hW⟩ := exists_good_subspace G hA hκ
  refine ⟨projectionMatrix W, projectionMatrix_mem_feasible hWG, ?_, ?_⟩
  · rw [projectionMatrix_trace]
    have he : (1 / κ + ζ) * m = (m : ℝ) / κ + ζ * m := by ring
    rw [he] at hdim
    linarith
  · apply trace_mul_projection_nonneg _ W hW
    exact (by simp [Matrix.IsHermitian, transpose_eq_of_isHermitian hA.isHermitian])

def slack (κ : ℝ) (A : Mat m) : Mat m := κ • Matrix.diagonal (Matrix.diag A) - A

theorem slack_isHermitian {A : Mat m} (hA : A.IsHermitian) (κ : ℝ) :
    (slack κ A).IsHermitian := by
  simp [slack, Matrix.IsHermitian, transpose_eq_of_isHermitian hA]

theorem trace_slack_commutes (κ : ℝ) (A B : Mat m) :
    (A * slack κ B).trace = (slack κ A * B).trace := by
  have he : (A * Matrix.diagonal (Matrix.diag B)).trace =
      (Matrix.diagonal (Matrix.diag A) * B).trace := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [slack, Matrix.mul_sub, Matrix.mul_smul, Matrix.sub_mul, Matrix.smul_mul,
    Matrix.trace_sub, Matrix.trace_smul, he]

def constraintMap (κ : ℝ) : Mat m →ₗ[ℝ] Mat m × ℝ where
  toFun A := (slack κ A, A.trace)
  map_add' A B := by
    apply Prod.ext
    · change slack κ (A + B) = slack κ A + slack κ B
      ext i j
      by_cases hij : i = j <;>
        simp [slack, Matrix.diagonal, hij, mul_add, sub_add_sub_comm, add_comm]
    · change (A + B).trace = A.trace + B.trace
      exact Matrix.trace_add _ _
  map_smul' r A := by
    apply Prod.ext
    · simp [slack, Matrix.diag_smul, Matrix.diagonal_smul, smul_sub, smul_smul, mul_comm]
    · change (r • A).trace = r • A.trace
      exact Matrix.trace_smul _ _

theorem convex_psd : Convex ℝ {A : Mat m | A.PosSemidef} := by
  intro A hA B hB a b ha hb _
  exact (hA.smul ha).add (hB.smul hb)

theorem nonneg_of_ray_lower_bound {a b c : ℝ}
    (h : ∀ t : ℝ, 0 ≤ t → c < t * a + b) : 0 ≤ a := by
  by_contra hn
  have ha : a < 0 := lt_of_not_ge hn
  have ha0 : a ≠ 0 := ne_of_lt ha
  let t := (|b - c| + 1) / (-a)
  have ht : 0 ≤ t := div_nonneg (by positivity) (neg_nonneg.mpr ha.le)
  have he : t * a = -(|b - c| + 1) := by
    dsimp [t]
    field_simp
  have hc := h t ht
  rw [he] at hc
  have hab := le_abs_self (b - c)
  linarith

theorem subspace_covariance (G : Submodule ℝ (E m)) {κ ζ : ℝ}
    (hκ : 1 < κ) (_hζ : 0 < ζ)
    (hdim : (1 / κ + ζ) * (m : ℝ) ≤ Module.finrank ℝ G) :
    ∃ Γ : Mat m, Γ.PosSemidef ∧ Supported G Γ ∧
      (∀ i, Γ i i ≤ 1) ∧ (slack κ Γ).PosSemidef ∧ ζ * m ≤ Γ.trace := by
  classical
  let b : ℝ := ζ * m
  let S := (constraintMap (m := m) κ) '' feasible G
  let T : Set (Mat m × ℝ) := {A : Mat m | A.PosSemidef} ×ˢ Set.Ici b
  by_contra hnone
  have hd : Disjoint S T := by
    rw [Set.disjoint_left]
    rintro _ ⟨Γ, hΓ, rfl⟩ hT
    exact hnone ⟨Γ, hΓ.1, hΓ.2.1, hΓ.2.2, hT.1, hT.2⟩
  have hSc : Convex ℝ S := (convex_feasible G).linear_image (constraintMap κ)
  have hSk : IsCompact S := (isCompact_feasible G).image
    (constraintMap κ).continuous_of_finiteDimensional
  have hTc : Convex ℝ T := convex_psd.prod (convex_Ici b)
  have hTk : IsClosed T := isClosed_psd.prod isClosed_Ici
  obtain ⟨f, u, v, hS, huv, hT⟩ :=
    geometric_hahn_banach_compact_closed hSc hSk hTc hTk hd
  let g : Mat m →ₗ[ℝ] ℝ := f.toLinearMap.comp (LinearMap.inl ℝ (Mat m) ℝ)
  let a : ℝ := f (0, 1)
  have hsplit : ∀ B : Mat m, ∀ t : ℝ, f (B, t) = g B + a * t := by
    intro B t
    calc
      f (B, t) = f ((B, 0) + t • (0, 1)) := by simp
      _ = f (B, 0) + t * f (0, 1) := by rw [map_add, map_smul]; rfl
      _ = _ := by change f (B, 0) + t * f (0, 1) = f (B, 0) + f (0, 1) * t; ring
  have hg : ∀ B : Mat m, B.PosSemidef → 0 ≤ g B := by
    intro B hB
    apply nonneg_of_ray_lower_bound (b := a * b) (c := v)
    intro t ht
    have h := hT (t • B, b) ⟨hB.smul ht, by change b ≤ b; rfl⟩
    rw [hsplit, map_smul, smul_eq_mul] at h
    exact h
  have ha : 0 ≤ a := by
    apply nonneg_of_ray_lower_bound (b := a * b) (c := v)
    intro t ht
    have h := hT (0, b + t) ⟨Matrix.PosSemidef.zero, le_add_of_nonneg_right ht⟩
    rw [hsplit, map_zero, zero_add] at h
    nlinarith
  have hA : (dualMatrix g).PosSemidef := dualMatrix_posSemidef g hg
  obtain ⟨P, hP, htr, hpair⟩ := exists_dual_projection G hA (lt_trans zero_lt_one hκ) hdim
  have hgp : 0 ≤ g (slack κ P) := by
    rw [← dualMatrix_trace g (slack_isHermitian hP.1.isHermitian κ), trace_slack_commutes]
    exact hpair
  have hpS := hS (constraintMap κ P) ⟨P, hP, rfl⟩
  have hpT := hT (0, b) ⟨Matrix.PosSemidef.zero, by change b ≤ b; rfl⟩
  change f (slack κ P, P.trace) < u at hpS
  rw [hsplit] at hpS hpT
  simp only [map_zero, zero_add] at hpT
  have hmul : a * b ≤ a * P.trace := mul_le_mul_of_nonneg_left htr ha
  linarith

end
end CurrentKS.Covariance

end OAI
