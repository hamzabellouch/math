import OAI.GroupTheory.Hyperbolic.Model

namespace OAI

namespace Release075

universe u v

open scoped BigOperators

theorem det_abs_le_prod_row_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    |A.det| ≤ ∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin n))‖ := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let v : Fin n → EuclideanSpace ℝ (Fin n) := fun i => WithLp.toLp 2 (A i)
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) := ⟨by simp⟩
  have h := b.toBasis.orientation.abs_volumeForm_apply_le v
  rw [b.toBasis.orientation.volumeForm_robust b rfl] at h
  have hmat : b.toBasis.toMatrix v = A.transpose := by
    ext i j
    simp [Module.Basis.toMatrix_apply, b, v, Matrix.transpose_apply]
  simpa [Module.Basis.det_apply, hmat, Matrix.det_transpose, v] using h

/-- A matrix has a spanning independent subset of its rows, with the expected size. -/
theorem exists_row_basis {ι κ K : Type*} [Fintype ι] [Fintype κ] [Field K]
    (M : Matrix ι κ K) :
    ∃ S : Finset ι, S.card = M.rank ∧
      LinearIndependent K (fun i : S => M i.val) ∧
      ∀ i, ∃ c : S → K, M i = ∑ j : S, c j • M j.val := by
  classical
  obtain ⟨T, _, _, hspan, hlin⟩ := exists_linearIndepOn_extension
    (linearIndepOn_empty K M.row) (Set.empty_subset (Set.univ : Set ι))
  let S := T.toFinset
  have hS : (S : Set ι) = T := Set.coe_toFinset T
  have hlinS : LinearIndepOn K M.row (S : Set ι) := by rw [hS]; exact hlin
  have hrange : Set.range (fun i : S => M.row i.val) = M.row '' (S : Set ι) := by
    ext x
    simp
  have hsp : Submodule.span K (Set.range (fun i : S => M.row i.val)) =
      Submodule.span K (Set.range M.row) := by
    rw [hrange]
    apply le_antisymm
    · exact Submodule.span_mono (Set.image_subset_range _ _)
    · apply Submodule.span_le.mpr
      rw [hS]
      simpa only [Set.image_univ] using hspan
  refine ⟨S, ?_, hlinS, ?_⟩
  · rw [M.rank_eq_finrank_span_row, ← hsp]
    simpa only [Finset.coe_sort_coe, Fintype.card_coe] using (finrank_span_eq_card hlinS).symm
  · intro i
    have hi : M.row i ∈ Submodule.span K (Set.range (fun j : S => M.row j.val)) := by
      rw [hsp]
      exact Submodule.subset_span (Set.mem_range_self i)
    rcases (Submodule.mem_span_range_iff_exists_fun K).mp hi with ⟨c, hc⟩
    exact ⟨c, hc.symm⟩

/-- Factoring a common divisor from all rows outside a specified set. -/
theorem pow_sub_card_dvd_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (S : Finset ι) (q : ℤ)
    (h : ∀ i, i ∉ S → ∀ j, q ∣ A i j) :
    q ^ (Fintype.card ι - S.card) ∣ A.det := by
  classical
  have hd : ∀ i j, (if i ∈ S then (1 : ℤ) else q) ∣ A i j := by
    intro i j
    split_ifs with hi
    · exact one_dvd _
    · exact h i hi j
  choose B hB using hd
  have hA : A = Matrix.of (fun i j => (if i ∈ S then (1 : ℤ) else q) * B i j) := by
    ext i j
    exact hB i j
  have hprod : (∏ i : ι, if i ∈ S then (1 : ℤ) else q) =
      q ^ (Fintype.card ι - S.card) := by
    simp only [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 1
    have hcard := Finset.card_filter_add_card_filter_not (s := Finset.univ) (· ∈ S)
    have hfilter : Finset.univ.filter (· ∈ S) = S := by ext; simp
    rw [hfilter, Finset.card_univ] at hcard
    omega
  refine ⟨Matrix.det (Matrix.of B), ?_⟩
  rw [hA]
  simpa only [hprod, Matrix.of_apply] using Matrix.det_mul_column (fun i => if i ∈ S then (1 : ℤ) else q) (Matrix.of B)

/-- The integral determinant detects the rank lost in reduction modulo a prime. -/
theorem pow_card_sub_rank_dvd_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (q : ℕ) [Fact q.Prime] :
    (q : ℤ) ^ (Fintype.card ι - (A.map (Int.cast : ℤ → ZMod q)).rank) ∣ A.det := by
  classical
  let M : Matrix ι ι (ZMod q) := A.map Int.cast
  obtain ⟨S, hScard, _, hspan⟩ := exists_row_basis M
  choose c hc using hspan
  let C : Matrix ι ι ℤ := fun i j =>
    if i ∈ S then 0 else if hj : j ∈ S then (c i ⟨j, hj⟩).cast else 0
  have hCC : C * C = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k ∈ S
    · simp [C, hk]
    · by_cases hi : i ∈ S <;> simp [C, hi, hk]
  have hunit : IsUnit (1 - C).det := by
    apply isUnit_iff_dvd_one.mpr
    refine ⟨(1 + C).det, ?_⟩
    rw [← Matrix.det_mul]
    have hinv : (1 - C) * (1 + C) = 1 := by
      simp [mul_add, sub_mul, hCC]
    rw [hinv, Matrix.det_one]
  have hdiv : ∀ i, i ∉ S → ∀ j, (q : ℤ) ∣ ((1 - C) * A) i j := by
    intro i hi j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
    rw [sub_mul, one_mul]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Int.cast_sub, Int.cast_sum, Int.cast_mul]
    apply sub_eq_zero.mpr
    have hrestrict : (∑ k : ι, (C i k : ZMod q) * (A k j : ZMod q)) =
        ∑ k ∈ S, (C i k : ZMod q) * (A k j : ZMod q) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro k _ hk
      simp [C, hi, hk]
    rw [hrestrict, ← Finset.sum_coe_sort]
    have heval := congrArg (fun v : ι → ZMod q => v j) (hc i)
    simpa [C, hi, M, Matrix.map_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using heval
  have hd := pow_sub_card_dvd_det ((1 - C) * A) S (q : ℤ) hdiv
  rw [Matrix.det_mul] at hd
  rw [← hScard]
  exact hunit.dvd_mul_left.mp hd

/-- A full-rank minor exists over a field; both index maps are injective. -/
theorem exists_full_rank_minor {ι κ K : Type*} [Fintype ι] [Fintype κ] [Field K]
    (M : Matrix ι κ K) :
    ∃ (f : Fin M.rank → ι) (g : Fin M.rank → κ),
      Function.Injective f ∧ Function.Injective g ∧ (M.submatrix f g).det ≠ 0 := by
  classical
  obtain ⟨S, hScard, hSlin, _⟩ := exists_row_basis M
  have hScard' : Fintype.card S = M.rank := by simpa using hScard
  let eS : Fin M.rank ≃ S := (Fintype.equivFinOfCardEq hScard').symm
  let f : Fin M.rank → ι := fun i => (eS i).val
  let R : Matrix (Fin M.rank) κ K := M.submatrix f id
  have hRlin : LinearIndependent K R.row := hSlin.comp eS eS.injective
  have hRrank : R.rank = M.rank := by
    simpa only [Fintype.card_fin] using hRlin.rank_matrix
  obtain ⟨T, hTcard, hTlin, _⟩ := exists_row_basis R.transpose
  have hTcard' : Fintype.card T = M.rank := by
    simpa only [Fintype.card_coe, Matrix.rank_transpose, hRrank] using hTcard
  let eT : Fin M.rank ≃ T := (Fintype.equivFinOfCardEq hTcard').symm
  let g : Fin M.rank → κ := fun i => (eT i).val
  have hBlin : LinearIndependent K (M.submatrix f g).col := hTlin.comp eT eT.injective
  refine ⟨f, g, Subtype.val_injective.comp eS.injective,
    Subtype.val_injective.comp eT.injective, ?_⟩
  exact Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.Nonsingular.of_linearIndependent_col hBlin)

/-- The squared form of Hadamard's inequality avoids fractional exponents. -/
theorem det_sq_le_pow_of_row_sq_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (r : ℝ) (hrow : ∀ i, ∑ j, A i j ^ 2 ≤ r) : A.det ^ 2 ≤ r ^ n := by
  have h := det_abs_le_prod_row_norm A
  have hsquare : A.det ^ 2 ≤
      (∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin n))‖) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg A.det) h 2
  rw [← Finset.prod_pow] at hsquare
  apply hsquare.trans
  calc
    (∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin n))‖ ^ 2)
        ≤ ∏ _i : Fin n, r := by
      apply Finset.prod_le_prod₀
      · intro i _; positivity
      · intro i _
        simpa only [EuclideanSpace.real_norm_sq_eq] using hrow i
    _ = r ^ n := by simp

/-- A nonsingular integer matrix loses less than half its rank modulo a prime
larger than the common squared row-norm bound. -/
theorem nonsingular_rank_reduction_half {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hdet : A.det ≠ 0) (r : ℝ) (hr : 1 ≤ r)
    (hrow : ∀ i, ∑ j, (A i j : ℝ) ^ 2 ≤ r)
    (q : ℕ) [Fact q.Prime] (hqr : r < q) :
    n ≤ 2 * (A.map (Int.cast : ℤ → ZMod q)).rank := by
  let AR : Matrix (Fin n) (Fin n) ℝ := A.map Int.cast
  let d := (A.map (Int.cast : ℤ → ZMod q)).rank
  have hcastdet : AR.det = (A.det : ℝ) := by
    simpa [AR] using (RingHom.map_det (Int.castRingHom ℝ) A).symm
  have hbound : AR.det ^ 2 ≤ r ^ n := det_sq_le_pow_of_row_sq_le AR r hrow
  have hdiv : (q : ℤ) ^ (n - d) ∣ A.det := by
    simpa only [Fintype.card_fin] using pow_card_sub_rank_dvd_det A q
  have hleI : (q : ℤ) ^ (n - d) ≤ |A.det| :=
    Int.le_of_dvd (abs_pos.mpr hdet) ((dvd_abs _ _).mpr hdiv)
  have hleR : (q : ℝ) ^ (n - d) ≤ |AR.det| := by
    rw [hcastdet]
    exact_mod_cast hleI
  have hsq := pow_le_pow_left₀ (pow_nonneg (Nat.cast_nonneg q) (n - d)) hleR 2
  rw [sq_abs, ← pow_mul] at hsq
  by_cases hn : n = 0
  · simp [hn]
  have hrnonneg : 0 ≤ r := le_trans zero_le_one hr
  have hstrict : (q : ℝ) ^ ((n - d) * 2) < (q : ℝ) ^ n :=
    (hsq.trans hbound).trans_lt (pow_lt_pow_left₀ hqr hrnonneg hn)
  have hexp : (n - d) * 2 < n :=
    (pow_lt_pow_iff_right₀ (lt_of_le_of_lt hr hqr)).mp hstrict
  change n ≤ 2 * d
  omega

theorem rank_reduction_half {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℤ) (r : ℝ) (hr : 1 ≤ r)
    (hrow : ∀ i, ∑ j, (M i j : ℝ) ^ 2 ≤ r)
    (q : ℕ) [Fact q.Prime] (hqr : r < q) :
    (M.map (Int.cast : ℤ → ℝ)).rank ≤
      2 * (M.map (Int.cast : ℤ → ZMod q)).rank := by
  classical
  let MR := M.map (Int.cast : ℤ → ℝ)
  obtain ⟨f, g, _, hg, hdet⟩ := exists_full_rank_minor MR
  let B := M.submatrix f g
  have hBR : B.map (Int.cast : ℤ → ℝ) = MR.submatrix f g := by
    rw [Matrix.submatrix_map]
  have hBdet : B.det ≠ 0 := by
    intro h
    apply hdet
    have hcast : (B.map (Int.cast : ℤ → ℝ)).det = (B.det : ℝ) := by
      simpa using (RingHom.map_det (Int.castRingHom ℝ) B).symm
    rw [← hBR, hcast, h]
    simp
  have hBrow : ∀ i, ∑ j, (B i j : ℝ) ^ 2 ≤ r := by
    intro i
    apply le_trans _ (hrow (f i))
    change (∑ j, (M (f i) (g j) : ℝ) ^ 2) ≤ _
    rw [← Finset.sum_image (f := fun j => (M (f i) j : ℝ) ^ 2)
      (s := Finset.univ) hg.injOn]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
      intro j _ _; positivity)
  have hh := nonsingular_rank_reduction_half B hBdet r hr hBrow q hqr
  apply hh.trans
  apply Nat.mul_le_mul_left
  change ((M.submatrix f g).map (Int.cast : ℤ → ZMod q)).rank ≤ _
  rw [← Matrix.submatrix_map]
  exact Matrix.rank_submatrix_le _ _ _

/-- The trace-rank inequality used on a Gram matrix in the finite quotient. -/
theorem trace_sq_le_rank_mul_trace_sq {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) :
    A.trace ^ 2 ≤ (A.rank : ℝ) * (A * A).trace := by
  classical
  have htrace : (A * A).trace = ∑ i, hA.eigenvalues i ^ 2 := by
    conv_lhs => rw [hA.spectral_theorem, ← map_mul, Matrix.diagonal_mul_diagonal,
      Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
      one_mul, Matrix.trace_diagonal]
    simp [pow_two]
  rw [hA.trace_eq_sum_eigenvalues, htrace, hA.rank_eq_card_non_zero_eigs]
  let T : Finset ι := Finset.univ.filter (fun i => hA.eigenvalues i ≠ 0)
  have hcard : Fintype.card {i // hA.eigenvalues i ≠ 0} = T.card := by
    simp [T, Fintype.card_subtype]
  have hsum : (∑ i ∈ T, hA.eigenvalues i) = ∑ i, hA.eigenvalues i :=
    Finset.sum_filter_ne_zero _
  have hsum2 : (∑ i ∈ T, hA.eigenvalues i ^ 2) = ∑ i, hA.eigenvalues i ^ 2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have : hA.eigenvalues i = 0 := by simpa [T] using hi
    simp [this]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq T (fun _ => (1 : ℝ)) hA.eigenvalues
  simpa [hsum, hsum2, hcard] using hcs

/-- Subadditivity of matrix rank over a field. -/
theorem rank_add_le {ι κ K : Type*} [Fintype ι] [Fintype κ] [Field K]
    (A B : Matrix ι κ K) : (A + B).rank ≤ A.rank + B.rank := by
  rw [Matrix.rank, Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem rank_sum_le {ι κ τ K : Type*} [Fintype ι] [Fintype κ] [Field K]
    (s : Finset τ) (A : τ → Matrix ι κ K) : (∑ t ∈ s, A t).rank ≤ ∑ t ∈ s, (A t).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.rank_zero]
  | @insert t s ht ih =>
    simp only [Finset.sum_insert ht]
    exact (rank_add_le _ _).trans (Nat.add_le_add_left ih _)

/-- The left regular permutation representation over any coefficient semiring. -/
def regularMatrix {F R : Type*} [Group F] [Fintype F] [DecidableEq F] [Semiring R] :
    F →* Matrix F F R := Matrix.permMatrixHom.comp (MulAction.toPermHom F F)

@[simp] theorem regularMatrix_apply {F R : Type*} [Group F] [Fintype F]
    [DecidableEq F] [Semiring R] (g a b : F) :
    regularMatrix (R := R) g a b = if a = g * b then 1 else 0 := by
  simp [regularMatrix, Matrix.permMatrixHom, Equiv.Perm.permMatrix,
    PEquiv.toMatrix, Equiv.toPEquiv_apply, inv_mul_eq_iff_eq_mul]

@[simp] theorem regularMatrix_transpose {F R : Type*} [Group F] [Fintype F]
    [DecidableEq F] [Semiring R] (g : F) :
    (regularMatrix (R := R) g).transpose = regularMatrix g⁻¹ := by
  ext a b
  simp [eq_inv_mul_iff_mul_eq, eq_comm]

@[simp] theorem regularMatrix_trace {F R : Type*} [Group F] [Fintype F]
    [DecidableEq F] [Semiring R] (g : F) :
    (regularMatrix (R := R) g).trace = if g = 1 then (Fintype.card F : R) else 0 := by
  by_cases hg : g = 1
  · subst g; simp
  · have hfix : ∀ a : F, a ≠ g * a := by
      intro a ha
      exact hg (mul_right_cancel (show g * a = 1 * a by simpa using ha.symm))
    simp [Matrix.trace, hfix, hg]

/-- Flatten a rectangular matrix of blocks, with the block index first. -/
def flattenMatrix {ι κ α β R : Type*} (A : Matrix ι κ (Matrix α β R)) :
    Matrix (ι × α) (κ × β) R := fun i j => A i.1 j.1 i.2 j.2

@[simp] theorem flattenMatrix_apply {ι κ α β R : Type*}
    (A : Matrix ι κ (Matrix α β R)) (i : ι × α) (j : κ × β) :
    flattenMatrix A i j = A i.1 j.1 i.2 j.2 := rfl

theorem flattenMatrix_mul {ι κ τ F R : Type*} [Fintype κ] [Fintype F]
    [DecidableEq F] [Semiring R] (A : Matrix ι κ (Matrix F F R))
    (B : Matrix κ τ (Matrix F F R)) :
    flattenMatrix (A * B) = flattenMatrix A * flattenMatrix B := by
  ext ⟨i,a⟩ ⟨j,b⟩
  simp [flattenMatrix, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.sum_apply]

theorem flattenMatrix_transpose {ι κ α β R : Type*}
    (A : Matrix ι κ (Matrix α β R)) :
    (flattenMatrix A).transpose = flattenMatrix (Matrix.of fun i j => (A j i).transpose) := rfl

theorem flattenMatrix_trace {ι F R : Type*} [Fintype ι] [Fintype F]
    [AddCommMonoid R] (A : Matrix ι ι (Matrix F F R)) :
    (flattenMatrix A).trace = ∑ i, (A i i).trace := by
  simp [Matrix.trace, Fintype.sum_prod_type, flattenMatrix]

/-- The block regular-representation matrix attached to one line label. -/
def quotientMatrix {ι F R : Type*} [Group F] [Fintype F] [DecidableEq F]
    [Semiring R] (g : ι → ι → F) : Matrix (ι × F) (ι × F) R :=
    flattenMatrix (Matrix.of fun u v => regularMatrix (g u v))

theorem quotientMatrix_gram {ι F R : Type*} [Fintype ι] [Group F]
    [Fintype F] [DecidableEq F] [Semiring R] (g : ι → ι → F) :
    quotientMatrix (R := R) g * (quotientMatrix g).transpose =
      flattenMatrix (Matrix.of fun u u' => ∑ v, regularMatrix (g u v * (g u' v)⁻¹)) := by
  rw [quotientMatrix, flattenMatrix_transpose, ← flattenMatrix_mul]
  congr 1
  ext u u' a b
  simp [Matrix.of_apply, Matrix.mul_apply, Matrix.sum_apply, ← map_mul]

theorem quotientMatrix_gram_trace {ι F R : Type*} [Fintype ι] [Group F]
    [Fintype F] [DecidableEq F] [Semiring R] (g : ι → ι → F) :
    (quotientMatrix (R := R) g * (quotientMatrix g).transpose).trace =
      (Fintype.card ι : R) ^ 2 * Fintype.card F := by
  rw [quotientMatrix_gram, flattenMatrix_trace]
  simp only [Matrix.of_apply, mul_inv_cancel, map_one, Matrix.trace_sum]
  simp [pow_two, mul_assoc]

/-- The second trace expansion, before counting degenerate rectangles. -/
theorem quotientMatrix_gram_sq_trace {ι F R : Type*} [Fintype ι] [Group F]
    [Fintype F] [DecidableEq F] [Semiring R] (g : ι → ι → F) :
    ((quotientMatrix (R := R) g * (quotientMatrix g).transpose) *
      (quotientMatrix g * (quotientMatrix g).transpose)).trace =
        ∑ u, ∑ u', ∑ v, ∑ v', (regularMatrix (R := R)
          (g u v * (g u' v)⁻¹ * g u' v' * (g u v')⁻¹)).trace := by
  rw [quotientMatrix_gram, ← flattenMatrix_mul, flattenMatrix_trace]
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.sum_mul, Matrix.mul_sum, ← map_mul,
    Matrix.trace_sum, mul_assoc]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro u' _
  exact Finset.sum_comm

/-- Nondegenerate rectangular words survive in the finite group. -/
def RectanglesSurvive {ι F : Type*} [Group F] (g : ι → ι → F) : Prop :=
  ∀ u u' v v', u ≠ u' → v ≠ v' →
    g u v * (g u' v)⁻¹ * g u' v' * (g u v')⁻¹ ≠ 1

/-- The exact count `2r^3-r^2` of degenerate index choices. -/
theorem quotientMatrix_gram_sq_trace_of_rectangles {ι F R : Type*} [Fintype ι]
    [Group F] [Fintype F] [DecidableEq F] [CommRing R]
    (g : ι → ι → F) (hg : RectanglesSurvive g) :
    ((quotientMatrix (R := R) g * (quotientMatrix g).transpose) *
      (quotientMatrix g * (quotientMatrix g).transpose)).trace =
      (2 * (Fintype.card ι : R) ^ 3 - (Fintype.card ι : R) ^ 2) * Fintype.card F := by
  classical
  rw [quotientMatrix_gram_sq_trace]
  have ht (u u' v v' : ι) :
      (regularMatrix (R := R) (g u v * (g u' v)⁻¹ * g u' v' * (g u v')⁻¹)).trace =
      (if u = u' then (Fintype.card F : R) else 0) +
      (if v = v' then (Fintype.card F : R) else 0) -
      (if u = u' ∧ v = v' then (Fintype.card F : R) else 0) := by
    by_cases hu : u = u'
    · subst u'
      simp only [mul_inv_cancel, one_mul, regularMatrix_trace,
        true_and, add_sub_cancel_right]
    · by_cases hv : v = v'
      · subst v'
        simp [mul_assoc, hu]
      · simp only [regularMatrix_trace, ite_eq_right (hg u u' v v' hu hv), ite_eq_right hu,
          ite_eq_right hv, ite_eq_right (not_and.mpr (fun h => (hu h).elim)), add_zero, sub_zero]
  simp only [ht, Finset.sum_sub_distrib, Finset.sum_add_distrib, ite_and]
  simp [pow_succ, mul_assoc, sub_mul]
  ring

/-- Each integral row has exactly one unit entry per block column. -/
theorem quotientMatrix_row_sq {ι F : Type*} [Fintype ι] [Group F]
    [Fintype F] [DecidableEq F] (g : ι → ι → F) (i : ι × F) :
    ∑ j, ((quotientMatrix (R := ℤ) g i j : ℤ) : ℝ) ^ 2 = Fintype.card ι := by
  rw [Fintype.sum_prod_type]
  simp [quotientMatrix, flattenMatrix, Matrix.of_apply, ← inv_mul_eq_iff_eq_mul]

/-- Casting the integral matrix gives the corresponding coefficient representation. -/
theorem quotientMatrix_map {ι F R : Type*} [Group F] [Fintype F]
    [DecidableEq F] [Ring R] (g : ι → ι → F) :
    (quotientMatrix (R := ℤ) g).map (Int.cast : ℤ → R) = quotientMatrix (R := R) g := by
  ext i j
  simp [quotientMatrix, flattenMatrix]

theorem quotientMatrix_rank_real_lower {ι F : Type*} [Fintype ι] [Group F]
    [Fintype F] [DecidableEq F] (g : ι → ι → F) (hg : RectanglesSurvive g) :
    Fintype.card ι * Fintype.card F ≤ 2 * (quotientMatrix (R := ℝ) g).rank := by
  by_cases hzero : Fintype.card ι = 0
  · simp [hzero]
  let Y := quotientMatrix (R := ℝ) g
  have hA : (Y * Y.transpose).IsHermitian := by
    exact Matrix.isHermitian_mul_conjTranspose_self Y
  have hArank : (Y * Y.transpose).rank = Y.rank := by
    exact Matrix.rank_self_mul_conjTranspose Y
  have h := trace_sq_le_rank_mul_trace_sq (Y * Y.transpose) hA
  rw [hArank] at h
  change (quotientMatrix (R := ℝ) g * (quotientMatrix g).transpose).trace ^ 2 ≤ _ at h
  rw [quotientMatrix_gram_trace] at h
  change _ ≤ (Y.rank : ℝ) * ((quotientMatrix (R := ℝ) g * (quotientMatrix g).transpose) *
    (quotientMatrix g * (quotientMatrix g).transpose)).trace at h
  rw [quotientMatrix_gram_sq_trace_of_rectangles g hg] at h
  let r : ℝ := Fintype.card ι
  let D : ℝ := Fintype.card F
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast Nat.pos_of_ne_zero hzero
  have hD : 0 < D := by
    dsimp [D]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  have hk : 0 ≤ (Y.rank : ℝ) := Nat.cast_nonneg _
  have hcancel : (r ^ 3 * D) * (r * D) ≤ (r ^ 3 * D) * (2 * (Y.rank : ℝ)) := by
    calc
      _ = (r ^ 2 * D) ^ 2 := by ring
      _ ≤ (Y.rank : ℝ) * ((2 * r ^ 3 - r ^ 2) * D) := h
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hk (sq_nonneg r)) hD.le]
  have hf := (mul_le_mul_iff_right₀ (show 0 < r ^ 3 * D by positivity)).mp hcancel
  dsimp [r, D, Y] at hf
  exact_mod_cast hf

theorem quotientMatrix_rank_mod_lower {ι F : Type*} [Fintype ι] [Group F]
    [Fintype F] [DecidableEq F] (g : ι → ι → F) (hg : RectanglesSurvive g)
    (q : ℕ) [Fact q.Prime] (hq : Fintype.card ι < q) :
    Fintype.card ι * Fintype.card F ≤ 4 * (quotientMatrix (R := ZMod q) g).rank := by
  by_cases hzero : Fintype.card ι = 0
  · simp [hzero]
  have hr : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
  have hqr : (Fintype.card ι : ℝ) < q := by exact_mod_cast hq
  have hred := rank_reduction_half (quotientMatrix (R := ℤ) g) (Fintype.card ι) hr
    (fun i => (quotientMatrix_row_sq g i).le) q hqr
  rw [quotientMatrix_map, quotientMatrix_map] at hred
  have hreal := quotientMatrix_rank_real_lower g hg
  omega

/-- Block direct sum with the line-label index first. -/
def diagonalBlocks {I ι κ K : Type*} [DecidableEq I] [Zero K]
    (Y : I → Matrix ι κ K) : Matrix (I × ι) (I × κ) K :=
    Matrix.of fun x y => if x.1 = y.1 then Y x.1 x.2 y.2 else 0

/-- The lower rank bound for a direct sum, proved by its full-rank block minors. -/
theorem sum_rank_le_rank_diagonalBlocks {I ι κ K : Type*} [Fintype I]
    [Fintype ι] [Fintype κ] [DecidableEq I] [Field K]
    (Y : I → Matrix ι κ K) : (∑ i, (Y i).rank) ≤ (diagonalBlocks Y).rank := by
  classical
  choose f g hf hg hdet using fun i => exists_full_rank_minor (Y i)
  let B : ∀ i, Matrix (Fin (Y i).rank) (Fin (Y i).rank) K :=
    fun i => (Y i).submatrix (f i) (g i)
  let rows : (Σ i, Fin (Y i).rank) → I × ι := fun x => (x.1, f x.1 x.2)
  let cols : (Σ i, Fin (Y i).rank) → I × κ := fun x => (x.1, g x.1 x.2)
  have hminor : (diagonalBlocks Y).submatrix rows cols = Matrix.blockDiagonal' B := by
    ext ⟨i,a⟩ ⟨j,b⟩
    by_cases hij : i = j
    · subst j
      simp [diagonalBlocks, rows, cols, B]
    · simp [diagonalBlocks, rows, cols, Matrix.blockDiagonal'_apply_ne _ _ _ hij, hij]
  have hBunit : IsUnit B := Pi.isUnit_iff.mpr (fun i =>
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hdet i)))
  have hunit : IsUnit (Matrix.blockDiagonal' B) :=
    hBunit.map (Matrix.blockDiagonal'RingHom (fun i => Fin (Y i).rank) K)
  have hrank := Matrix.rank_of_isUnit (Matrix.blockDiagonal' B) hunit
  calc
    (∑ i, (Y i).rank) = Fintype.card (Σ i, Fin (Y i).rank) := by simp
    _ = (Matrix.blockDiagonal' B).rank := hrank.symm
    _ ≤ (diagonalBlocks Y).rank := by
      rw [← hminor]
      exact Matrix.rank_submatrix_le _ _ _

theorem rank_neg {ι κ K : Type*} [Fintype ι] [Fintype κ] [Field K]
    (A : Matrix ι κ K) : (-A).rank = A.rank := by
  simpa using Matrix.rank_smul_of_mem_nonZeroDivisors A
    (mem_nonZeroDivisors_of_ne_zero (show (-1 : K) ≠ 0 by simp))

/-- The rank-one scalar matrix `f fᵀ` tensored with a matrix. -/
def weightedMatrix {I ι κ K : Type*} [Mul K] (f : I → K) (Z : Matrix ι κ K) :
    Matrix (I × ι) (I × κ) K := Matrix.of fun x y => f x.1 * f y.1 * Z x.2 y.2

/-- A rank-one tensor weight never increases rank. -/
theorem weightedMatrix_rank_le {I ι κ K : Type*} [Fintype I] [Fintype ι]
    [Fintype κ] [Field K] (f : I → K) (Z : Matrix ι κ K) :
    (weightedMatrix f Z).rank ≤ Z.rank := by
  classical
  let L : Matrix (I × ι) ι K := Matrix.of fun x a => if x.2 = a then f x.1 else 0
  let R : Matrix κ (I × κ) K := Matrix.of fun b y => if b = y.2 then f y.1 else 0
  have hfactor : weightedMatrix f Z = L * Z * R := by
    ext ⟨i,a⟩ ⟨j,b⟩
    simp [weightedMatrix, L, R, Matrix.mul_apply, mul_ite, ite_mul]
    ring
  rw [hfactor]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- Exchanging the incidence sums turns the punctured-line certificate into a
block-diagonal matrix identity. The coefficient order in each matrix is unchanged. -/
theorem tensor_certificate {P I ι κ K : Type*} [Fintype P] [Fintype I]
    [DecidableEq I] [Field K] (inc : P → Finset I) (f : P → I → K)
    (Y : I → Matrix ι κ K)
    (hline : ∀ i j k, (∑ z, if i ∈ inc z then f z j * f z k else 0) =
      -(if j = i ∧ k = i then 1 else 0)) :
    (∑ z, weightedMatrix (f z) (∑ i ∈ inc z, Y i)) = -diagonalBlocks Y := by
  classical
  ext ⟨j,a⟩ ⟨k,b⟩
  simp only [Matrix.sum_apply, weightedMatrix, Matrix.of_apply, Matrix.neg_apply,
    diagonalBlocks]
  simp only [Finset.mul_sum]
  have hsum (z : P) : (∑ i ∈ inc z, f z j * f z k * Y i a b) =
      ∑ i, (if i ∈ inc z then f z j * f z k else 0) * Y i a b := by
    simp [ite_mul]
  simp_rw [hsum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hline, neg_mul, ite_mul, one_mul, zero_mul]
  by_cases hjk : j = k
  · subst k
    simp
  · simp [hjk, show ∀ i, ¬(j = i ∧ k = i) by rintro i ⟨rfl,rfl⟩; exact hjk rfl]

theorem rank_budget_of_line_certificate {P I ι κ K : Type*} [Fintype P]
    [Fintype I] [Fintype ι] [Fintype κ] [DecidableEq I] [Field K]
    (inc : P → Finset I) (f : P → I → K) (Y : I → Matrix ι κ K)
    (hline : ∀ i j k, (∑ z, if i ∈ inc z then f z j * f z k else 0) =
      -(if j = i ∧ k = i then 1 else 0)) :
    (∑ i, (Y i).rank) ≤ ∑ z, (∑ i ∈ inc z, Y i).rank := by
  calc
    _ ≤ (diagonalBlocks Y).rank := sum_rank_le_rank_diagonalBlocks Y
    _ = (-diagonalBlocks Y).rank := (rank_neg _).symm
    _ = (∑ z, weightedMatrix (f z) (∑ i ∈ inc z, Y i)).rank := by
      rw [tensor_certificate inc f Y hline]
    _ ≤ ∑ z, (weightedMatrix (f z) (∑ i ∈ inc z, Y i)).rank := rank_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun z _ => weightedMatrix_rank_le _ _)

/-- A local Cartesian block factors through one copy of the finite regular module. -/
theorem quotientMatrix_sum_rank_le {ι s t F K : Type*} [Fintype ι]
    [Fintype s] [Fintype t] [Group F] [Fintype F] [DecidableEq F] [Field K]
    (L : ι → s → F) (R : ι → t → F) :
    (∑ j : s, ∑ k : t, quotientMatrix (R := K) (fun u v => (L u j)⁻¹ * R v k)).rank ≤
      Fintype.card F := by
  classical
  let A : Matrix (ι × F) F K := Matrix.of fun x a =>
    (∑ j, regularMatrix (R := K) (L x.1 j)⁻¹) x.2 a
  let B : Matrix F (ι × F) K := Matrix.of fun b y =>
    (∑ k, regularMatrix (R := K) (R y.1 k)) b y.2
  have hfactor :
      (∑ j : s, ∑ k : t, quotientMatrix (R := K) (fun u v => (L u j)⁻¹ * R v k)) =
      A * B := by
    ext ⟨u,a⟩ ⟨v,b⟩
    simp only [Matrix.sum_apply, quotientMatrix, flattenMatrix_apply, Matrix.of_apply,
      map_mul, Matrix.mul_apply, A, B]
    simp only [Finset.sum_mul, Finset.mul_sum]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset t))
      (t := (Finset.univ : Finset F))]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact Finset.sum_comm
  rw [hfactor]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

/-- An arbitrary relabeling of a Cartesian block does not affect its summed
regular-representation matrix. Opposite-index shifts are permitted independently. -/
theorem quotientMatrix_sum_reindex {ι B s t F K : Type*} [Fintype B]
    [Fintype s] [Fintype t] [Group F] [Fintype F] [DecidableEq F] [Semiring K]
    (g : B → ι → ι → F) (L : ι → s → F) (R : ι → t → F)
    (e : ι → ι → B ≃ s × t)
    (h : ∀ i u v, g i u v = (L u (e u v i).1)⁻¹ * R v (e u v i).2) :
    (∑ i, quotientMatrix (R := K) (g i)) =
      ∑ j : s, ∑ k : t, quotientMatrix (R := K) (fun u v => (L u j)⁻¹ * R v k) := by
  ext ⟨u,a⟩ ⟨v,b⟩
  simp only [Matrix.sum_apply, quotientMatrix, flattenMatrix_apply, Matrix.of_apply, h]
  exact (Equiv.sum_comp (e u v) (fun p : s × t =>
    (regularMatrix (R := K) ((L u p.1)⁻¹ * R v p.2)) a b)).trans
      (Fintype.sum_prod_type _)

/-- A polynomial below the finite-field power-sum threshold has zero total sum. -/
theorem polynomial_sum_eq_zero {K : Type*} [Field K] [Fintype K]
    (p : Polynomial K) (hdeg : p.natDegree < Fintype.card K - 1) :
    ∑ x, p.eval x = 0 := by
  simp only [Polynomial.eval_eq_sum_range]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i hi
  rw [← Finset.mul_sum, FiniteField.sum_pow_lt_card_sub_one K i
    (lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hdeg), mul_zero]

def gridLagrange {T K : Type*} [Fintype T] [Field K] [DecidableEq K]
    (S : Finset K) (a x : T → K) : K :=
    ∏ t, ∏ w ∈ S.erase (a t), (x t - w) / (a t - w)

@[simp] theorem gridLagrange_self {T K : Type*} [Fintype T] [Field K]
    [DecidableEq K] (S : Finset K) (a : T → K) : gridLagrange S a a = 1 := by
  apply Finset.prod_eq_one
  intro t _
  apply Finset.prod_eq_one
  intro w hw
  exact div_self (sub_ne_zero.mpr (Finset.mem_erase.mp hw).1.symm)

theorem gridLagrange_other {T K : Type*} [Fintype T] [Field K]
    [DecidableEq K] (S : Finset K) (a x : T → K) (hx : ∀ t, x t ∈ S)
    (hax : a ≠ x) : gridLagrange S a x = 0 := by
  classical
  obtain ⟨t, ht⟩ := Function.ne_iff.mp hax
  apply Finset.prod_eq_zero (Finset.mem_univ t)
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨ht.symm, hx t⟩)
  simp

/-- Restriction of the grid Lagrange basis along the parametrized affine line. -/
noncomputable def gridLagrangeLine {T K : Type*} [Fintype T] [Field K] [DecidableEq K]
    (S : Finset K) (a b v : T → K) : Polynomial K :=
    ∏ t, ∏ w ∈ S.erase (a t),
      (Polynomial.C (b t - w) + Polynomial.X * Polynomial.C (v t)) *
        Polynomial.C ((a t - w)⁻¹)

@[simp] theorem gridLagrangeLine_eval {T K : Type*} [Fintype T] [Field K]
    [DecidableEq K] (S : Finset K) (a b v : T → K) (x : K) :
    (gridLagrangeLine S a b v).eval x = gridLagrange S a (fun t => b t + x * v t) := by
  simp only [gridLagrangeLine, gridLagrange, Polynomial.eval_prod,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
    div_eq_mul_inv]
  apply Finset.prod_congr rfl
  intro t _
  apply Finset.prod_congr rfl
  intro w _
  ring

theorem gridLagrangeLine_natDegree_le {T K : Type*} [Fintype T] [Field K]
    [DecidableEq K] (S : Finset K) (a b v : T → K) (ha : ∀ t, a t ∈ S) :
    (gridLagrangeLine S a b v).natDegree ≤ Fintype.card T * (S.card - 1) := by
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ t : T, (S.card - 1) := by
      apply Finset.sum_le_sum
      intro t _
      apply (Polynomial.natDegree_prod_le _ _).trans
      calc
        _ ≤ ∑ _w ∈ S.erase (a t), 1 := by
          apply Finset.sum_le_sum
          intro w _
          apply Polynomial.natDegree_mul_le.trans
          simp only [Polynomial.natDegree_C, add_zero]
          apply (Polynomial.natDegree_add_le _ _).trans
          apply max_le
          · simp
          · exact Polynomial.natDegree_mul_le.trans (by simp)
        _ = S.card - 1 := by simp [Finset.card_erase_of_mem (ha t)]
    _ = _ := by simp

/-- Every entry of the rank-one weight matrix has zero sum over a full line. -/
theorem polygon_weight_line_sum {T K : Type*} [Fintype T] [Field K] [Fintype K]
    [DecidableEq K] (S : Finset K) (a a' b v : T → K)
    (ha : ∀ t, a t ∈ S) (ha' : ∀ t, a' t ∈ S)
    (hdeg : 2 * (Fintype.card T * (S.card - 1)) < Fintype.card K - 1) :
    (∑ x : K, gridLagrange S a (fun t => b t + x * v t) *
      gridLagrange S a' (fun t => b t + x * v t)) = 0 := by
  have h := polynomial_sum_eq_zero (gridLagrangeLine S a b v * gridLagrangeLine S a' b v)
    (lt_of_le_of_lt (Polynomial.natDegree_mul_le.trans (Nat.add_le_add
      (gridLagrangeLine_natDegree_le S a b v ha)
      (gridLagrangeLine_natDegree_le S a' b v ha'))) (by omega))
  simpa only [Polynomial.eval_mul, gridLagrangeLine_eval] using h

/-- Finite separating families can be combined into one finite target. -/
theorem exists_finite_separating_family {G : Type u} {ι : Type v} [Group G] [Fintype ι]
    [Group.ResiduallyFinite G] (w : ι → G) (hw : ∀ i, w i ≠ 1) :
    ∃ (Q : Type (max u v)) (_ : Group Q) (_ : Fintype Q) (φ : G →* Q), ∀ i, φ (w i) ≠ 1 := by
  classical
  choose H hH using fun i => Group.exists_finiteIndexNormalSubgroup_notMem (w i) (hw i)
  let Q := ∀ i, G ⧸ (H i).toSubgroup
  let : ∀ i, Fintype (G ⧸ (H i).toSubgroup) := fun i => Fintype.ofFinite _
  let φ : G →* Q := MonoidHom.pi (fun i => QuotientGroup.mk' (H i).toSubgroup)
  refine ⟨Q, inferInstance, inferInstance, φ, ?_⟩
  intro i hi
  have h := congrFun hi i
  exact hH i ((QuotientGroup.eq_one_iff (w i)).mp h)

/-- Standard affine parametrization, with the marked point at parameter zero. -/
def affineLineMap {T K : Type*} [Field K] (a v : T → K) (x : K) : T → K :=
  fun t => a t + x * v t

theorem affineLineMap_injective {T K : Type*} [Field K] (a v : T → K)
    (hv : v ≠ 0) : Function.Injective (affineLineMap a v) := by
  classical
  obtain ⟨t, ht⟩ := Function.ne_iff.mp hv
  intro x y hxy
  have h := congrFun hxy t
  exact mul_right_cancel₀ ht (add_left_cancel h)

/-- The geometric affine line punctured only at its own marked point. -/
noncomputable def puncturedLine {T K : Type*} [Fintype T] [Field K] [Fintype K]
    (a v : T → K) : Finset (T → K) := by
  classical
  exact (Finset.univ.erase 0).image (affineLineMap a v)

/-- Summation on a punctured line subtracts exactly the value at its own mark. -/
theorem puncturedLine_sum {T K R : Type*} [Fintype T] [Field K] [Fintype K]
    [AddCommGroup R] (a v : T → K) (hv : v ≠ 0) (w : (T → K) → R) :
    (∑ z ∈ puncturedLine a v, w z) = (∑ x, w (affineLineMap a v x)) - w a := by
  classical
  have hzero : affineLineMap a v 0 = a := by ext t; simp [affineLineMap]
  rw [puncturedLine, Finset.sum_image (affineLineMap_injective a v hv).injOn,
    Finset.sum_erase_eq_sub (Finset.mem_univ 0), hzero]

noncomputable def lineIncidence {T I K : Type*} [Fintype T] [Fintype I]
    [Field K] [Fintype K] (a v : I → T → K) (z : T → K) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => z ∈ puncturedLine (a i) (v i))

/-- The exact finite-field punctured-line matrix certificate, with no asymptotic
or characteristic assumption beyond its explicit degree threshold. -/
theorem grid_line_certificate {T I K : Type*} [Fintype T] [Fintype I]
    [DecidableEq T] [DecidableEq I] [Field K] [Fintype K] [DecidableEq K]
    (S : Finset K) (a v : I → T → K) (ha : ∀ i t, a i t ∈ S)
    (hinj : Function.Injective a) (hv : ∀ i, v i ≠ 0)
    (hdeg : 2 * (Fintype.card T * (S.card - 1)) < Fintype.card K - 1) :
    ∀ i j k, (∑ z, if i ∈ lineIncidence a v z then
      gridLagrange S (a j) z * gridLagrange S (a k) z else 0) =
      -(if j = i ∧ k = i then 1 else 0) := by
  classical
  intro i j k
  have heval (j : I) : gridLagrange S (a j) (a i) = if j = i then 1 else 0 := by
    by_cases hji : j = i
    · subst j; simp
    · rw [ite_eq_right hji]
      exact gridLagrange_other S (a j) (a i) (ha i) (fun h => hji (hinj h))
  have hs : (∑ z, if i ∈ lineIncidence a v z then
      gridLagrange S (a j) z * gridLagrange S (a k) z else 0) =
      ∑ z ∈ puncturedLine (a i) (v i), gridLagrange S (a j) z * gridLagrange S (a k) z := by
    simp [lineIncidence]
  rw [hs, puncturedLine_sum (a i) (v i) (hv i)]
  rw [show (∑ x, gridLagrange S (a j) (affineLineMap (a i) (v i) x) *
    gridLagrange S (a k) (affineLineMap (a i) (v i) x)) = 0 from
      polygon_weight_line_sum S (a j) (a k) (a i) (v i) (ha j) (ha k) hdeg]
  by_cases hj : j = i <;> by_cases hk : k = i <;> simp_all

theorem two_block_sizes (r d : ℕ) (hr : 0 < r) (hd : 4 * r ^ 2 ≤ d) :
    ∃ n₁ n₂ : ℕ, r ≤ n₁ ∧ r ≤ n₂ ∧ n₂ < 2 * r ∧
      d = r * n₁ + (r + 1) * n₂ := by
  have hmod : d % r < r := Nat.mod_lt d hr
  have hquot : 4 * r ≤ d / r := (Nat.le_div_iff_mul_le hr).mpr (by nlinarith)
  have hsub : r + 1 + d % r ≤ d / r := by omega
  refine ⟨d / r - (r + 1 + d % r), r + d % r, by omega, by omega, by omega, ?_⟩
  have hdecomp := Nat.div_add_mod d r
  have hdiff := Nat.sub_add_cancel hsub
  nlinarith

structure CartesianBlock (I : Type*) (r : ℕ) where
  s : ℕ
  t : ℕ
  hs : r ≤ s
  ht : r ≤ t
  spos : 0 < s
  tpos : 0 < t
  labels : Finset I
  coordinates : labels ≃ ZMod s × ZMod t

instance {I : Type*} {r : ℕ} (b : CartesianBlock I r) : NeZero b.s := ⟨b.spos.ne'⟩
instance {I : Type*} {r : ℕ} (b : CartesianBlock I r) : NeZero b.t := ⟨b.tpos.ne'⟩

/-- Opposite-index shifts are bijections of the block coordinates. -/
def CartesianBlock.shifted {I : Type*} {r : ℕ} (b : CartesianBlock I r)
    (u v : Fin r) : b.labels ≃ ZMod b.s × ZMod b.t :=
  b.coordinates.trans (Equiv.prodCongr (Equiv.addRight (v.val : ZMod b.s))
    (Equiv.addRight (u.val : ZMod b.t)))

theorem CartesianBlock.quotient_rank_le {I F K : Type*} {r : ℕ}
    [Group F] [Fintype F] [DecidableEq F] [Field K]
    (b : CartesianBlock I r) (g : I → Fin r → Fin r → F)
    (L : Fin r → ZMod b.s → F) (R : Fin r → ZMod b.t → F)
    (hrel : ∀ (i : b.labels) u v,
      g i u v = (L u ((b.coordinates i).1 + (v.val : ZMod b.s)))⁻¹ *
        R v ((b.coordinates i).2 + (u.val : ZMod b.t))) :
    (∑ i ∈ b.labels, quotientMatrix (R := K) (g i)).rank ≤ Fintype.card F := by
  classical
  rw [Finset.sum_subtype b.labels (fun _ => Iff.rfl)]
  rw [quotientMatrix_sum_reindex (fun i : b.labels => g i) L R b.shifted hrel]
  exact quotientMatrix_sum_rank_le L R

/-- Every sufficiently large finite set has the two Cartesian blocks required by
the construction; the coordinate bijections are chosen without deleting labels. -/
theorem exists_two_cartesian_blocks {I : Type*} [DecidableEq I] (r : ℕ) (hr : 0 < r)
    (A : Finset I) (hA : 4 * r ^ 2 ≤ A.card) :
    ∃ b₀ b₁ : CartesianBlock I r,
      Disjoint b₀.labels b₁.labels ∧ b₀.labels ∪ b₁.labels = A := by
  classical
  obtain ⟨n₁,n₂,hn₁,hn₂,_,heq⟩ := two_block_sizes r A.card hr hA
  obtain ⟨A₀,hA₀,hcard⟩ := Finset.exists_subset_card_eq (show r * n₁ ≤ A.card by omega)
  let A₁ := A \ A₀
  have hcard₁ : A₁.card = (r + 1) * n₂ := by rw [Finset.card_sdiff_of_subset hA₀, hcard, heq]; omega
  let : NeZero r := ⟨hr.ne'⟩
  let : NeZero n₁ := ⟨(hr.trans_le hn₁).ne'⟩
  let : NeZero n₂ := ⟨(hr.trans_le hn₂).ne'⟩
  let b₀ : CartesianBlock I r :=
    {s := r, t := n₁, hs := le_rfl, ht := hn₁, spos := hr, tpos := hr.trans_le hn₁,
     labels := A₀, coordinates := Fintype.equivOfCardEq (by simpa using hcard)}
  let b₁ : CartesianBlock I r :=
    {s := r+1, t := n₂, hs := Nat.le_succ r, ht := hn₂, spos := Nat.succ_pos r,
     tpos := hr.trans_le hn₂,
     labels := A₁, coordinates := Fintype.equivOfCardEq (by simpa using hcard₁)}
  refine ⟨b₀,b₁,?_,?_⟩
  · exact Finset.disjoint_sdiff
  · exact Finset.union_sdiff_of_subset hA₀

/-- The numerical rank contradiction. The exceptional incidences are retained;
the ambient dimension, not a deletion, bounds their matrices. -/
theorem finite_quotient_rank_obstruction {P I F : Type*} [Fintype P] [Fintype I]
    [DecidableEq I] [Group F] [Fintype F] [DecidableEq F]
    (r q : ℕ) [Fact q.Prime] (hq : r < q)
    (inc : P → Finset I) (f : P → I → ZMod q) (E : Finset P)
    (g : I → Fin r → Fin r → F) (hg : ∀ i, RectanglesSurvive (g i))
    (hline : ∀ i j k, (∑ z, if i ∈ inc z then f z j * f z k else 0) =
      -(if j = i ∧ k = i then 1 else 0))
    (hlocal : ∀ z, z ∉ E → (∑ i ∈ inc z, quotientMatrix (R := ZMod q) (g i)).rank ≤
      2 * Fintype.card F)
    (hbudget : 4 * (2 * Fintype.card P + r * E.card) < Fintype.card I * r) : False := by
  classical
  let D := Fintype.card F
  let Y := fun i => quotientMatrix (R := ZMod q) (g i)
  let Z := fun z => ∑ i ∈ inc z, Y i
  have lower : Fintype.card I * r * D ≤ 4 * ∑ i, (Y i).rank := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
      quotientMatrix_rank_mod_lower (g i) (hg i) q (by simpa using hq))
    simpa [Y, D, ← Finset.mul_sum, mul_assoc] using h
  have middle : (∑ i, (Y i).rank) ≤ ∑ z, (Z z).rank :=
    rank_budget_of_line_certificate inc f Y hline
  have upper : (∑ z, (Z z).rank) ≤ (2 * Fintype.card P + r * E.card) * D := by
    have hbound (z : P) : (Z z).rank ≤ 2 * D + if z ∈ E then r * D else 0 := by
      by_cases hz : z ∈ E
      · rw [ite_eq_left hz]
        have hrank : (Z z).rank ≤ r * D := by
          simpa [D] using Matrix.rank_le_card_height (Z z)
        omega
      · rw [ite_eq_right hz, add_zero]
        exact hlocal z hz
    calc
      _ ≤ ∑ z, (2 * D + if z ∈ E then r * D else 0) := Finset.sum_le_sum (fun z _ => hbound z)
      _ = _ := by simp [Finset.sum_add_distrib, add_mul]; ring
  have hc : Fintype.card I * r * D ≤ (4 * (2 * Fintype.card P + r * E.card)) * D := by
    calc
      _ ≤ 4 * ∑ i, (Y i).rank := lower
      _ ≤ 4 * ∑ z, (Z z).rank := Nat.mul_le_mul_left _ middle
      _ ≤ 4 * ((2 * Fintype.card P + r * E.card) * D) := Nat.mul_le_mul_left _ upper
      _ = _ := by ring
  exact (Nat.not_le_of_gt (Nat.mul_lt_mul_of_pos_right hbudget
    (Fintype.card_pos : 0 < D))) hc

/-- The exact defining relation of a single block, retaining the order `L⁻¹R`. -/
def CartesianBlock.Relations {I G : Type*} [Group G] {r : ℕ}
    (b : CartesianBlock I r) (g : I → Fin r → Fin r → G) : Prop :=
    ∃ (L : Fin r → ZMod b.s → G) (R : Fin r → ZMod b.t → G),
      ∀ (i : b.labels) u v, g i u v =
        (L u ((b.coordinates i).1 + (v.val : ZMod b.s)))⁻¹ *
         R v ((b.coordinates i).2 + (u.val : ZMod b.t))

theorem CartesianBlock.Relations.map {I G F : Type*} [Group G] [Group F] {r : ℕ}
    {b : CartesianBlock I r} {g : I → Fin r → Fin r → G}
    (h : b.Relations g) (φ : G →* F) : b.Relations (fun i u v => φ (g i u v)) := by
  obtain ⟨L,R,hrel⟩ := h
  refine ⟨fun u j => φ (L u j), fun v k => φ (R v k), ?_⟩
  intros
  simp [hrel]

theorem two_block_quotient_rank_le {I F K : Type*} [DecidableEq I]
    [Group F] [Fintype F] [DecidableEq F] [Field K] {r : ℕ}
    (A : Finset I) (g : I → Fin r → Fin r → F)
    (b₀ b₁ : CartesianBlock I r)
    (hdis : Disjoint b₀.labels b₁.labels) (hunion : b₀.labels ∪ b₁.labels = A)
    (h₀ : b₀.Relations g) (h₁ : b₁.Relations g) :
    (∑ i ∈ A, quotientMatrix (R := K) (g i)).rank ≤ 2 * Fintype.card F := by
  obtain ⟨L₀,R₀,h₀⟩ := h₀
  obtain ⟨L₁,R₁,h₁⟩ := h₁
  rw [← hunion, Finset.sum_union hdis]
  have h := (rank_add_le _ _).trans (Nat.add_le_add
    (b₀.quotient_rank_le (K := K) g L₀ R₀ h₀)
    (b₁.quotient_rank_le (K := K) g L₁ R₁ h₁))
  simpa [two_mul] using h

/-- All specified nontrivial rectangular words can be preserved in one finite
image if the group is residually finite. -/
theorem exists_finite_preserving_rectangles {I : Type u} {G : Type v} [Fintype I] [Group G]
    [Group.ResiduallyFinite G] {r : ℕ} (g : I → Fin r → Fin r → G)
    (hg : ∀ i, RectanglesSurvive (g i)) :
    ∃ (Q : Type (max u v)) (_ : Group Q) (_ : Fintype Q) (φ : G →* Q),
      ∀ i, RectanglesSurvive (fun u v => φ (g i u v)) := by
  classical
  let J := {x : I × Fin r × Fin r × Fin r × Fin r // x.2.1 ≠ x.2.2.1 ∧ x.2.2.2.1 ≠ x.2.2.2.2}
  let w : J → G := fun x => g x.val.1 x.val.2.1 x.val.2.2.2.1 *
    (g x.val.1 x.val.2.2.1 x.val.2.2.2.1)⁻¹ *
    g x.val.1 x.val.2.2.1 x.val.2.2.2.2 * (g x.val.1 x.val.2.1 x.val.2.2.2.2)⁻¹
  have hw (x : J) : w x ≠ 1 := hg _ _ _ _ _ x.property.1 x.property.2
  obtain ⟨Q,hQ,hfin,φ,hφ⟩ := exists_finite_separating_family w hw
  refine ⟨Q,hQ,hfin,φ,?_⟩
  intro i u u' v v' hu hv
  have h := hφ ⟨(i,u,u',v,v'),hu,hv⟩
  simpa [w] using h

theorem not_residuallyFinite_of_line_blocks {T I G : Type*}
    [Fintype T] [Fintype I] [DecidableEq T] [DecidableEq I] [Group G]
    (r q : ℕ) [Fact q.Prime] (hq : r < q)
    (S : Finset (ZMod q)) (a v : I → T → ZMod q)
    (ha : ∀ i t, a i t ∈ S) (hinj : Function.Injective a) (hv : ∀ i, v i ≠ 0)
    (hdeg : 2 * (Fintype.card T * (S.card - 1)) < q - 1)
    (E : Finset (T → ZMod q)) (g : I → Fin r → Fin r → G)
    (hg : ∀ i, RectanglesSurvive (g i))
    (hblocks : ∀ z, z ∉ E → ∃ b₀ b₁ : CartesianBlock I r,
      Disjoint b₀.labels b₁.labels ∧ b₀.labels ∪ b₁.labels = lineIncidence a v z ∧
      b₀.Relations g ∧ b₁.Relations g)
    (hbudget : 4 * (2 * Fintype.card (T → ZMod q) + r * E.card) < Fintype.card I * r) :
    ¬ Group.ResiduallyFinite G := by
  classical
  intro hRF
  let := hRF
  obtain ⟨Q,hQ,hfin,φ,hφ⟩ := exists_finite_preserving_rectangles g hg
  let := hQ
  let := hfin
  apply finite_quotient_rank_obstruction r q hq (lineIncidence a v)
    (fun z i => gridLagrange S (a i) z) E (fun i u v => φ (g i u v)) hφ
    (grid_line_certificate S a v ha hinj hv (by simpa using hdeg)) _ hbudget
  intro z hz
  obtain ⟨b₀,b₁,hd,hu,h₀,h₁⟩ := hblocks z hz
  exact two_block_quotient_rank_le _ _ b₀ b₁ hd hu (h₀.map φ) (h₁.map φ)

end Release075

end OAI
