import OAI.Algebra.Determinantal.ConductorLocalization

namespace OAI

namespace PermanentBorder.AdjugateAlgebra
open Matrix Polynomial

section Commutator
variable {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]

theorem trace_commutator_adjugate (M Y : Matrix ι ι K) :
    ((M * Y - Y * M) * M.adjugate).trace = 0 := by
  rw [sub_mul, Matrix.trace_sub, Matrix.trace_mul_cycle M Y M.adjugate,
    Matrix.adjugate_mul, Matrix.mul_assoc Y M M.adjugate, Matrix.mul_adjugate]
  simp

theorem trace_commutator_adjugate_scalar (A Y : Matrix ι ι K) (s : K) :
    ((A * Y - Y * A) * (s • (1 : Matrix ι ι K) + A).adjugate).trace = 0 := by
  have he : (s • (1 : Matrix ι ι K) + A) * Y - Y * (s • 1 + A) =
      A * Y - Y * A := by
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
    abel
  rw [← he]
  exact trace_commutator_adjugate _ _

end Commutator

section DiagonalCommutator
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem exists_diagonal_commutator (θ : ι → K) (hθ : Function.Injective θ)
    (Y : Matrix ι ι K) (hY : ∀ i, Y i i = 0) :
    ∃ Z : Matrix ι ι K, Matrix.diagonal θ * Z - Z * Matrix.diagonal θ = Y := by
  let Z : Matrix ι ι K := fun i j => Y i j / (θ i - θ j)
  refine ⟨Z, ?_⟩
  ext i j
  simp only [Matrix.sub_apply]
  rw [Matrix.diagonal_mul θ Z i j, Matrix.mul_diagonal θ Z i j]
  dsimp only [Z]
  by_cases hij : i = j
  · subst j
    simp [hY]
  · have hne : θ i - θ j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hθ h))
    field_simp
end DiagonalCommutator

section PolynomialAdjugate
variable {R : Type*} [CommRing R] {k : ℕ}

theorem natDegree_adjugate_linear_le
    (A B : Matrix (Fin (k+1)) (Fin (k+1)) R) (i j : Fin (k+1)) :
    (((X : R[X]) • A.map C + B.map C).adjugate i j).natDegree ≤ k := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  have hsub : ((X : R[X]) • A.map C + B.map C).submatrix j.succAbove i.succAbove =
      (X : R[X]) • (A.submatrix j.succAbove i.succAbove).map C +
        (B.submatrix j.succAbove i.succAbove).map C := by ext; rfl
  rw [hsub]
  calc
    _ ≤ ((-1 : R[X]) ^ (↑j + ↑i)).natDegree +
        ((X : R[X]) • (A.submatrix j.succAbove i.succAbove).map C +
        (B.submatrix j.succAbove i.succAbove).map C).det.natDegree := natDegree_mul_le
    _ ≤ 0 + k := by
      gcongr
      · rw [show (-1 : R[X]) ^ (↑j + ↑i) = C ((-1 : R) ^ (↑j + ↑i)) by simp]
        simp only [natDegree_C, le_refl]
      · simpa using natDegree_det_X_add_C_le
          (A.submatrix j.succAbove i.succAbove) (B.submatrix j.succAbove i.succAbove)
    _ = k := zero_add _

theorem coeff_adjugate_linear
    (A B : Matrix (Fin (k+1)) (Fin (k+1)) R) (i j : Fin (k+1)) :
    (((X : R[X]) • A.map C + B.map C).adjugate i j).coeff k = A.adjugate i j := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix,
    Matrix.adjugate_fin_succ_eq_det_submatrix]
  have hsub : ((X : R[X]) • A.map C + B.map C).submatrix j.succAbove i.succAbove =
      (X : R[X]) • (A.submatrix j.succAbove i.succAbove).map C +
        (B.submatrix j.succAbove i.succAbove).map C := by ext; rfl
  rw [hsub, show (-1 : R[X]) ^ (↑j + ↑i) = C ((-1 : R) ^ (↑j + ↑i)) by simp]
  rw [coeff_C_mul]
  congr 1
  simpa using coeff_det_X_add_C_card
    (A.submatrix j.succAbove i.succAbove) (B.submatrix j.succAbove i.succAbove)

end PolynomialAdjugate

section Slope
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

noncomputable def spectralSlope (θ : ι → K) : Matrix ι ι K[X] :=
  Matrix.diagonal (fun i => X + C (θ i))

theorem diagonal_zero_of_trace_slope (θ : ι → K) (hθ : Function.Injective θ)
    (Y : Matrix ι ι K)
    (h : (Y.map C * (spectralSlope θ).adjugate).trace = 0) : ∀ i, Y i i = 0 := by
  intro i
  have he := congrArg (Polynomial.eval (-θ i)) h
  simp only [spectralSlope, Matrix.adjugate_diagonal, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_diagonal, Matrix.map_apply,
    eval_finsetSum, eval_mul, eval_C, eval_prod, eval_add, eval_X, eval_zero] at he
  have heq : (∑ j : ι, Y j j * ∏ l ∈ Finset.univ.erase j, (-θ i + θ l)) =
      Y i i * ∏ l ∈ Finset.univ.erase i, (-θ i + θ l) := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      have hf : (∏ l ∈ Finset.univ.erase j, (-θ i + θ l)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hji, Finset.mem_univ i⟩)
        simp
      simp [hf]
    · simp
  rw [heq] at he
  have hp : (∏ l ∈ Finset.univ.erase i, (-θ i + θ l)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hji := Finset.ne_of_mem_erase hj
    intro hz
    apply hji
    apply hθ
    exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg, add_comm] using hz)
  exact (mul_eq_zero.mp he).resolve_right hp

end Slope

section Scaling
variable {K : Type*} [Field K] {k : ℕ}

noncomputable def pencilBase (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) :
    Matrix (Fin (k+1)) (Fin (k+1)) K[X] :=
  (X : K[X]) • (Matrix.diagonal θ).map C + A.map C

noncomputable def scaledPencil (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) :
    Matrix (Fin (k+1)) (Fin (k+1)) K[X][X] :=
  (X : K[X][X]) • (spectralSlope θ).map C + (A.map C).map C

noncomputable def liftCoefficients : K[X] →+* K[X][X] := Polynomial.mapRingHom C

noncomputable def scaledTrace (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K)
    (Y : Matrix (Fin (k+1)) (Fin (k+1)) K[X]) : K[X][X] :=
  (Y.map liftCoefficients * (scaledPencil θ A).adjugate).trace

 theorem scaledPencil_eq (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) :
    scaledPencil θ A = (C (X : K[X]) * (X : K[X][X])) • (1 : Matrix (Fin (k+1)) (Fin (k+1)) K[X][X]) +
      (pencilBase θ A).map liftCoefficients := by
  apply Matrix.ext
  intro i j
  simp only [scaledPencil, pencilBase, spectralSlope, Matrix.add_apply,
    Matrix.smul_apply, Matrix.map_apply, Matrix.diagonal_apply, Matrix.one_apply,
    liftCoefficients, map_add]
  (split_ifs <;> simp [Polynomial.mapRingHom]); ring

theorem scaledTrace_commutator (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K)
    (Z : Matrix (Fin (k+1)) (Fin (k+1)) K[X]) :
    scaledTrace θ A (pencilBase θ A * Z - Z * pencilBase θ A) = 0 := by
  unfold scaledTrace
  rw [scaledPencil_eq]
  have hm : (pencilBase θ A * Z - Z * pencilBase θ A).map liftCoefficients =
      (pencilBase θ A).map liftCoefficients * Z.map liftCoefficients -
        Z.map liftCoefficients * (pencilBase θ A).map liftCoefficients := by
    change (liftCoefficients (K := K)).mapMatrix _ = _
    rw [map_sub, map_mul, map_mul]
    rfl
  rw [hm]
  exact trace_commutator_adjugate_scalar _ _ _

theorem coeff_scaledTrace_top (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K)
    (Y : Matrix (Fin (k+1)) (Fin (k+1)) K[X]) (d : ℕ)
    (hY : ∀ i j, (Y i j).natDegree ≤ d) :
    (scaledTrace θ A Y).coeff (d+k) =
      (Y.map (fun p => C (p.coeff d)) * (spectralSlope θ).adjugate).trace := by
  simp only [scaledTrace, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.map_apply, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (Polynomial.map C (Y i j) *
    ((X : K[X][X]) • (spectralSlope θ).map C + (A.map C).map C).adjugate j i).coeff (d+k) = _
  rw [coeff_mul_add_eq_of_natDegree_le
    ((natDegree_map_le).trans (hY i j))
    (natDegree_adjugate_linear_le (spectralSlope θ) (A.map C) j i)]
  simp only [coeff_map]
  rw [coeff_adjugate_linear]

theorem diagonal_top_zero (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K)
    (Y : Matrix (Fin (k+1)) (Fin (k+1)) K[X]) (d : ℕ) (hd : 0<d)
    (hY : ∀ i j, (Y i j).natDegree ≤ d)
    (hT : (scaledTrace θ A Y).natDegree ≤ k) :
    ∀ i, (Y i i).coeff d = 0 := by
  have hh := coeff_eq_zero_of_natDegree_lt (hT.trans_lt (by omega : k < d+k))
  rw [coeff_scaledTrace_top θ A Y d hY] at hh
  exact diagonal_zero_of_trace_slope θ hθ
    (Y.map (fun p => p.coeff d)) hh

theorem scaledTrace_sub (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K)
    (Y Z : Matrix (Fin (k+1)) (Fin (k+1)) K[X]) :
    scaledTrace θ A (Y-Z) = scaledTrace θ A Y - scaledTrace θ A Z := by
  unfold scaledTrace
  have hm : (Y-Z).map liftCoefficients = Y.map liftCoefficients - Z.map liftCoefficients :=
    (liftCoefficients (K := K)).mapMatrix.map_sub Y Z
  rw [hm, sub_mul, Matrix.trace_sub]

theorem pencil_commutator_expand (θ : Fin (k+1) → K)
    (A Z : Matrix (Fin (k+1)) (Fin (k+1)) K) (d : ℕ) :
    pencilBase θ A * ((X : K[X])^d • Z.map C) -
      ((X : K[X])^d • Z.map C) * pencilBase θ A =
      (X : K[X])^(d+1) • (Matrix.diagonal θ * Z - Z * Matrix.diagonal θ).map C +
        (X : K[X])^d • (A * Z - Z * A).map C := by
  simp only [pencilBase, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.map_sub C (map_sub C), Matrix.map_mul, smul_sub, pow_succ]
  rw [mul_comm X (X^d)]
  module

theorem exists_lower_multiplier (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K)
    (Y : Matrix (Fin (k+1)) (Fin (k+1)) K[X]) (d : ℕ)
    (hY : ∀ i j, (Y i j).natDegree ≤ d+1)
    (hT : (scaledTrace θ A Y).natDegree ≤ k) :
    ∃ Y' : Matrix (Fin (k+1)) (Fin (k+1)) K[X],
      (∀ i j, (Y' i j).natDegree ≤ d) ∧ scaledTrace θ A Y' = scaledTrace θ A Y := by
  let Ytop : Matrix (Fin (k+1)) (Fin (k+1)) K := Y.map (fun p => p.coeff (d+1))
  have hz : ∀ i, Ytop i i = 0 := diagonal_top_zero θ hθ A Y (d+1) (by omega) hY hT
  obtain ⟨Z, hZ⟩ := exists_diagonal_commutator θ hθ Ytop hz
  let W := pencilBase θ A * ((X : K[X])^d • Z.map C) -
    ((X : K[X])^d • Z.map C) * pencilBase θ A
  refine ⟨Y-W, ?_, ?_⟩
  · intro i j
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    have hW : W = (X : K[X])^(d+1) • Ytop.map C +
        (X : K[X])^d • (A * Z - Z * A).map C := by
      dsimp [W]
      rw [pencil_commutator_expand, hZ]
    rw [Matrix.sub_apply, coeff_sub, hW]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      coeff_add, mul_comm (_^_) (C _), coeff_C_mul, coeff_X_pow]
    by_cases hnd : n = d+1
    · subst n
      simp [Ytop]
    · have hlt : d+1 < n := by omega
      rw [coeff_eq_zero_of_natDegree_lt ((hY i j).trans_lt hlt)]
      simp [hnd, show n≠d by omega]
  · rw [scaledTrace_sub]
    have hzero : scaledTrace θ A W = 0 := scaledTrace_commutator θ A _
    rw [hzero, sub_zero]

theorem exists_constant_multiplier_of_bounded_scaledTrace
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K)
    (Y : Matrix (Fin (k+1)) (Fin (k+1)) K[X]) (d : ℕ)
    (hY : ∀ i j, (Y i j).natDegree ≤ d)
    (hT : (scaledTrace θ A Y).natDegree ≤ k) :
    ∃ Y₀ : Matrix (Fin (k+1)) (Fin (k+1)) K,
      scaledTrace θ A (Y₀.map C) = scaledTrace θ A Y := by
  induction d generalizing Y with
  | zero =>
      refine ⟨Y.map (fun p => p.coeff 0), ?_⟩
      have he : (Y.map (fun p => p.coeff 0)).map C = Y := by
        apply Matrix.ext
        intro i j
        exact (eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero (hY i j))).symm
      rw [he]
  | succ d ih =>
      obtain ⟨Y', hY', he⟩ := exists_lower_multiplier θ hθ A Y d hY hT
      have hT' : (scaledTrace θ A Y').natDegree ≤ k := by rw [he]; exact hT
      obtain ⟨Y₀, hY₀⟩ := ih Y' hY' hT'
      exact ⟨Y₀, hY₀.trans he⟩

end Scaling

section OuterVariableReduction
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

noncomputable def pencilMatrix (A : Matrix ι ι R) : Matrix ι ι R[X] :=
  (X : R[X]) • (1 : Matrix ι ι R[X]) + A.map C

noncomputable def adjTrace (A Y : Matrix ι ι R) : R[X] :=
  (Y.map C * (pencilMatrix A).adjugate).trace

@[simp] theorem adjTrace_zero (A : Matrix ι ι R) : adjTrace A 0 = 0 := by
  simp [adjTrace]

theorem adjTrace_add (A Y Z : Matrix ι ι R) :
    adjTrace A (Y+Z) = adjTrace A Y + adjTrace A Z := by
  have hm : (Y+Z).map C = Y.map C + Z.map C := C.mapMatrix.map_add Y Z
  simp only [adjTrace, hm, add_mul, Matrix.trace_add]

theorem adjTrace_neg (A Y : Matrix ι ι R) : adjTrace A (-Y) = -adjTrace A Y := by
  have hm : (-Y).map C = -Y.map C := C.mapMatrix.map_neg Y
  simp only [adjTrace, hm, neg_mul, Matrix.trace_neg]

theorem adjTrace_smul (A Y : Matrix ι ι R) (a : R) :
    adjTrace A (a • Y) = C a * adjTrace A Y := by
  have hm : (a • Y).map C = C a • Y.map C := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  simp only [adjTrace, hm, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

theorem X_mul_adjTrace (A Y : Matrix ι ι R) :
    X * adjTrace A Y = adjTrace A (-(Y*A)) + C Y.trace * (pencilMatrix A).det := by
  have hM : (X : R[X]) • (pencilMatrix A).adjugate =
      (pencilMatrix A).det • (1 : Matrix ι ι R[X]) -
        A.map C * (pencilMatrix A).adjugate := by
    have he := Matrix.mul_adjugate (pencilMatrix A)
    conv_lhs at he => rw [pencilMatrix, add_mul, Matrix.smul_mul, one_mul]
    exact eq_sub_of_add_eq he
  calc
    _ = (Y.map C * ((X : R[X]) • (pencilMatrix A).adjugate)).trace := by
      rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      rfl
    _ = (Y.map C * ((pencilMatrix A).det • 1 -
        A.map C * (pencilMatrix A).adjugate)).trace := by rw [hM]
    _ = _ := by
      rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, mul_one,
        Matrix.trace_smul, smul_eq_mul, ← Matrix.mul_assoc,
        ← Matrix.map_mul, adjTrace_neg]
      have ht : (Y.map C).trace = C Y.trace := (AddMonoidHom.map_trace (C : R →+* R[X]) Y).symm
      rw [ht]
      dsimp only [adjTrace]
      ring

def HasAdjugateNormalForm (A : Matrix ι ι R) (P : R[X]) : Prop :=
  ∃ (Y : Matrix ι ι R) (H : R[X]), P = adjTrace A Y + H * (pencilMatrix A).det

namespace HasAdjugateNormalForm
variable {A : Matrix ι ι R} {P Q : R[X]}

theorem zero : HasAdjugateNormalForm A 0 := by
  exact ⟨0, 0, by simp⟩

theorem add (hP : HasAdjugateNormalForm A P) (hQ : HasAdjugateNormalForm A Q) :
    HasAdjugateNormalForm A (P+Q) := by
  obtain ⟨Y,H,rfl⟩ := hP
  obtain ⟨Z,J,rfl⟩ := hQ
  refine ⟨Y+Z,H+J,?_⟩
  rw [adjTrace_add]
  ring

theorem C_mul (hP : HasAdjugateNormalForm A P) (a : R) :
    HasAdjugateNormalForm A (C a * P) := by
  obtain ⟨Y,H,rfl⟩ := hP
  refine ⟨a • Y, C a * H, ?_⟩
  rw [adjTrace_smul]
  ring

theorem X_mul (hP : HasAdjugateNormalForm A P) :
    HasAdjugateNormalForm A (X*P) := by
  obtain ⟨Y,H,rfl⟩ := hP
  refine ⟨-(Y*A), C Y.trace + X*H, ?_⟩
  rw [mul_add, X_mul_adjTrace]
  ring

theorem mul (hP : HasAdjugateNormalForm A P) (f : R[X]) :
    HasAdjugateNormalForm A (f*P) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simpa only [add_mul] using hf.add hg
  | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial, mul_assoc]
      apply HasAdjugateNormalForm.C_mul
      induction n with
      | zero => simpa using hP
      | succ n ih => simpa only [pow_succ', mul_assoc] using ih.X_mul

end HasAdjugateNormalForm

noncomputable def cofactorIdeal (A : Matrix ι ι R) : Ideal R[X] :=
  Ideal.span (Set.range fun ij : ι × ι => (pencilMatrix A).adjugate ij.1 ij.2)

theorem normalForm_of_mem_cofactorIdeal (A : Matrix ι ι R) (P : R[X])
    (hP : P ∈ cofactorIdeal A) : HasAdjugateNormalForm A P := by
  let J : Ideal R[X] :=
    { carrier := {P | HasAdjugateNormalForm A P}
      zero_mem' := HasAdjugateNormalForm.zero
      add_mem' := fun h h' => h.add h'
      smul_mem' := fun f _ h => h.mul f }
  have hle : cofactorIdeal A ≤ J := by
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨i,j⟩, rfl⟩
    change HasAdjugateNormalForm A ((pencilMatrix A).adjugate i j)
    refine ⟨Matrix.single j i 1, 0, ?_⟩
    simp [adjTrace, Matrix.map_single, Matrix.trace_single_mul]
  exact hle hP

end OuterVariableReduction

section DegreeNormalForm
variable {R : Type*} [CommRing R] [IsDomain R] {k : ℕ}

omit [IsDomain R] in

theorem natDegree_adjTrace_le
    (A Y : Matrix (Fin (k+1)) (Fin (k+1)) R) :
    (adjTrace A Y).natDegree ≤ k := by
  unfold adjTrace
  change (∑ i, (Y.map C * (pencilMatrix A).adjugate) i i).natDegree ≤ k
  apply natDegree_sum_le_of_forall_le
  intro i hi
  rw [Matrix.mul_apply]
  apply natDegree_sum_le_of_forall_le
  intro j hj
  apply le_trans (natDegree_C_mul_le _ _)
  have hm : (1 : Matrix (Fin (k+1)) (Fin (k+1)) R).map C = 1 := by
    exact C.mapMatrix.map_one
  simpa only [pencilMatrix, hm] using natDegree_adjugate_linear_le (1 : Matrix (Fin (k+1)) (Fin (k+1)) R) A j i

theorem natDegree_det_pencilMatrix
    (A : Matrix (Fin (k+1)) (Fin (k+1)) R) :
    (pencilMatrix A).det.natDegree = k+1 := by
  have hm : (1 : Matrix (Fin (k+1)) (Fin (k+1)) R).map C = 1 := C.mapMatrix.map_one
  have hc : (pencilMatrix A).det.coeff (k+1) = 1 := by
    simpa only [pencilMatrix, hm, Fintype.card_fin, Matrix.det_one] using
      coeff_det_X_add_C_card (1 : Matrix (Fin (k+1)) (Fin (k+1)) R) A
  apply le_antisymm
  · simpa only [pencilMatrix, hm, Fintype.card_fin] using
      natDegree_det_X_add_C_le (1 : Matrix (Fin (k+1)) (Fin (k+1)) R) A
  · exact le_natDegree_of_ne_zero (hc ▸ one_ne_zero)

theorem exists_multiplier_of_mem_cofactorIdeal
    (A : Matrix (Fin (k+1)) (Fin (k+1)) R) (P : R[X])
    (hP : P ∈ cofactorIdeal A) (hdeg : P.natDegree ≤ k) :
    ∃ Y : Matrix (Fin (k+1)) (Fin (k+1)) R, P = adjTrace A Y := by
  obtain ⟨Y,H,h⟩ := normalForm_of_mem_cofactorIdeal A P hP
  have hH : H = 0 := by
    by_contra hn
    have hF : (pencilMatrix A).det ≠ 0 := by
      intro hzero
      have := natDegree_det_pencilMatrix A
      simp only [hzero, natDegree_zero] at this
      omega
    have hd : (H*(pencilMatrix A).det).natDegree ≤ k := by
      have he : H*(pencilMatrix A).det = P - adjTrace A Y := by rw [h]; ring
      rw [he]
      exact le_trans (natDegree_sub_le _ _) (max_le hdeg (natDegree_adjTrace_le A Y))
    rw [natDegree_mul hn hF, natDegree_det_pencilMatrix] at hd
    omega
  refine ⟨Y, ?_⟩
  simpa only [hH, zero_mul, add_zero] using h
end DegreeNormalForm

section BivariateScaling
variable {K : Type*} [Field K] {k : ℕ}

noncomputable def scaleHom : K[X][X] →+* K[X][X] :=
  Bivariate.swap.toRingHom.comp (compRingHom (C X * X))

@[simp] theorem scaleHom_C (p : K[X]) : scaleHom (C p) = liftCoefficients p := by
  simp [scaleHom, Bivariate.swap_C, liftCoefficients]

@[simp] theorem scaleHom_X : scaleHom (X : K[X][X]) = C X * X := by
  change Bivariate.swap ((X : K[X][X]).comp (C X * X)) = _
  rw [X_comp, map_mul, Bivariate.swap_X, Bivariate.swap_Y, mul_comm]

theorem scaleHom_injective : Function.Injective (scaleHom (K := K)) := by
  apply (injective_iff_map_eq_zero _).2
  intro p hp
  have hc : p.comp (C X * X) = 0 := by
    apply Bivariate.swap.injective
    change Bivariate.swap (p.comp (C X * X)) = 0 at hp
    simpa only [map_zero] using hp
  rcases comp_eq_zero_iff.mp hc with h | ⟨_, h⟩
  · exact h
  · have hn := congrArg natDegree h
    rw [natDegree_C_mul_X X X_ne_zero, natDegree_C] at hn
    omega

theorem scaleHom_pencil (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) :
    (pencilMatrix (pencilBase θ A)).map scaleHom = scaledPencil θ A := by
  rw [scaledPencil_eq]
  apply Matrix.ext
  intro i j
  simp only [pencilMatrix, Matrix.map_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, map_add, map_mul]
  split_ifs <;> simp

theorem scaleHom_adjTrace (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K)
    (Y : Matrix (Fin (k+1)) (Fin (k+1)) K[X]) :
    scaleHom (adjTrace (pencilBase θ A) Y) = scaledTrace θ A Y := by
  unfold adjTrace scaledTrace
  have ha : (pencilMatrix (pencilBase θ A)).adjugate.map scaleHom =
      ((pencilMatrix (pencilBase θ A)).map scaleHom).adjugate :=
    RingHom.map_adjugate scaleHom _
  rw [AddMonoidHom.map_trace, Matrix.map_mul, ha, scaleHom_pencil]
  congr 2
  apply Matrix.ext
  intro i j
  exact scaleHom_C _

theorem exists_constant_multiplier_of_mem_cofactorIdeal
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (P : K[X][X])
    (hP : P ∈ cofactorIdeal (pencilBase θ A))
    (houter : P.natDegree ≤ k) (htotal : (scaleHom P).natDegree ≤ k) :
    ∃ Y : Matrix (Fin (k+1)) (Fin (k+1)) K,
      P = adjTrace (pencilBase θ A) (Y.map C) := by
  obtain ⟨Y, hY⟩ := exists_multiplier_of_mem_cofactorIdeal _ _ hP houter
  have hs : (scaledTrace θ A Y).natDegree ≤ k := by
    simpa only [hY, scaleHom_adjTrace] using htotal
  obtain ⟨d, hd⟩ := (Set.finite_range (fun ij : Fin (k+1) × Fin (k+1) =>
    (Y ij.1 ij.2).natDegree)).bddAbove
  obtain ⟨Z, hZ⟩ := exists_constant_multiplier_of_bounded_scaledTrace θ hθ A Y d
    (fun i j => hd ⟨(i,j), rfl⟩) hs
  refine ⟨Z, scaleHom_injective ?_⟩
  rw [hY, scaleHom_adjTrace, scaleHom_adjTrace]
  exact hZ.symm

theorem scaleHom_monomial_monomial (a b : ℕ) (c : K) :
    scaleHom (monomial a (monomial b c)) = monomial (a+b) (monomial a c) := by
  simp only [← C_mul_X_pow_eq_monomial, map_mul, map_pow, scaleHom_C,
    scaleHom_X, liftCoefficients, coe_mapRingHom, Polynomial.map_C, Polynomial.map_X]
  simp only [mul_pow, pow_add]
  ring

theorem coeff_scaleHom (P : K[X][X]) (d i : ℕ) :
    ((scaleHom P).coeff d).coeff i =
      if i ≤ d then (P.coeff i).coeff (d-i) else 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [map_add, coeff_add, hP, hQ]
      split_ifs <;> simp
  | monomial a p =>
      induction p using Polynomial.induction_on' with
      | add p q hp hq =>
          simp only [map_add, coeff_add, hp, hq]
          split_ifs <;> simp
      | monomial b c =>
          rw [scaleHom_monomial_monomial]
          by_cases hai : a = i
          · subst a
            by_cases hib : i+b = d
            · have hi : i ≤ d := by omega
              have hb : b = d-i := by omega
              simp [hi, hb]
            · by_cases hi : i ≤ d
              · have hb : b ≠ d-i := by omega
                simp [coeff_monomial, hi, hib, hb]
              · simp [coeff_monomial, hi, hib]
          · by_cases hab : a+b = d <;> simp [coeff_monomial, hai, hab]

def TotalDegreeLE (P : K[X][X]) (d : ℕ) : Prop :=
  ∀ i j : ℕ, d < i+j → (P.coeff i).coeff j = 0

theorem TotalDegreeLE.outer {P : K[X][X]} {d : ℕ} (hP : TotalDegreeLE P d) :
    P.natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  ext j
  simpa only [coeff_zero] using hP i j (by omega)

theorem TotalDegreeLE.scaled {P : K[X][X]} {d : ℕ} (hP : TotalDegreeLE P d) :
    (scaleHom P).natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  ext i
  rw [coeff_scaleHom]
  split_ifs with hi
  · simpa only [coeff_zero] using hP i (n-i) (by omega)
  · simp

theorem adjugate_generation
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (P : K[X][X])
    (hP : P ∈ cofactorIdeal (pencilBase θ A)) (hdeg : TotalDegreeLE P k) :
    ∃ Y : Matrix (Fin (k+1)) (Fin (k+1)) K,
      P = adjTrace (pencilBase θ A) (Y.map C) :=
  exists_constant_multiplier_of_mem_cofactorIdeal θ hθ A P hP hdeg.outer hdeg.scaled
theorem totalDegreeLE_iff_scaled_natDegree (P : K[X][X]) (d : ℕ) :
    TotalDegreeLE P d ↔ (scaleHom P).natDegree ≤ d := by
  refine ⟨TotalDegreeLE.scaled, ?_⟩
  intro hd i j hij
  have hc := coeff_eq_zero_of_natDegree_lt (hd.trans_lt hij)
  have hh := congrArg (fun p : K[X] => p.coeff i) hc
  simpa only [coeff_scaleHom, Nat.le_add_right, ↓reduceIte, Nat.add_sub_cancel_left,
    coeff_zero] using hh

theorem TotalDegreeLE.mul {P Q : K[X][X]} {d e : ℕ}
    (hP : TotalDegreeLE P d) (hQ : TotalDegreeLE Q e) :
    TotalDegreeLE (P*Q) (d+e) := by
  rw [totalDegreeLE_iff_scaled_natDegree, map_mul]
  exact natDegree_mul_le.trans (Nat.add_le_add hP.scaled hQ.scaled)

theorem TotalDegreeLE.mono {P : K[X][X]} {d e : ℕ}
    (hP : TotalDegreeLE P d) (hde : d ≤ e) : TotalDegreeLE P e :=
  fun i j hij => hP i j (hde.trans_lt hij)

theorem totalDegreeLE_monomial (a b : ℕ) (c : K) :
    TotalDegreeLE (monomial a (monomial b c)) (a+b) := by
  rw [totalDegreeLE_iff_scaled_natDegree, scaleHom_monomial_monomial]
  exact natDegree_monomial_le _

theorem coeff_adjTrace_eq_zero
    (θ : Fin (k+1) → K) (A Y : Matrix (Fin (k+1)) (Fin (k+1)) K) (q : ℕ)
    (hcrit : ∀ i j, (((pencilMatrix (pencilBase θ A)).adjugate i j).coeff q).coeff q = 0) :
    ((adjTrace (pencilBase θ A) (Y.map C)).coeff q).coeff q = 0 := by
  simp only [adjTrace, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.map_apply, finsetSum_coeff, coeff_C_mul, hcrit, mul_zero,
    Finset.sum_const_zero]

theorem critical_ideal_eq_zero
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (q : ℕ) (hq : 3*q ≤ k)
    (hcrit : ∀ i j, (((pencilMatrix (pencilBase θ A)).adjugate i j).coeff q).coeff q = 0)
    {P : K[X][X]} (hP : P ∈ cofactorIdeal (pencilBase θ A))
    (hdeg : TotalDegreeLE P q) : P = 0 := by
  ext a b
  simp only [coeff_zero]
  by_cases hab : a+b ≤ q
  · have ha : a ≤ q := by omega
    have hb : b ≤ q := by omega
    let W : K[X][X] := monomial (q-a) (monomial (q-b) 1)
    have hW : TotalDegreeLE (W*P) k :=
      ((totalDegreeLE_monomial (q-a) (q-b) (1 : K)).mul hdeg).mono (by omega)
    have hWP : W*P ∈ cofactorIdeal (pencilBase θ A) :=
      Ideal.mul_mem_left _ W hP
    obtain ⟨Y, hY⟩ := adjugate_generation θ hθ A (W*P) hWP hW
    have hz : (((W*P).coeff q).coeff q) = 0 := by
      rw [hY]
      exact coeff_adjTrace_eq_zero θ A Y q hcrit
    have hca := coeff_monomial_mul P (q-a) a (monomial (q-b) (1 : K))
    have hcb := coeff_monomial_mul (P.coeff a) (q-b) b (1 : K)
    rw [Nat.add_sub_of_le ha] at hca
    rw [Nat.add_sub_of_le hb, one_mul] at hcb
    change (((monomial (q-a) (monomial (q-b) 1) * P).coeff q).coeff q) = 0 at hz
    rw [hca, hcb] at hz
    exact hz
  · exact hdeg a b (by omega)

abbrev PlaneIndex (q : ℕ) := {p : Fin (q+2) × Fin (q+2) // p.1 < p.2}

theorem card_planeIndex (q : ℕ) : Fintype.card (PlaneIndex q) = (q+2).choose 2 := by
  rw [Fintype.card_subtype]
  simpa only [Fintype.card_fin] using (Fintype.card_product_filter_lt (α := Fin (q+2)))

noncomputable def planeMap (q : ℕ) : (PlaneIndex q → K) →ₗ[K] K[X][X] where
  toFun f := ∑ i, monomial i.val.1.val (monomial (i.val.2.val-i.val.1.val-1) (f i))
  map_add' f g := by simp [Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.smul_sum, smul_monomial]

theorem coeff_planeMap (q : ℕ) (f : PlaneIndex q → K) (i : PlaneIndex q) :
    (((planeMap q f).coeff i.val.1.val).coeff (i.val.2.val-i.val.1.val-1)) = f i := by
  classical
  simp only [planeMap, LinearMap.coe_mk, AddHom.coe_mk, finsetSum_coeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    by_cases ha : j.val.1.val = i.val.1.val
    · have hb : j.val.2.val-j.val.1.val-1 ≠ i.val.2.val-i.val.1.val-1 := by
        intro h
        apply hji
        apply Subtype.ext
        apply Prod.ext
        · exact Fin.ext ha
        · apply Fin.ext
          have hi := i.property
          have hj := j.property
          change i.val.1.val < i.val.2.val at hi
          change j.val.1.val < j.val.2.val at hj
          omega
      simp only [ha] at hb
      simp [coeff_monomial, ha, hb]
    · simp [coeff_monomial, ha]
  · simp

theorem totalDegreeLE_planeMap (q : ℕ) (f : PlaneIndex q → K) :
    TotalDegreeLE (planeMap q f) q := by
  classical
  intro a b hab
  simp only [planeMap, LinearMap.coe_mk, AddHom.coe_mk, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i _
  have hi := i.property
  change i.val.1.val < i.val.2.val at hi
  have hbnd := i.val.2.isLt
  by_cases ha : i.val.1.val = a
  · have hb : i.val.2.val-i.val.1.val-1 ≠ b := by omega
    simp only [ha] at hb
    simp [coeff_monomial, ha, hb]
  · simp [coeff_monomial, ha]

theorem critical_cofactor_length
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (q : ℕ) (hq : 3*q ≤ k)
    (hcrit : ∀ i j, (((pencilMatrix (pencilBase θ A)).adjugate i j).coeff q).coeff q = 0) :
    ((q+2).choose 2 : ℕ∞) ≤ Module.length K (K[X][X] ⧸ cofactorIdeal (pencilBase θ A)) := by
  classical
  let I := cofactorIdeal (pencilBase θ A)
  let f : (PlaneIndex q → K) →ₗ[K] (K[X][X] ⧸ I) :=
    (Ideal.Quotient.mkₐ K I).toLinearMap.comp (planeMap q)
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro P hP
    have hmem : planeMap q P ∈ cofactorIdeal (pencilBase θ A) :=
      Ideal.Quotient.eq_zero_iff_mem.mp hP
    have hz := critical_ideal_eq_zero θ hθ A q hq hcrit hmem (totalDegreeLE_planeMap q P)
    funext i
    have hc := congrArg (fun p : K[X][X] => (p.coeff i.val.1.val).coeff
      (i.val.2.val-i.val.1.val-1)) hz
    simpa only [coeff_planeMap, coeff_zero, Pi.zero_apply] using hc
  have h := Module.length_le_of_injective (R := K) f hf
  rw [Module.length_eq_finrank, Module.finrank_fintype_fun_eq_card, card_planeIndex] at h
  exact h

theorem totalDegreeLE_cofactor (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (i j : Fin (k+1)) :
    TotalDegreeLE ((pencilMatrix (pencilBase θ A)).adjugate i j) k := by
  rw [totalDegreeLE_iff_scaled_natDegree]
  have ha : (pencilMatrix (pencilBase θ A)).adjugate.map scaleHom =
      ((pencilMatrix (pencilBase θ A)).map scaleHom).adjugate :=
    RingHom.map_adjugate scaleHom _
  have hh := congrArg (fun M => M i j) ha
  change scaleHom ((pencilMatrix (pencilBase θ A)).adjugate i j) = _ at hh
  rw [hh, scaleHom_pencil]
  exact natDegree_adjugate_linear_le (spectralSlope θ) (A.map C) i j

theorem TotalDegreeLE.add {P Q : K[X][X]} {d : ℕ}
    (hP : TotalDegreeLE P d) (hQ : TotalDegreeLE Q d) : TotalDegreeLE (P+Q) d := by
  intro i j hij
  simp only [coeff_add, hP i j hij, hQ i j hij, add_zero]

theorem TotalDegreeLE.sub {P Q : K[X][X]} {d : ℕ}
    (hP : TotalDegreeLE P d) (hQ : TotalDegreeLE Q d) : TotalDegreeLE (P-Q) d := by
  intro i j hij
  simp only [coeff_sub, hP i j hij, hQ i j hij, sub_zero]

theorem TotalDegreeLE.sum {ι : Type*} (s : Finset ι) (f : ι → K[X][X]) {d : ℕ}
    (h : ∀ i ∈ s, TotalDegreeLE (f i) d) : TotalDegreeLE (∑ i ∈ s, f i) d := by
  intro a b hab
  simp only [finsetSum_coeff]
  exact Finset.sum_eq_zero fun i hi => h i hi a b hab

noncomputable def diagonalContraction (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (y : Fin (k+1) → K) : K[X][X] :=
  adjTrace (pencilBase θ A) ((Matrix.diagonal y).map C)

theorem diagonalContraction_eq_sum (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (y : Fin (k+1) → K) :
    diagonalContraction θ A y = ∑ i, C (C (y i)) *
      (pencilMatrix (pencilBase θ A)).adjugate i i := by
  simp [diagonalContraction, adjTrace, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.diagonal_apply]

theorem diagonalContraction_mem (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (y : Fin (k+1) → K) :
    diagonalContraction θ A y ∈ cofactorIdeal (pencilBase θ A) := by
  rw [diagonalContraction_eq_sum]
  apply Ideal.sum_mem
  intro i _
  apply Ideal.mul_mem_left
  exact Ideal.subset_span ⟨(i,i), rfl⟩

theorem totalDegreeLE_diagonalContraction (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (y : Fin (k+1) → K) :
    TotalDegreeLE (diagonalContraction θ A y) k := by
  rw [diagonalContraction_eq_sum]
  apply TotalDegreeLE.sum
  intro i _
  simpa only [zero_add, monomial_zero_left] using
    (totalDegreeLE_monomial 0 0 (y i)).mul (totalDegreeLE_cofactor θ A i i)

noncomputable def slopeTrace (θ : Fin (k+1) → K) (y : Fin (k+1) → K) : K[X] :=
  ((Matrix.diagonal y).map C * (spectralSlope θ).adjugate).trace

theorem natDegree_adjugate_slope_le (θ : Fin (k+1) → K) (i j : Fin (k+1)) :
    ((spectralSlope θ).adjugate i j).natDegree ≤ k := by
  have hs : spectralSlope θ = (X : K[X]) •
      (1 : Matrix (Fin (k+1)) (Fin (k+1)) K).map C +
      (Matrix.diagonal θ).map C := by
    ext i j
    simp only [spectralSlope, Matrix.diagonal_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hs]
  exact natDegree_adjugate_linear_le 1 (Matrix.diagonal θ) i j

theorem natDegree_slopeTrace_le (θ : Fin (k+1) → K) (y : Fin (k+1) → K) :
    (slopeTrace θ y).natDegree ≤ k := by
  simp only [slopeTrace, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.map_apply]
  apply natDegree_sum_le_of_forall_le
  intro i _
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_C_mul_le _ _).trans (natDegree_adjugate_slope_le θ j i)

noncomputable def slopeCoefficientMap (θ : Fin (k+1) → K) :
    (Fin (k+1) → K) →ₗ[K] (Fin (k+1) → K) where
  toFun y i := (slopeTrace θ y).coeff i
  map_add' y z := by
    ext i
    simp [slopeTrace, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.diagonal_apply, finsetSum_coeff, coeff_C_mul, Finset.sum_add_distrib, add_mul]
  map_smul' c y := by
    ext i
    simp [slopeTrace, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.diagonal_apply, finsetSum_coeff, coeff_C_mul, Finset.mul_sum, mul_assoc]

theorem slopeCoefficientMap_injective (θ : Fin (k+1) → K) (hθ : Function.Injective θ) :
    Function.Injective (slopeCoefficientMap θ) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro y hy
  have hz : slopeTrace θ y = 0 := by
    ext n
    simp only [coeff_zero]
    by_cases hn : n < k+1
    · exact congrFun hy ⟨n,hn⟩
    · exact coeff_eq_zero_of_natDegree_lt ((natDegree_slopeTrace_le θ y).trans_lt (by omega))
  have h := diagonal_zero_of_trace_slope θ hθ (Matrix.diagonal y) hz
  funext i
  simpa only [Matrix.diagonal_apply_eq, Pi.zero_apply] using h i

theorem exists_diagonalContraction_top (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (a : ℕ) (ha : a ≤ k) :
    ∃ y : Fin (k+1) → K,
      (scaleHom (diagonalContraction θ A y)).coeff k = monomial a 1 := by
  obtain ⟨y, hy⟩ := LinearMap.surjective_of_injective (slopeCoefficientMap_injective θ hθ)
    (fun i => (monomial a (1 : K)).coeff i)
  have hs : slopeTrace θ y = monomial a 1 := by
    ext n
    by_cases hn : n < k+1
    · exact congrFun hy ⟨n,hn⟩
    · rw [coeff_eq_zero_of_natDegree_lt ((natDegree_slopeTrace_le θ y).trans_lt (by omega)),
        coeff_eq_zero_of_natDegree_lt ((natDegree_monomial_le (1 : K) : (monomial a (1 : K)).natDegree ≤ a).trans_lt (by omega))]
  refine ⟨y, ?_⟩
  have ht := coeff_scaledTrace_top θ A ((Matrix.diagonal y).map C) 0 (by simp)
  simp only [zero_add] at ht
  rw [diagonalContraction, scaleHom_adjTrace, ht]
  convert hs using 1
  simp [slopeTrace]

theorem TotalDegreeLE.pred_of_top_zero {P : K[X][X]} {d : ℕ}
    (hd : 0 < d) (hP : TotalDegreeLE P d) (hz : (scaleHom P).coeff d = 0) :
    TotalDegreeLE P (d-1) := by
  intro a b hab
  by_cases hlt : d < a+b
  · exact hP a b hlt
  · have he : a+b = d := by omega
    have hc := congrArg (fun p : K[X] => p.coeff a) hz
    rw [coeff_scaleHom] at hc
    simpa only [show a ≤ d by omega, ↓reduceIte, show d-a = b by omega,
      coeff_zero] using hc

theorem exists_lower_monomial_representative
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (hk : 0 < k)
    (a b : ℕ) (hab : a+b = k) :
    ∃ R : K[X][X], TotalDegreeLE R (k-1) ∧
      monomial a (monomial b 1) - R ∈ cofactorIdeal (pencilBase θ A) := by
  obtain ⟨y, hy⟩ := exists_diagonalContraction_top θ hθ A a (by omega)
  let R := monomial a (monomial b (1 : K)) - diagonalContraction θ A y
  refine ⟨R, ?_, ?_⟩
  · apply TotalDegreeLE.pred_of_top_zero hk
    · exact ((totalDegreeLE_monomial a b (1 : K)).mono hab.le).sub
        (totalDegreeLE_diagonalContraction θ A y)
    · simp only [R, map_sub, coeff_sub, scaleHom_monomial_monomial, hab,
        coeff_monomial_same, hy, sub_self]
  · simpa only [R, sub_sub_cancel] using diagonalContraction_mem θ A y

theorem eq_sum_bivariate (P : K[X][X]) :
    P = ∑ a ∈ P.support, ∑ b ∈ (P.coeff a).support,
      monomial a (monomial b ((P.coeff a).coeff b)) := by
  calc
    P = ∑ a ∈ P.support, monomial a (P.coeff a) := (sum_monomial_eq P).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← map_sum]
      exact congrArg (monomial a) (sum_monomial_eq (P.coeff a)).symm

theorem map_mem_of_monomials {V : Type*} [AddCommGroup V] [Module K V]
    (f : K[X][X] →ₗ[K] V) (W : Submodule K V) (P : K[X][X])
    (h : ∀ a b, (P.coeff a).coeff b ≠ 0 →
      f (monomial a (monomial b ((P.coeff a).coeff b))) ∈ W) : f P ∈ W := by
  rw [eq_sum_bivariate P, map_sum]
  apply Submodule.sum_mem
  intro a ha
  rw [map_sum]
  apply Submodule.sum_mem
  intro b hb
  apply h
  exact mem_support_iff.mp hb

theorem cofactor_quotient_spanned
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (hk : 0 < k) :
    Submodule.span K (Set.range (fun i : PlaneIndex (k-1) =>
      (Ideal.Quotient.mkₐ K (cofactorIdeal (pencilBase θ A)))
        (monomial i.val.1.val (monomial (i.val.2.val-i.val.1.val-1) 1)))) = ⊤ := by
  classical
  let I := cofactorIdeal (pencilBase θ A)
  let f := (Ideal.Quotient.mkₐ K I).toLinearMap
  let W := Submodule.span K (Set.range (fun i : PlaneIndex (k-1) =>
    f (monomial i.val.1.val (monomial (i.val.2.val-i.val.1.val-1) 1))))
  have hmon : ∀ d a b : ℕ, a+b = d → ∀ c : K, f (monomial a (monomial b c)) ∈ W := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro a b hab c
      have hscalar : monomial a (monomial b c) = c • monomial a (monomial b (1 : K)) := by
        simp only [smul_monomial, smul_eq_mul, mul_one]
      rw [hscalar, map_smul]
      apply W.smul_mem
      by_cases hd : d < k
      · let i : PlaneIndex (k-1) := ⟨(⟨a, by omega⟩, ⟨a+b+1, by omega⟩), by
          change a < a+b+1
          omega⟩
        apply Submodule.subset_span
        refine ⟨i, ?_⟩
        change f (monomial a (monomial (a+b+1-a-1) (1 : K))) = _
        rw [show a+b+1-a-1 = b by omega]
      · let α := min a k
        let β := k-α
        have hα : α ≤ a := Nat.min_le_left _ _
        have hβ : β ≤ b := by dsimp [β, α]; omega
        have hsum : α+β = k := by dsimp [β, α]; omega
        obtain ⟨R, hR, hmem⟩ := exists_lower_monomial_representative θ hθ A hk α β hsum
        let Q : K[X][X] := monomial (a-α) (monomial (b-β) 1)
        have heq : f (monomial a (monomial b 1)) = f (Q*R) := by
          apply sub_eq_zero.mp
          rw [← map_sub]
          apply Ideal.Quotient.eq_zero_iff_mem.mpr
          have hh := I.mul_mem_left Q hmem
          convert hh using 1
          rw [mul_sub]
          congr 1
          simp only [Q, monomial_mul_monomial, one_mul]
          rw [Nat.sub_add_cancel hα, Nat.sub_add_cancel hβ]
        rw [heq]
        apply map_mem_of_monomials f W (Q*R)
        intro u v huv
        have hde : TotalDegreeLE (Q*R) ((a-α)+(b-β)+(k-1)) :=
          (totalDegreeLE_monomial (a-α) (b-β) (1 : K)).mul hR
        have hle : u+v ≤ (a-α)+(b-β)+(k-1) := by
          by_contra hn
          exact huv (hde u v (by omega))
        exact ih (u+v) (by omega) u v rfl _
  apply top_unique
  intro x _
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply map_mem_of_monomials f W P
  intro a b _
  exact hmon (a+b) a b rfl _

theorem finite_cofactor_quotient
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (hk : 0 < k) :
    Module.Finite K (K[X][X] ⧸ cofactorIdeal (pencilBase θ A)) := by
  classical
  let g := fun i : PlaneIndex (k-1) =>
    (Ideal.Quotient.mkₐ K (cofactorIdeal (pencilBase θ A)))
      (monomial i.val.1.val (monomial (i.val.2.val-i.val.1.val-1) 1))
  have hg := cofactor_quotient_spanned θ hθ A hk
  change Submodule.span K (Set.range g) = ⊤ at hg
  exact Module.Finite.of_fg_top (Submodule.fg_def.mpr ⟨Set.range g, Set.finite_range g, hg⟩)

end BivariateScaling

end PermanentBorder.AdjugateAlgebra

end OAI
