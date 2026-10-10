import OAI.Combinatorics.Sidorenko.Discriminant

namespace OAI


section

namespace SidorenkoCounterexample
open scoped BigOperators
section Scalar
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
noncomputable def characterSignIndicator (ξ : ℤ) (a : K) : ℝ :=
  if quadraticChar K a = ξ then 1 else 0

 theorem characterSignIndicator_nonneg (ξ : ℤ) (a : K) : 0 ≤ characterSignIndicator ξ a := by
  unfold characterSignIndicator; split <;> norm_num
 theorem characterSignIndicator_le_one (ξ : ℤ) (a : K) : characterSignIndicator ξ a ≤ 1 := by
  unfold characterSignIndicator; split <;> norm_num

 theorem characterSignIndicator_formula {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) (a : K) :
    2 * characterSignIndicator ξ a =
      (if a = 0 then 0 else 1) + (ξ : ℝ) * (quadraticChar K a : ℝ) := by
  by_cases ha : a = 0
  · rcases hξ with rfl | rfl <;> simp [characterSignIndicator, ha]
  · rcases quadraticChar_dichotomy ha with hc | hc <;>
      rcases hξ with rfl | rfl <;> norm_num [characterSignIndicator, hc, ha]

omit [Field K] in
 theorem uniformMean_singleton (b : K) :
    uniformMean (fun a : K => if a = b then 1 else 0) = 1 / (Fintype.card K : ℝ) := by
  simp [uniformMean]

 theorem uniformMean_nonzero :
    uniformMean (fun a : K => if a = 0 then 0 else 1) = 1 - 1 / (Fintype.card K : ℝ) := by
  have h := uniformMean_sub (fun _ : K => (1 : ℝ)) (fun a => if a = 0 then 1 else 0)
  simp only [uniformMean_const, uniformMean_singleton] at h
  rw [← h]
  apply uniformMean_congr
  intro a; split <;> simp_all

 theorem uniformMean_character (hK : ringChar K ≠ 2) :
    uniformMean (fun a : K => (quadraticChar K a : ℝ)) = 0 := by
  unfold uniformMean
  have h : (∑ a : K, (quadraticChar K a : ℝ)) = 0 := by
    exact_mod_cast quadraticChar_sum_zero hK
  rw [h, zero_div]

 theorem uniformMean_characterSignIndicator (hK : ringChar K ≠ 2)
    {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    uniformMean (characterSignIndicator (K := K) ξ) =
      (1 - 1 / (Fintype.card K : ℝ)) / 2 := by
  have h := uniformMean_congr (characterSignIndicator_formula (K := K) hξ)
  rw [uniformMean_mul, uniformMean_add, uniformMean_nonzero,
    uniformMean_mul, uniformMean_character hK, mul_zero, add_zero] at h
  linarith

 def scalarAffineEquiv (c b : K) (hc : c ≠ 0) : K ≃ K where
  toFun a := c * (a-b)
  invFun t := t/c+b
  left_inv a := by field_simp; ring
  right_inv t := by field_simp; ring

omit [DecidableEq K] in
 theorem uniformMean_affine (c b : K) (hc : c ≠ 0) (f : K → ℝ) :
    uniformMean (fun a => f (c * (a-b))) = uniformMean f :=
  uniformMean_equiv (scalarAffineEquiv c b hc) f
end Scalar

section MatrixSign
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
noncomputable def symmetricSingularProb (n : ℕ) : ℝ :=
  uniformMean fun M : SymMatrix K n => if M.val.det = 0 then 1 else 0
noncomputable def symmetricSignProb (n : ℕ) (ξ : ℤ) : ℝ :=
  uniformMean fun M : SymMatrix K n => characterSignIndicator ξ M.val.det

 theorem border_singularMean {n : ℕ} (M : SymMatrix K n) (z : Fin n → K)
    (hM : M.val.det ≠ 0) :
    uniformMean (fun a => if (symmetricBorder M z a).val.det = 0 then 1 else 0) =
      1 / (Fintype.card K : ℝ) := by
  simp_rw [symmetricBorder_det M z _ hM, mul_eq_zero, hM, false_or, sub_eq_zero]
  exact uniformMean_singleton _

 theorem border_signMean {n : ℕ} (M : SymMatrix K n) (z : Fin n → K)
    (hM : M.val.det ≠ 0) (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    uniformMean (fun a => characterSignIndicator ξ (symmetricBorder M z a).val.det) =
      (1 - 1 / (Fintype.card K : ℝ)) / 2 := by
  simp_rw [symmetricBorder_det M z _ hM]
  rw [uniformMean_affine _ _ hM, uniformMean_characterSignIndicator hK hξ]

 theorem symmetricSingularProb_nonneg (n : ℕ) : 0 ≤ symmetricSingularProb (K := K) n := by
  apply uniformMean_nonneg; intro M; split <;> norm_num

 theorem symmetricSingularProb_zero : symmetricSingularProb (K := K) 0 = 0 := by
  unfold symmetricSingularProb
  simp [Matrix.det_isEmpty, uniformMean]

 theorem symmetricSingularProb_succ (n : ℕ) :
    symmetricSingularProb (K := K) (n+1) ≤
      symmetricSingularProb (K := K) n + 1 / (Fintype.card K : ℝ) := by
  classical
  unfold symmetricSingularProb
  rw [← uniformMean_equiv (symmetricBorderEquiv (K := K) n).symm,
    uniformMean_prod]
  dsimp only [Function.comp_def, symmetricBorderEquiv, Equiv.coe_fn_symm_mk]
  calc
    _ ≤ uniformMean (fun M : SymMatrix K n =>
        (if M.val.det = 0 then 1 else 0) + 1 / (Fintype.card K : ℝ)) := by
      apply uniformMean_mono
      intro M
      rw [uniformMean_prod]
      by_cases hM : M.val.det = 0
      · simp only [hM, ite_true]
        apply le_trans (show uniformMean (fun z => uniformMean (fun a =>
          if (symmetricBorder M z a).val.det = 0 then 1 else 0)) ≤ 1 from
          uniformMean_bound fun z => uniformMean_bound fun a => by split <;> norm_num)
        have : (0 : ℝ) ≤ 1 / (Fintype.card K : ℝ) := by positivity
        linarith
      · simp only [hM, ite_false, zero_add]
        simp_rw [border_singularMean M _ hM]
        exact le_of_eq (uniformMean_const _)
    _ = _ := by rw [uniformMean_add, uniformMean_const]

 theorem symmetricSingularProb_bound (n : ℕ) :
    symmetricSingularProb (K := K) n ≤ n / (Fintype.card K : ℝ) := by
  induction n with
  | zero => simp [symmetricSingularProb_zero]
  | succ n ih =>
    calc
      _ ≤ symmetricSingularProb (K := K) n + 1 / (Fintype.card K : ℝ) :=
        symmetricSingularProb_succ n
      _ ≤ n / (Fintype.card K : ℝ) + 1 / (Fintype.card K : ℝ) := by linarith
      _ = _ := by push_cast; ring

 theorem symmetricSignProb_nonneg (n : ℕ) (ξ : ℤ) : 0 ≤ symmetricSignProb (K := K) n ξ :=
  uniformMean_nonneg fun _ => characterSignIndicator_nonneg ..

 theorem symmetricSignProb_le_one (n : ℕ) (ξ : ℤ) : symmetricSignProb (K := K) n ξ ≤ 1 :=
  uniformMean_bound fun _ => characterSignIndicator_le_one ..

 theorem symmetricSignProb_succ_error (n : ℕ) (hK : ringChar K ≠ 2)
    {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    |symmetricSignProb (K := K) (n+1) ξ - 1/2| ≤
      symmetricSingularProb (K := K) n + 1 / (Fintype.card K : ℝ) := by
  classical
  have hq : (0 : ℝ) ≤ 1 / (Fintype.card K : ℝ) := by positivity
  unfold symmetricSignProb
  rw [← uniformMean_equiv (symmetricBorderEquiv (K := K) n).symm, uniformMean_prod]
  dsimp only [Function.comp_def, symmetricBorderEquiv, Equiv.coe_fn_symm_mk]
  rw [← uniformMean_const (A := SymMatrix K n) (1/2), ← uniformMean_sub]
  calc
    _ ≤ uniformMean (fun M : SymMatrix K n =>
      |uniformMean (fun za : (Fin n → K) × K =>
        characterSignIndicator ξ (symmetricBorder M za.1 za.2).val.det) - 1/2|) :=
      abs_uniformMean_le _
    _ ≤ uniformMean (fun M : SymMatrix K n =>
        (if M.val.det = 0 then 1 else 0) + 1 / (Fintype.card K : ℝ)) := by
      apply uniformMean_mono
      intro M
      rw [uniformMean_prod]
      by_cases hM : M.val.det = 0
      · simp only [hM, ite_true]
        have h0 := uniformMean_nonneg (fun z : Fin n → K =>
          uniformMean_nonneg fun a => characterSignIndicator_nonneg ξ
            (symmetricBorder M z a).val.det)
        have h1 := uniformMean_bound (fun z : Fin n → K =>
          uniformMean_bound fun a => characterSignIndicator_le_one ξ
            (symmetricBorder M z a).val.det)
        apply abs_le.mpr
        constructor <;> linarith
      · simp only [hM, ite_false, zero_add]
        simp_rw [border_signMean M _ hM hK hξ]
        rw [uniformMean_const]
        apply abs_le.mpr
        constructor <;> linarith
    _ = _ := by rw [uniformMean_add, uniformMean_const]; rfl

 theorem symmetricSignProb_error (n : ℕ) (hn : 0 < n) (hK : ringChar K ≠ 2)
    {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    |symmetricSignProb (K := K) n ξ - 1/2| ≤ n / (Fintype.card K : ℝ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  calc
    _ ≤ symmetricSingularProb (K := K) m + 1 / (Fintype.card K : ℝ) :=
      symmetricSignProb_succ_error m hK hξ
    _ ≤ m / (Fintype.card K : ℝ) + 1 / (Fintype.card K : ℝ) := by
      have := symmetricSingularProb_bound (K := K) m
      linarith
    _ = _ := by push_cast; ring

end MatrixSign
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module LinearMap
section NondegSign
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]
/-- For a nondegenerate form, the radical quotient definition reduces to
its ordinary determinant character in any basis. -/
theorem discriminantSign_nondegenerate (B : LinearMap.BilinForm K V)
    (hBs : B.IsSymm) (hB : B.Nondegenerate)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K V) :
    discriminantSign B hBs = quadraticChar K (B.toMatrix b).det := by
  simpa only [LinearMap.compl₁₂_id_id] using
    discriminantSign_pullback B hBs hB LinearMap.id Function.surjective_id b

end NondegSign
section SumForms
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

def orthogonalSumForm (A : LinearMap.BilinForm K V) (B : LinearMap.BilinForm K W) :
    LinearMap.BilinForm K (V × W) :=
  A.compl₁₂ (LinearMap.fst K V W) (LinearMap.fst K V W) +
    B.compl₁₂ (LinearMap.snd K V W) (LinearMap.snd K V W)

@[simp] theorem orthogonalSumForm_apply (A : LinearMap.BilinForm K V)
    (B : LinearMap.BilinForm K W) (x y : V × W) :
    orthogonalSumForm A B x y = A x.1 y.1 + B x.2 y.2 := rfl

theorem orthogonalSumForm_isSymm (A : LinearMap.BilinForm K V)
    (B : LinearMap.BilinForm K W) (hA : A.IsSymm) (hB : B.IsSymm) :
    (orthogonalSumForm A B).IsSymm := by
  constructor
  intro x y
  simp only [orthogonalSumForm_apply, hA.eq x.1 y.1, hB.eq x.2 y.2]

theorem orthogonalSumForm_nondegenerate (A : LinearMap.BilinForm K V)
    (B : LinearMap.BilinForm K W) (hA : A.Nondegenerate) (hB : B.Nondegenerate) :
    (orthogonalSumForm A B).Nondegenerate := by
  constructor
  · intro x hx
    apply Prod.ext
    · apply hA.1
      intro y
      simpa using hx (y, 0)
    · apply hB.1
      intro y
      simpa using hx (0, y)
  · intro x hx
    apply Prod.ext
    · apply hA.2
      intro y
      simpa using hx (y, 0)
    · apply hB.2
      intro y
      simpa using hx (0, y)

theorem orthogonalSumForm_matrix (A : LinearMap.BilinForm K V)
    (B : LinearMap.BilinForm K W) {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (b : Basis ι K V) (c : Basis κ K W) :
    (orthogonalSumForm A B).toMatrix (b.prod c) =
      Matrix.fromBlocks (A.toMatrix b) 0 0 (B.toMatrix c) := by
  ext i j
  cases i <;> cases j <;>
    simp [LinearMap.BilinForm.toMatrix_apply, Basis.prod_apply]

variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]

/-- When the ranks add without loss and the sum is nondegenerate, determinant
characters multiply. The proof uses the actual radical quotients. -/
theorem discriminantSign_add (A B : LinearMap.BilinForm K V)
    (hA : A.IsSymm) (hB : B.IsSymm) (hS : (A+B).Nondegenerate)
    (hdim : finrank K (V ⧸ A.ker) + finrank K (V ⧸ B.ker) = finrank K V) :
    discriminantSign (A+B) (hA.add hB) = discriminantSign A hA * discriminantSign B hB := by
  classical
  let AQ := radicalQuotientForm A hA
  let BQ := radicalQuotientForm B hB
  let C := orthogonalSumForm AQ BQ
  have hCs : C.IsSymm := orthogonalSumForm_isSymm _ _
    (radicalQuotientForm_isSymm A hA) (radicalQuotientForm_isSymm B hB)
  have hC : C.Nondegenerate := orthogonalSumForm_nondegenerate _ _
    (radicalQuotientForm_nondegenerate A hA) (radicalQuotientForm_nondegenerate B hB)
  let f : V →ₗ[K] (V ⧸ A.ker) × (V ⧸ B.ker) := A.ker.mkQ.prod B.ker.mkQ
  have hfi : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro x hx
    change f x = 0 at hx
    have ha : A x = 0 := (Submodule.Quotient.mk_eq_zero A.ker).mp (congrArg Prod.fst hx)
    have hb : B x = 0 := (Submodule.Quotient.mk_eq_zero B.ker).mp (congrArg Prod.snd hx)
    apply hS.1
    intro y
    simp only [LinearMap.add_apply, ha, hb, LinearMap.zero_apply, add_zero]
  have hfs : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      simpa only [Module.finrank_prod] using hdim.symm)).mp hfi
  have he : C.compl₁₂ f f = A+B := by ext x y; rfl
  let b := Module.finBasis K (V ⧸ A.ker)
  let c := Module.finBasis K (V ⧸ B.ker)
  have hs := discriminantSign_pullback C hCs hC f hfs (b.prod c)
  simp only [he] at hs
  rw [hs]
  change quadraticChar K ((orthogonalSumForm AQ BQ).toMatrix (b.prod c)).det = _
  rw [orthogonalSumForm_matrix, Matrix.det_fromBlocks_zero₂₁, map_mul]
  rfl

end SumForms
section PairSign
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
variable [Fintype K] [DecidableEq K]


theorem half_rank_pair_sign (r : ℕ) (hdim : Fintype.card n = 2*r)
    (A B : Matrix n n K) (hAs : A.IsSymm) (hBs : B.IsSymm)
    (hB : B.det ≠ 0) (hAr : A.rank = r) (hCr : (A-B).rank = r) :
    quadraticChar K B.det = quadraticChar K ((-1 : K)^r) *
      discriminantSign A.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr hAs) *
      discriminantSign (A-B).toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr (hAs.sub hBs)) := by
  classical
  have hAs' := Matrix.isSymm_toBilin'_iff_isSymm.mpr hAs
  have hCs' := Matrix.isSymm_toBilin'_iff_isSymm.mpr (hBs.sub hAs)
  have hadd : A.toBilin' + (B-A).toBilin' = B.toBilin' := by
    rw [← map_add, add_sub_cancel]
  have hBs' := Matrix.isSymm_toBilin'_iff_isSymm.mpr hBs
  have hBnd : B.toBilin'.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hB
  have hdim' : finrank K ((n → K) ⧸ A.toBilin'.ker) +
      finrank K ((n → K) ⧸ (B-A).toBilin'.ker) = finrank K (n → K) := by
    rw [matrix_radical_quotient_rank, matrix_radical_quotient_rank,
      show B-A = -(A-B) by abel, matrix_rank_neg, hAr, hCr, Module.finrank_pi, hdim]
    omega
  have hs := discriminantSign_add A.toBilin' (B-A).toBilin' hAs' hCs'
    (hadd.symm ▸ hBnd) hdim'
  simp only [hadd] at hs
  have hb := discriminantSign_nondegenerate B.toBilin' hBs' hBnd (Pi.basisFun K n)
  have hb' : discriminantSign B.toBilin' hBs' = quadraticChar K B.det := by
    simpa only [show B.toBilin'.toMatrix (Pi.basisFun K n) = B from
      LinearMap.BilinForm.toMatrix'_toBilin' B] using hb
  rw [hb'] at hs
  have hn := discriminantSign_neg (A-B).toBilin'
    (Matrix.isSymm_toBilin'_iff_isSymm.mpr (hAs.sub hBs))
  rw [matrix_radical_quotient_rank, hCr] at hn
  have hneg : -(A-B).toBilin' = (B-A).toBilin' := by
    rw [show B-A = -(A-B) by abel, map_neg]
  simp only [hneg] at hn
  rw [hs, hn]
  ring
end PairSign
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module LinearMap
section RadicalCount
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype K] [DecidableEq K]

omit [Fintype K] [DecidableEq K] in
 theorem symFormQuotient_nondegenerate_iff (U : Submodule K V) (C : SymForm K (V ⧸ U)) :
    (C.val.compl₁₂ U.mkQ U.mkQ).ker = U ↔ C.val.Nondegenerate := by
  constructor
  · intro h
    apply LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mpr
    apply bot_unique
    intro x hx
    obtain ⟨y, rfl⟩ := U.mkQ_surjective x
    apply (Submodule.Quotient.mk_eq_zero U).mpr
    rw [← h]
    apply LinearMap.mem_ker.mpr
    ext z
    exact congrArg (fun f => f (U.mkQ z)) hx
  · intro h
    rw [pullback_ker C.val h U.mkQ U.mkQ_surjective, Submodule.ker_mkQ]

 theorem discriminantSign_pullback_nondegenerate (U : Submodule K V)
    (C : SymForm K (V ⧸ U)) (hC : C.val.Nondegenerate) :
    discriminantSign (C.val.compl₁₂ U.mkQ U.mkQ)
      (pullback_isSymm C.val C.property U.mkQ) = discriminantSign C.val C.property := by
  rw [discriminantSign_pullback C.val C.property hC U.mkQ U.mkQ_surjective
    (Module.finBasis K (V ⧸ U)),
    discriminantSign_nondegenerate C.val C.property hC (Module.finBasis K (V ⧸ U))]

noncomputable def signedRadicalFiberEquiv (U : Submodule K V) (ξ : ℤ) :
    {B : SymForm K V // B.val.ker = U ∧ discriminantSign B.val B.property = ξ} ≃
      {C : SymForm K (V ⧸ U) // C.val.Nondegenerate ∧
        discriminantSign C.val C.property = ξ} := by
  let e : {B : SymForm K V // B.val.ker = U ∧ discriminantSign B.val B.property = ξ} ≃
      {B : {B : SymForm K V // U ≤ B.val.ker} //
        B.val.val.ker = U ∧ discriminantSign B.val.val B.val.property = ξ} :=
    { toFun := fun B => ⟨⟨B.val, le_of_eq B.property.1.symm⟩, B.property⟩
      invFun := fun B => ⟨B.val.val, B.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine e.trans ((formRadicalEquiv U).subtypeEquiv ?_)
  intro B
  let C := formRadicalEquiv U B
  have hback : C.val.compl₁₂ U.mkQ U.mkQ = B.val.val := rfl
  have hn : B.val.val.ker = U ↔ C.val.Nondegenerate := by
    rw [← hback]; exact symFormQuotient_nondegenerate_iff U C
  constructor
  · rintro ⟨hB,hξ⟩
    have hC := hn.mp hB
    refine ⟨hC, ?_⟩
    have hs := discriminantSign_pullback_nondegenerate U C hC
    change discriminantSign B.val.val B.val.property = discriminantSign C.val C.property at hs
    exact hs.symm.trans hξ
  · rintro ⟨hC,hξ⟩
    refine ⟨hn.mpr hC, ?_⟩
    have hs := discriminantSign_pullback_nondegenerate U C hC
    change discriminantSign B.val.val B.val.property = discriminantSign C.val C.property at hs
    exact hs.trans hξ

noncomputable def nonsingularSignedMatrixEquiv (ξ : ℤ) :
    {C : SymForm K V // C.val.Nondegenerate ∧ discriminantSign C.val C.property = ξ} ≃
      {M : SymMatrix K (finrank K V) // quadraticChar K M.val.det = ξ ∧ M.val.det ≠ 0} := by
  refine (symFormMatrix K V).subtypeEquiv ?_
  intro C
  have hn : C.val.Nondegenerate ↔ (C.val.toMatrix (Module.finBasis K V)).det ≠ 0 :=
    LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (Module.finBasis K V)
  constructor
  · rintro ⟨hC,hξ⟩
    refine ⟨?_, hn.mp hC⟩
    change quadraticChar K (C.val.toMatrix (Module.finBasis K V)).det = ξ
    rw [← discriminantSign_nondegenerate C.val C.property hC (Module.finBasis K V)]
    exact hξ
  · rintro ⟨hξ,hC⟩
    refine ⟨hn.mpr hC, ?_⟩
    rw [discriminantSign_nondegenerate C.val C.property (hn.mpr hC) (Module.finBasis K V)]
    exact hξ

 theorem nonsingularSignedForm_card {r : ℕ} (hV : finrank K V = r)
    {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    Nat.card {C : SymForm K V // C.val.Nondegenerate ∧ discriminantSign C.val C.property = ξ} =
      Nat.card {M : SymMatrix K r // quadraticChar K M.val.det = ξ} := by
  rw [Nat.card_congr (nonsingularSignedMatrixEquiv (K := K) (V := V) ξ), hV]
  apply Nat.card_congr
  apply Equiv.subtypeEquiv (Equiv.refl _)
  intro M
  simp only [Equiv.refl_apply, and_iff_left_iff_imp]
  intro h
  apply mt quadraticChar_eq_zero_iff.mpr
  rw [h]
  rcases hξ with rfl | rfl <;> norm_num

 theorem signedRadicalFiber_card (U : Submodule K V) {r : ℕ}
    (hU : finrank K (V ⧸ U) = r) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    Nat.card {B : SymForm K V // B.val.ker = U ∧ discriminantSign B.val B.property = ξ} =
      Nat.card {M : SymMatrix K r // quadraticChar K M.val.det = ξ} := by
  rw [Nat.card_congr (signedRadicalFiberEquiv U ξ)]
  exact nonsingularSignedForm_card hU hξ

end RadicalCount
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module LinearMap
open scoped BigOperators
section RankCard
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype K] [DecidableEq K]

noncomputable def signedNullityFiberEquiv (k : ℕ) (ξ : ℤ) :
    {B : SymForm K V // finrank K B.val.ker = k ∧ discriminantSign B.val B.property = ξ} ≃
      Σ U : DimSubspace K V k,
        {B : SymForm K V // B.val.ker = U.val ∧ discriminantSign B.val B.property = ξ} where
  toFun B := ⟨⟨B.val.val.ker, B.property.1⟩, ⟨B.val, rfl, B.property.2⟩⟩
  invFun UB := ⟨UB.2.val, by rw [UB.2.property.1]; exact UB.1.property, UB.2.property.2⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨U,hU⟩,⟨B,hB,hξ⟩⟩
    dsimp only
    change B.val.ker = U at hB
    subst U
    rfl

 theorem signedNullityForm_card (k : ℕ) (_hk : k ≤ finrank K V)
    {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    Nat.card {B : SymForm K V // finrank K B.val.ker = k ∧ discriminantSign B.val B.property = ξ} =
      Nat.card (DimSubspace K V k) *
        Nat.card {M : SymMatrix K (finrank K V - k) // quadraticChar K M.val.det = ξ} := by
  classical
  let : Finite V := Module.finite_of_finite K
  let : Fintype (DimSubspace K V k) := Fintype.ofFinite _
  rw [Nat.card_congr (signedNullityFiberEquiv k ξ), Nat.card_sigma]
  have hf (U : DimSubspace K V k) :
      Nat.card {B : SymForm K V // B.val.ker = U.val ∧ discriminantSign B.val B.property = ξ} =
        Nat.card {M : SymMatrix K (finrank K V - k) // quadraticChar K M.val.det = ξ} := by
    apply signedRadicalFiber_card U.val _ hξ
    have := U.val.finrank_quotient_add_finrank
    rw [U.property] at this
    omega
  simp only [hf, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Nat.card_eq_fintype_card, Nat.cast_id]

end RankCard
section LayerCard
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

noncomputable def matrixFormEquiv (D : ℕ) : SymMatrix K D ≃ SymForm K (Fin D → K) :=
  Equiv.subtypeEquiv Matrix.toBilin'.toEquiv
    (fun _M => Matrix.isSymm_toBilin'_iff_isSymm.symm)

 theorem signedLayer_card_exact (D r : ℕ) (hrD : r ≤ D) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    (signedLayer K D r ξ).card =
      Nat.card (DimSubspace K (Fin D → K) (D-r)) *
        Nat.card {M : SymMatrix K r // quadraticChar K M.val.det = ξ} := by
  classical
  have e : {M : SymMatrix K D // M.val.rank = r ∧ matrixSign K D M = ξ} ≃
      {B : SymForm K (Fin D → K) // finrank K B.val.ker = D-r ∧
        discriminantSign B.val B.property = ξ} := by
    apply (matrixFormEquiv D).subtypeEquiv
    intro M
    change (M.val.rank = r ∧ matrixSign K D M = ξ) ↔
      (finrank K M.val.toBilin'.ker = D-r ∧ matrixSign K D M = ξ)
    have h := M.val.toBilin'.ker.finrank_quotient_add_finrank
    rw [matrix_radical_quotient_rank] at h
    simp only [Module.finrank_pi, Fintype.card_fin] at h
    omega
  calc
    _ = Nat.card {M : SymMatrix K D // M.val.rank = r ∧ matrixSign K D M = ξ} := by
      simp only [signedLayer, Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = _ := by
      rw [Nat.card_congr e, signedNullityForm_card (D-r) (by simp) hξ]
      have hd : finrank K (Fin D → K) = D := by simp
      rw [hd, Nat.sub_sub_self hrD]

 theorem symmetricSignProb_card (r : ℕ) (ξ : ℤ) :
    symmetricSignProb (K := K) r ξ =
      (Nat.card {M : SymMatrix K r // quadraticChar K M.val.det = ξ} : ℝ) /
        (Fintype.card K : ℝ)^((r+1).choose 2) := by
  unfold symmetricSignProb characterSignIndicator
  rw [uniformMean_indicator, ← Nat.card_eq_fintype_card (α := SymMatrix K r), symMatrix_card]
  simp only [Nat.card_eq_fintype_card, Nat.cast_pow]

 theorem layerMass_exact (D r : ℕ) (hrD : r ≤ D) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    layerMass K D r ξ =
      (Nat.card (DimSubspace K (Fin D → K) (D-r)) : ℝ) *
        (Fintype.card K : ℝ)^((r+1).choose 2) * symmetricSignProb (K := K) r ξ /
        (Fintype.card K : ℝ)^((D+1).choose 2) := by
  unfold layerMass
  rw [signedLayer_card_exact D r hrD hξ, ← Nat.card_eq_fintype_card, symMatrix_card,
    symmetricSignProb_card]
  push_cast
  have hq : (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

end LayerCard
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module LinearMap
open scoped BigOperators
section Binary
variable {K : Type*} [Field K] [Fintype K]

theorem binary_norm_surjective (hK : ringChar K ≠ 2) (a b t : K)
    (ha : a ≠ 0) (hb : b ≠ 0) : ∃ x y : K, a*x^2+b*y^2=t := by
  open Polynomial in
  have hf : (C a * X^2 : K[X]).degree = 2 := degree_C_mul_X_pow 2 ha
  open Polynomial in
  have hg : (C b * X^2 - C t : K[X]).degree = 2 := by
    rw [degree_sub_C (by rw [degree_C_mul_X_pow 2 hb]; decide), degree_C_mul_X_pow 2 hb]
    norm_num
  obtain ⟨x,y,hxy⟩ := FiniteField.exists_root_sum_quadratic hf hg
    (FiniteField.odd_card_of_char_ne_two hK)
  refine ⟨x,y,?_⟩
  simpa only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    ← add_sub_assoc, sub_eq_zero] using hxy
end Binary
section Norms
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

theorem nondegenerate_ne_zero_of_pos (B : LinearMap.BilinForm K E)
    (hB : B.Nondegenerate) (hd : 0 < finrank K E) : B ≠ 0 := by
  intro h
  have hz : ∀ x : E, x=0 := by
    intro x
    apply hB.1
    intro y
    rw [h]
    rfl
  have hzdim : finrank K E=0 := (finrank_zero_iff_forall_zero).mpr hz
  omega

theorem orthogonal_line_finrank (B : LinearMap.BilinForm K E) {x : E}
    (hx : B x x ≠ 0) : finrank K (B.orthogonal (K ∙ x)) + 1 = finrank K E := by
  have hx0 : x ≠ 0 := by intro h; subst x; simp at hx
  have h := Submodule.finrank_add_eq_of_isCompl (B.isCompl_span_singleton_orthogonal hx)
  rw [finrank_span_singleton hx0] at h
  omega

variable [Fintype K]
theorem symmetric_norm_surjective (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
    (hB : B.Nondegenerate) (hD : 2 ≤ finrank K E) (hK : ringChar K ≠ 2) (t : K) :
    ∃ v : E, B v v = t := by
  let : Invertible (2 : K) := invertibleOfNonzero (Ring.two_ne_zero hK)
  obtain ⟨x,hx⟩ := LinearMap.BilinForm.exists_bilinForm_self_ne_zero
    (nondegenerate_ne_zero_of_pos B hB (by omega)) (LinearMap.BilinForm.isSymm_iff.mp hs)
  let P := B.orthogonal (K ∙ x)
  have hPs : (B.restrict P).IsSymm := by constructor; intro u v; exact hs.eq _ _
  have hP := B.restrict_nondegenerate_orthogonal_spanSingleton hB hs.isRefl hx
  have hd : 0 < finrank K P := by have := orthogonal_line_finrank B hx; dsimp [P]; omega
  obtain ⟨y,hy⟩ := LinearMap.BilinForm.exists_bilinForm_self_ne_zero
    (nondegenerate_ne_zero_of_pos (B.restrict P) hP hd) (LinearMap.BilinForm.isSymm_iff.mp hPs)
  obtain ⟨a,b,hab⟩ := binary_norm_surjective hK (B x x) (B y.val y.val) t hx hy
  have hxy : B x y.val = 0 := y.property x (Submodule.mem_span_singleton_self x)
  have hyx : B y.val x = 0 := (hs.eq _ _).trans hxy
  refine ⟨a • x + b • y.val, ?_⟩
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hxy, hyx, mul_zero, add_zero, zero_add]
  linear_combination hab
end Norms
section Equivalences
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]

def BilinEquivalent (B : LinearMap.BilinForm K E) (C : LinearMap.BilinForm K F) : Prop :=
  ∃ e : E ≃ₗ[K] F, ∀ x y, C (e x) (e y) = B x y

def scalarBilin (a : K) : LinearMap.BilinForm K K := a • LinearMap.mul K K
@[simp] theorem scalarBilin_apply (a x y : K) : scalarBilin a x y = a*x*y := by
  simp only [scalarBilin, LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
  ring

theorem scalarBilin_symm (a : K) : (scalarBilin a).IsSymm := by
  constructor; intro x y; simp only [scalarBilin_apply]; ring

theorem scalarBilin_nondegenerate (a : K) (ha : a≠0) : (scalarBilin a).Nondegenerate := by
  constructor
  · intro x hx; have h := hx 1; simpa only [scalarBilin_apply, mul_one, mul_eq_zero,ha,false_or] using h
  · intro x hx; have h := hx 1; simpa only [scalarBilin_apply, mul_one, mul_eq_zero,ha,false_or] using h

noncomputable def lineOrthogonalEquiv (B : LinearMap.BilinForm K E) (x : E)
    (hx : B x x ≠ 0) : (K × B.orthogonal (K ∙ x)) ≃ₗ[K] E :=
  ((LinearEquiv.toSpanNonzeroSingleton K E x (by intro h; subst x; simp at hx)).prodCongr
    (LinearEquiv.refl K (B.orthogonal (K ∙ x)))).trans
    ((K ∙ x).prodEquivOfIsCompl _ (B.isCompl_span_singleton_orthogonal hx))

theorem lineOrthogonalEquiv_apply (B : LinearMap.BilinForm K E) (x : E)
    (hx : B x x ≠ 0) (z : K × B.orthogonal (K ∙ x)) :
    lineOrthogonalEquiv B x hx z = z.1 • x + z.2.val := rfl

theorem lineOrthogonalEquiv_form (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
    (x : E) (hx : B x x ≠ 0) (z w : K × B.orthogonal (K ∙ x)) :
    B (lineOrthogonalEquiv B x hx z) (lineOrthogonalEquiv B x hx w) =
      B x x * z.1 * w.1 + B z.2.val w.2.val := by
  have h1 : B x w.2.val = 0 := w.2.property x (Submodule.mem_span_singleton_self x)
  have h2 : B z.2.val x = 0 := (hs.eq _ _).trans (z.2.property x (Submodule.mem_span_singleton_self x))
  rw [lineOrthogonalEquiv_apply, lineOrthogonalEquiv_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul,h1,h2,mul_zero,add_zero,zero_add]
  ring

variable [FiniteDimensional K E] [FiniteDimensional K F] [Fintype K] [DecidableEq K]
theorem discriminantSign_isometry (B : LinearMap.BilinForm K E)
    (C : LinearMap.BilinForm K F) (hs : B.IsSymm) (ht : C.IsSymm)
    (hB : B.Nondegenerate) (hC : C.Nondegenerate)
    (e : E ≃ₗ[K] F) (he : ∀ x y, C (e x) (e y) = B x y) :
    discriminantSign B hs = discriminantSign C ht := by
  rw [discriminantSign_nondegenerate B hs hB (Module.finBasis K E),
    discriminantSign_nondegenerate C ht hC ((Module.finBasis K E).map e)]
  congr 2
  ext i j
  simp only [LinearMap.BilinForm.toMatrix_apply, Basis.map_apply, he]

theorem discriminantSign_orthogonalSum (B : LinearMap.BilinForm K E)
    (C : LinearMap.BilinForm K F) (hs : B.IsSymm) (ht : C.IsSymm)
    (hB : B.Nondegenerate) (hC : C.Nondegenerate) :
    discriminantSign (orthogonalSumForm B C) (orthogonalSumForm_isSymm B C hs ht) =
      discriminantSign B hs * discriminantSign C ht := by
  rw [discriminantSign_nondegenerate _ _ (orthogonalSumForm_nondegenerate B C hB hC)
      ((Module.finBasis K E).prod (Module.finBasis K F)), orthogonalSumForm_matrix,
    Matrix.det_fromBlocks_zero₂₁, map_mul,
    discriminantSign_nondegenerate B hs hB (Module.finBasis K E),
    discriminantSign_nondegenerate C ht hC (Module.finBasis K F)]

 theorem discriminantSign_scalar (a : K) (ha : a≠0) :
    discriminantSign (scalarBilin a) (scalarBilin_symm a) = quadraticChar K a := by
  rw [discriminantSign_nondegenerate _ _ (scalarBilin_nondegenerate a ha)
    (Basis.singleton Unit K), Matrix.det_unique]
  simp only [LinearMap.BilinForm.toMatrix_apply, Basis.singleton_apply, scalarBilin_apply, mul_one]

 theorem discriminantSign_line_complement (B : LinearMap.BilinForm K E)
    (hs : B.IsSymm) (hB : B.Nondegenerate) (x : E) (hx : B x x ≠ 0) :
    discriminantSign B hs = quadraticChar K (B x x) *
      discriminantSign (B.restrict (B.orthogonal (K ∙ x)))
        (by constructor; intro u v; exact hs.eq u.val v.val) := by
  let P := B.orthogonal (K ∙ x)
  have hp : (B.restrict P).IsSymm := by constructor; intro u v; exact hs.eq _ _
  have hP := B.restrict_nondegenerate_orthogonal_spanSingleton hB hs.isRefl hx
  have he : discriminantSign (orthogonalSumForm (scalarBilin (B x x)) (B.restrict P))
      (orthogonalSumForm_isSymm _ _ (scalarBilin_symm _) hp) = discriminantSign B hs :=
    discriminantSign_isometry _ _ _ hs
      (orthogonalSumForm_nondegenerate _ _ (scalarBilin_nondegenerate _ hx) hP) hB
      (lineOrthogonalEquiv B x hx) (fun z w => by
        simpa only [orthogonalSumForm_apply,scalarBilin_apply,LinearMap.BilinForm.restrict_apply,LinearMap.domRestrict_apply] using lineOrthogonalEquiv_form B hs x hx z w)
  rw [← he, discriminantSign_orthogonalSum _ _ (scalarBilin_symm _) hp (scalarBilin_nondegenerate _ hx) hP,
    discriminantSign_scalar _ hx]
end Equivalences
section Classification
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]
  [Fintype K] [DecidableEq K]

theorem scalarBilin_equivalent_of_sign (a b : K) (ha : a≠0) (hb : b≠0)
    (h : quadraticChar K a = quadraticChar K b) : BilinEquivalent (scalarBilin a) (scalarBilin b) := by
  have hc : quadraticChar K (a*b) = 1 := by
    rw [map_mul,h,←pow_two,quadraticChar_sq_one hb]
  obtain ⟨t,ht⟩ := (quadraticChar_one_iff_isSquare (mul_ne_zero ha hb)).mp hc
  have ht0 : t≠0 := by intro hz; rw [hz,mul_zero] at ht; exact mul_ne_zero ha hb ht
  have hscale : b*(t/b)^2=a := by
    field_simp
    linear_combination ht.symm
  refine ⟨LinearEquiv.smulOfNeZero K K (t/b) (div_ne_zero ht0 hb), ?_⟩
  intro x y
  simp only [LinearEquiv.smulOfNeZero_apply,smul_eq_mul,scalarBilin_apply]
  linear_combination x*y*hscale

omit [Fintype K] [DecidableEq K] in
theorem one_dimensional_form (B : LinearMap.BilinForm K E) (hD : finrank K E=1) :
    ∃ e : K ≃ₗ[K] E, ∀ s t : K, B (e s) (e t) = B (e 1) (e 1)*s*t := by
  let e := LinearEquiv.ofFinrankEq (R := K) K E (by simpa using hD.symm)
  refine ⟨e,?_⟩
  intro s t
  have hs : e s = s • e 1 := by rw [←map_smul]; simp
  have ht : e t = t • e 1 := by rw [←map_smul]; simp
  rw [hs,ht]
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
  ring

theorem one_dimensional_equivalent (B : LinearMap.BilinForm K E) (C : LinearMap.BilinForm K F)
    (hs : B.IsSymm) (ht : C.IsSymm) (hB : B.Nondegenerate) (hC : C.Nondegenerate)
    (hE : finrank K E=1) (hF : finrank K F=1)
    (h : discriminantSign B hs = discriminantSign C ht) : BilinEquivalent B C := by
  obtain ⟨e,he⟩ := one_dimensional_form B hE
  obtain ⟨f,hf⟩ := one_dimensional_form C hF
  have ha : B (e 1) (e 1)≠0 := by
    intro hz
    have he1 : e 1=0 := hB.1 _ (fun y => by
      obtain ⟨s,rfl⟩ := e.surjective y
      rw [he,hz]; simp)
    have : (1:K)=0 := e.injective (he1.trans e.map_zero.symm)
    exact one_ne_zero this
  have hb : C (f 1) (f 1)≠0 := by
    intro hz
    have hf1 : f 1=0 := hC.1 _ (fun y => by
      obtain ⟨s,rfl⟩ := f.surjective y
      rw [hf,hz]; simp)
    exact one_ne_zero (f.injective (hf1.trans f.map_zero.symm))
  have hsa := discriminantSign_isometry (scalarBilin (B (e 1) (e 1))) B
    (scalarBilin_symm _) hs (scalarBilin_nondegenerate _ ha) hB e
    (fun s t => by simpa only [scalarBilin_apply] using he s t)
  have hsb := discriminantSign_isometry (scalarBilin (C (f 1) (f 1))) C
    (scalarBilin_symm _) ht (scalarBilin_nondegenerate _ hb) hC f
    (fun s t => by simpa only [scalarBilin_apply] using hf s t)
  rw [discriminantSign_scalar _ ha] at hsa
  rw [discriminantSign_scalar _ hb] at hsb
  obtain ⟨g,hg⟩ := scalarBilin_equivalent_of_sign _ _ ha hb (hsa.trans (h.trans hsb.symm))
  refine ⟨e.symm.trans (g.trans f), ?_⟩
  intro x y
  change C (f (g (e.symm x))) (f (g (e.symm y))) = B x y
  rw [hf]
  have hg' := hg (e.symm x) (e.symm y)
  simp only [scalarBilin_apply] at hg'
  rw [hg']
  have hx := he (e.symm x) (e.symm y)
  simpa only [e.apply_symm_apply,scalarBilin_apply] using hx.symm

 theorem symmetric_equivalent_of_dim_sign (B : LinearMap.BilinForm K E)
    (C : LinearMap.BilinForm K F) (hs : B.IsSymm) (ht : C.IsSymm)
    (hB : B.Nondegenerate) (hC : C.Nondegenerate) (hK : ringChar K≠2)
    (hd : finrank K E = finrank K F)
    (h : discriminantSign B hs = discriminantSign C ht) : BilinEquivalent B C := by
  suffices ∀ n, finrank K E=n → finrank K F=n → BilinEquivalent B C by exact this _ rfl hd.symm
  intro n hnE hnF
  induction n using Nat.strong_induction_on generalizing E F with
  | h n ih =>
    by_cases hn0 : n=0
    · let e := LinearEquiv.ofFinrankEq E F (hnE.trans hnF.symm)
      have hzero : Subsingleton E := Module.finrank_zero_iff.mp (hnE.trans hn0)
      refine ⟨e,?_⟩
      intro x y
      have hx : x=0 := Subsingleton.elim _ _
      simp only [hx,map_zero,LinearMap.zero_apply]
    by_cases hn1 : n=1
    · exact one_dimensional_equivalent B C hs ht hB hC (hnE.trans hn1) (hnF.trans hn1) h
    have hn2 : 2≤n := by omega
    obtain ⟨x,hx⟩ := symmetric_norm_surjective B hs hB (by omega) hK 1
    obtain ⟨y,hy⟩ := symmetric_norm_surjective C ht hC (by omega) hK 1
    have hx0 : B x x≠0 := hx ▸ one_ne_zero
    have hy0 : C y y≠0 := hy ▸ one_ne_zero
    let P := B.orthogonal (K ∙ x)
    let Q := C.orthogonal (K ∙ y)
    have hp : (B.restrict P).IsSymm := by constructor; intro u v; exact hs.eq _ _
    have hq : (C.restrict Q).IsSymm := by constructor; intro u v; exact ht.eq _ _
    have hP := B.restrict_nondegenerate_orthogonal_spanSingleton hB hs.isRefl hx0
    have hQ := C.restrict_nondegenerate_orthogonal_spanSingleton hC ht.isRefl hy0
    have hdP : finrank K P=n-1 := by have := orthogonal_line_finrank B hx0; dsimp [P]; omega
    have hdQ : finrank K Q=n-1 := by have := orthogonal_line_finrank C hy0; dsimp [Q]; omega
    have hdPQ : finrank K P=finrank K Q := hdP.trans hdQ.symm
    have hsP := discriminantSign_line_complement B hs hB x hx0
    have hsQ := discriminantSign_line_complement C ht hC y hy0
    rw [hx,map_one,one_mul] at hsP
    rw [hy,map_one,one_mul] at hsQ
    have hh : discriminantSign (B.restrict P) hp = discriminantSign (C.restrict Q) hq :=
      hsP.symm.trans (h.trans hsQ)
    obtain ⟨g,hg⟩ := ih (n-1) (by omega) (B.restrict P) (C.restrict Q) hp hq hP hQ hdPQ hh hdP hdQ
    let e := (lineOrthogonalEquiv B x hx0).symm.trans
      (((LinearEquiv.refl K K).prodCongr g).trans (lineOrthogonalEquiv C y hy0))
    refine ⟨e,?_⟩
    intro v w
    let a := (lineOrthogonalEquiv B x hx0).symm v
    let b := (lineOrthogonalEquiv B x hx0).symm w
    change C (lineOrthogonalEquiv C y hy0 (a.1,g a.2))
      (lineOrthogonalEquiv C y hy0 (b.1,g b.2)) = B v w
    rw [lineOrthogonalEquiv_form C ht,hy]
    change 1*a.1*b.1 + (C.restrict Q) (g a.2) (g b.2) = B v w
    rw [hg]
    have he := lineOrthogonalEquiv_form B hs x hx0 a b
    rw [hx] at he
    simpa only [a,b,LinearEquiv.apply_symm_apply,LinearMap.BilinForm.restrict_apply,LinearMap.domRestrict_apply] using he.symm
end Classification
end SidorenkoCounterexample


end



section

namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section LinearMean
variable {K U W : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup W] [Module K W] [Fintype U] [Fintype W]
theorem uniformMean_surjective_linear (f : U →ₗ[K] W) (hf : Function.Surjective f)
    (g : W → ℝ) : uniformMean (g ∘ f) = uniformMean g := by
  classical
  have hcard (y : W) : Fintype.card {x : U // f x = y} = Fintype.card f.ker := by
    simpa [Fintype.card_subtype, LinearMap.mem_ker] using
      AddMonoidHom.card_fiber_eq_of_mem_range f (hf y) (hf 0)
  have hc : Fintype.card U = Fintype.card W * Fintype.card f.ker := by
    simpa only [Nat.card_eq_fintype_card] using surjective_linear_card f hf
  unfold uniformMean
  simp only [Function.comp_def]
  rw [←Fintype.sum_fiberwise f (fun x => g (f x))]
  have hs (y : W) : (∑ x : {x : U // f x=y}, g (f x.val)) =
      (Fintype.card f.ker : ℝ)*g y := by
    have he (x : {x : U // f x=y}) : g (f x.val)=g y := congrArg g x.property
    simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hcard]
  simp only [hs]
  rw [←Finset.mul_sum, hc, Nat.cast_mul]
  have hk : (Fintype.card f.ker : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp
end LinearMean
section Forms
variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
noncomputable instance symForm_fintype : Fintype (SymForm K V) := Fintype.ofFinite _
noncomputable def formSignIndicator (ξ : ℤ) (Q : SymForm K V) : ℝ := by
  classical
  exact if Q.val.Nondegenerate then if discriminantSign Q.val Q.property = ξ then 1 else 0 else 0
noncomputable def formSingularIndicator (Q : SymForm K V) : ℝ := by
  classical
  exact if Q.val.Nondegenerate then 0 else 1

theorem formSignIndicator_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) {ξ : ℤ} (hξ : ξ=1 ∨ ξ = -1) (Q : SymForm K V) :
    formSignIndicator ξ Q = characterSignIndicator ξ (Q.val.toMatrix b).det := by
  by_cases h : Q.val.Nondegenerate
  · simp only [formSignIndicator,h,ite_true,characterSignIndicator,
      discriminantSign_nondegenerate Q.val Q.property h b]
  · have hd : (Q.val.toMatrix b).det=0 := by
      simpa only [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b,not_not] using h
    rcases hξ with rfl | rfl <;>
      simp [formSignIndicator,h,characterSignIndicator,hd]

omit [Fintype K] [FiniteDimensional K V] in
theorem formSingularIndicator_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (Q : SymForm K V) :
    formSingularIndicator Q = if (Q.val.toMatrix b).det=0 then 1 else 0 := by
  simp only [formSingularIndicator,LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b]
  split <;> simp_all

theorem formSignIndicator_nonneg (ξ : ℤ) (Q : SymForm K V) : 0 ≤ formSignIndicator ξ Q := by
  unfold formSignIndicator; split <;> (try split) <;> norm_num

theorem formSignIndicator_le_one (ξ : ℤ) (Q : SymForm K V) : formSignIndicator ξ Q ≤ 1 := by
  unfold formSignIndicator; split <;> (try split) <;> norm_num

omit [Fintype K] [DecidableEq K] [FiniteDimensional K V] in
theorem formSingularIndicator_nonneg (Q : SymForm K V) : 0 ≤ formSingularIndicator Q := by
  unfold formSingularIndicator; split <;> norm_num

theorem formSingularMean_bound :
    uniformMean (formSingularIndicator (K := K) (V := V)) ≤
      (finrank K V : ℝ)/(Fintype.card K : ℝ) := by
  have h := uniformMean_equiv (symFormMatrix K V)
    (fun M : SymMatrix K (finrank K V) => if M.val.det=0 then 1 else 0)
  have he : uniformMean (formSingularIndicator (K := K) (V := V)) =
      symmetricSingularProb (K := K) (finrank K V) := by
    unfold symmetricSingularProb
    rw [←h]; apply uniformMean_congr
    intro Q; exact formSingularIndicator_matrix (Module.finBasis K V) Q
  rw [he]; exact symmetricSingularProb_bound _

theorem formSignMean_error (hK : ringChar K ≠ 2) (hd : 0 < finrank K V)
    {ξ : ℤ} (hξ : ξ=1 ∨ ξ = -1) :
    |uniformMean (formSignIndicator (K := K) (V := V) ξ)-1/2| ≤
      (finrank K V : ℝ)/(Fintype.card K : ℝ) := by
  have h := uniformMean_equiv (symFormMatrix K V)
    (fun M : SymMatrix K (finrank K V) => characterSignIndicator ξ M.val.det)
  have he : uniformMean (formSignIndicator (K := K) (V := V) ξ) =
      symmetricSignProb (K := K) (finrank K V) ξ := by
    unfold symmetricSignProb
    rw [←h]; apply uniformMean_congr
    intro Q; exact formSignIndicator_matrix (Module.finBasis K V) hξ Q
  rw [he]; exact symmetricSignProb_error _ hd hK hξ

variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
omit [DecidableEq K] in
theorem uniformMean_restrict (f : W →ₗ[K] V) (hf : Function.Injective f)
    (g : SymForm K W → ℝ) :
    uniformMean (fun Q : SymForm K V => g (symFormPull f Q)) = uniformMean g :=
  uniformMean_surjective_linear (symFormPull f) (symFormPull_surjective f hf) g
end Forms
end SidorenkoCounterexample

end

end OAI
