import OAI.Combinatorics.Sidorenko.Tail

namespace OAI


section




namespace SidorenkoCounterexample
open Module LinearMap

section Forms
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The bilinear form induced on the quotient by its radical. -/
def radicalQuotientForm (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    LinearMap.BilinForm K (V ⧸ B.ker) :=
  LinearMap.IsRefl.liftQ₂ B B.ker hB.isRefl le_rfl

@[simp] theorem radicalQuotientForm_mk (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (x y : V) : radicalQuotientForm B hB
      (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = B x y := rfl

/-- Passing to the radical quotient really gives a nondegenerate form. -/
theorem radicalQuotientForm_nondegenerate [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    (radicalQuotientForm B hB).Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mpr
  apply bot_unique
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    apply (Submodule.Quotient.mk_eq_zero B.ker).mpr
    apply LinearMap.mem_ker.mpr
    ext y
    have h := congrArg (fun f => f (Submodule.Quotient.mk y)) hx
    exact h

theorem radicalQuotientForm_isSymm (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    (radicalQuotientForm B hB).IsSymm := by
  constructor
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y => exact hB.eq x y

theorem form_isSymm_neg (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    (-B).IsSymm := by
  constructor
  intro x y
  change -(B x y) = -(B y x)
  rw [hB.eq x y]

def radicalNegEquiv (B : LinearMap.BilinForm K V) :
    (V ⧸ (-B).ker) ≃ₗ[K] (V ⧸ B.ker) :=
  Submodule.quotEquivOfEq _ _ (LinearMap.ker_neg B)

theorem radicalQuotientForm_neg (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (x y : V ⧸ (-B).ker) :
    radicalQuotientForm (-B) (form_isSymm_neg B hB) x y =
      -(radicalQuotientForm B hB (radicalNegEquiv B x) (radicalNegEquiv B y)) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y => rfl

variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]

/-- Determinant character of the nondegenerate radical quotient, including
rank zero (where the empty determinant is one). -/
noncomputable def discriminantSign (B : LinearMap.BilinForm K V) (hB : B.IsSymm) : ℤ :=
  quadraticChar K ((radicalQuotientForm B hB).toMatrix
    (Module.finBasis K (V ⧸ B.ker))).det

theorem discriminantSign_ne_zero (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    discriminantSign B hB ≠ 0 := by
  apply mt quadraticChar_eq_zero_iff.mp
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero _).mp
    (radicalQuotientForm_nondegenerate B hB)

theorem discriminantSign_sq (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    discriminantSign B hB ^ 2 = 1 := by
  apply quadraticChar_sq_one
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero _).mp
    (radicalQuotientForm_nondegenerate B hB)

theorem discriminantSign_cases (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    discriminantSign B hB = 1 ∨ discriminantSign B hB = -1 := by
  apply quadraticChar_dichotomy
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero _).mp
    (radicalQuotientForm_nondegenerate B hB)

omit [FiniteDimensional K V] in
/-- The determinant character is independent of a basis. -/
theorem determinant_character_basis_independent {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b c : Basis ι K V) (B : LinearMap.BilinForm K V) :
    quadraticChar K (B.toMatrix b).det = quadraticChar K (B.toMatrix c).det := by
  have hu : (b.toMatrix c).det ≠ 0 := (b.isUnit_det c).ne_zero
  rw [← B.toMatrix_mul_basis_toMatrix b c, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, map_mul, map_mul]
  have hsq := quadraticChar_sq_one (F := K) hu
  linear_combination -(quadraticChar K (B.toMatrix b).det) * hsq

omit [FiniteDimensional K V] in
/-- Basis invariance also allows unrelated finite indexing types. -/
theorem determinant_character_basis_independent_indices {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Basis ι K V) (c : Basis κ K V) (B : LinearMap.BilinForm K V) :
    quadraticChar K (B.toMatrix b).det = quadraticChar K (B.toMatrix c).det := by
  classical
  let e := b.indexEquiv c
  have h : B.toMatrix (b.reindex e) = Matrix.reindex e e (B.toMatrix b) := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply, Matrix.reindex_apply]
  calc
    quadraticChar K (B.toMatrix b).det =
        quadraticChar K (B.toMatrix (b.reindex e)).det := by
      rw [h, Matrix.det_reindex_self]
    _ = quadraticChar K (B.toMatrix c).det :=
      determinant_character_basis_independent _ _ _

/-- The definition can be evaluated in any basis of the radical quotient. -/
theorem discriminantSign_eq (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K (V ⧸ B.ker)) :
    discriminantSign B hB = quadraticChar K ((radicalQuotientForm B hB).toMatrix b).det :=
  determinant_character_basis_independent_indices _ _ _

/-- Negation changes the intrinsic sign by the character of (-1)^rank. -/
theorem discriminantSign_neg (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    discriminantSign (-B) (form_isSymm_neg B hB) =
      quadraticChar K ((-1 : K) ^ finrank K (V ⧸ B.ker)) * discriminantSign B hB := by
  classical
  let b := Module.finBasis K (V ⧸ B.ker)
  rw [discriminantSign_eq (-B) (form_isSymm_neg B hB)
    (b.map (radicalNegEquiv B).symm)]
  have hm : (radicalQuotientForm (-B) (form_isSymm_neg B hB)).toMatrix
      (b.map (radicalNegEquiv B).symm) = -(radicalQuotientForm B hB).toMatrix b := by
    ext i j
    simp only [LinearMap.BilinForm.toMatrix_apply, Basis.map_apply, Matrix.neg_apply]
    rw [radicalQuotientForm_neg B hB]
    simp only [LinearEquiv.apply_symm_apply]
  rw [hm, Matrix.det_neg, map_mul, Fintype.card_fin]
  rfl

end Forms
section Pullback
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

 theorem pullback_isSymm (B : LinearMap.BilinForm K W) (hB : B.IsSymm)
    (f : V →ₗ[K] W) : LinearMap.BilinForm.IsSymm (B.compl₁₂ f f) := by
  constructor
  intro x y
  exact hB.eq (f x) (f y)

theorem pullback_ker (B : LinearMap.BilinForm K W) (hB : B.Nondegenerate)
    (f : V →ₗ[K] W) (hf : Function.Surjective f) :
    (B.compl₁₂ f f).ker = f.ker := by
  ext x
  simp only [LinearMap.mem_ker]
  constructor
  · intro hx
    apply hB.1
    intro y
    obtain ⟨z, rfl⟩ := hf y
    exact congrArg (fun g => g z) hx
  · intro hx
    ext y
    simp [hx]

noncomputable def pullbackQuotientEquiv (B : LinearMap.BilinForm K W)
    (hB : B.Nondegenerate) (f : V →ₗ[K] W) (hf : Function.Surjective f) :
    (V ⧸ (B.compl₁₂ f f).ker) ≃ₗ[K] W :=
  (Submodule.quotEquivOfEq _ _ (pullback_ker B hB f hf)).trans
    (f.quotKerEquivOfSurjective hf)

@[simp] theorem pullbackQuotientEquiv_mk (B : LinearMap.BilinForm K W)
    (hB : B.Nondegenerate) (f : V →ₗ[K] W) (hf : Function.Surjective f) (x : V) :
    pullbackQuotientEquiv B hB f hf (Submodule.Quotient.mk x) = f x := rfl

theorem pullbackQuotientForm (B : LinearMap.BilinForm K W)
    (hBs : B.IsSymm) (hB : B.Nondegenerate)
    (f : V →ₗ[K] W) (hf : Function.Surjective f)
    (x y : V ⧸ (B.compl₁₂ f f).ker) :
    radicalQuotientForm (B.compl₁₂ f f) (pullback_isSymm B hBs f) x y =
      B (pullbackQuotientEquiv B hB f hf x) (pullbackQuotientEquiv B hB f hf y) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y => rfl

variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]

/-- Pulling a nondegenerate form back along a surjection does not change
its intrinsic determinant character. This covers the rank-k matrix
representation P*R*Pᵀ used in the signed layer counts. -/
theorem discriminantSign_pullback (B : LinearMap.BilinForm K W)
    (hBs : B.IsSymm) (hB : B.Nondegenerate)
    (f : V →ₗ[K] W) (hf : Function.Surjective f)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K W) :
    discriminantSign (B.compl₁₂ f f) (pullback_isSymm B hBs f) =
      quadraticChar K (B.toMatrix b).det := by
  classical
  let e := pullbackQuotientEquiv B hB f hf
  rw [discriminantSign_eq _ _ (b.map e.symm)]
  congr 2
  ext i j
  simp only [LinearMap.BilinForm.toMatrix_apply, Basis.map_apply]
  rw [pullbackQuotientForm B hBs hB f hf]
  simp only [e, LinearEquiv.apply_symm_apply]

end Pullback
section MatrixForms
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem matrix_bilin_eval (M : Matrix n n K) (x y : n → K) :
    M.toBilin' x y = (M.transpose.mulVec x) ⬝ᵥ y := by
  rw [Matrix.toBilin'_apply]
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem matrix_bilin_ker (M : Matrix n n K) :
    M.toBilin'.ker = M.transpose.toLin'.ker := by
  ext x
  simp only [LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply,
    matrix_bilin_eval, Matrix.toLin'_apply]
  exact dotProduct_eq_zero_iff

/-- The rank of the intrinsic quotient is the usual matrix rank. -/
theorem matrix_radical_quotient_rank (M : Matrix n n K) :
    finrank K ((n → K) ⧸ M.toBilin'.ker) = M.rank := by
  have h₁ := M.toBilin'.ker.finrank_quotient_add_finrank
  have h₂ := M.transpose.toLin'.finrank_range_add_finrank_ker
  rw [matrix_bilin_ker] at h₁
  have hr : finrank K M.transpose.toLin'.range = M.transpose.rank := rfl
  rw [hr, Matrix.rank_transpose] at h₂
  rw [matrix_bilin_ker]
  omega

theorem matrix_rank_neg (M : Matrix n n K) : (-M).rank = M.rank := by
  change finrank K (Matrix.toLin' (-M)).range = finrank K (Matrix.toLin' M).range
  rw [map_neg, LinearMap.range_neg]

end MatrixForms
end SidorenkoCounterexample

namespace SidorenkoCounterexample


def MainClaim : Prop := ∃ n : ℕ, 0 < n ∧ ∃ G : SimpleGraph (Fin n),
    (∃ u v, G.Adj u v) ∧ homDensity H G < (edgeDensity G) ^ 66


end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module

section FiniteLayer
variable (K : Type*) [Field K] (D : ℕ)

variable [Fintype K] [DecidableEq K]
noncomputable instance : Fintype (SymMatrix K D) := Fintype.ofFinite _

noncomputable def matrixSign (Z : SymMatrix K D) : ℤ :=
  discriminantSign Z.val.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr Z.property)

/-- A nonsingular r-form occurs as a rank-r symmetric D-matrix, with its
intrinsic sign unchanged. -/
theorem exists_matrix_of_nonsingular {r : ℕ} (hrD : r ≤ D)
    (R : Matrix (Fin r) (Fin r) K) (hRs : R.IsSymm) (hR : R.det ≠ 0) :
    ∃ Z : SymMatrix K D, Z.val.rank = r ∧
      matrixSign K D Z = quadraticChar K R.det := by
  classical
  let f : (Fin D → K) →ₗ[K] (Fin r → K) :=
    LinearMap.funLeft K K (Fin.castLE hrD)
  have hf : Function.Surjective f :=
    LinearMap.funLeft_surjective_of_injective K K _ (Fin.castLE_injective hrD)
  have hbs : R.toBilin'.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr hRs
  have hb : R.toBilin'.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hR
  let B : LinearMap.BilinForm K (Fin D → K) := R.toBilin'.compl₁₂ f f
  have hB : B.IsSymm := pullback_isSymm _ hbs f
  let Z : SymMatrix K D := ⟨B.toMatrix',
    LinearMap.BilinForm.isSymm_toMatrix'_iff_isSymm.mpr hB⟩
  have hz : Z.val.toBilin' = B := Matrix.toBilin'_toMatrix' B
  refine ⟨Z, ?_, ?_⟩
  · rw [← matrix_radical_quotient_rank, hz]
    calc
      finrank K ((Fin D → K) ⧸ B.ker) = finrank K (Fin r → K) :=
        (pullbackQuotientEquiv R.toBilin' hb f hf).finrank_eq
      _ = r := by simp
  · unfold matrixSign
    simp only [hz]
    have he := discriminantSign_pullback R.toBilin' hbs hb f hf
      (Pi.basisFun K (Fin r))
    convert he using 1
    exact congrArg (fun M : Matrix (Fin r) (Fin r) K => quadraticChar K M.det)
      (LinearMap.BilinForm.toMatrix'_toBilin' R).symm

/-- The two positive-rank layers used in the manuscript are nonempty. -/
theorem exists_matrix_rank_sign {r : ℕ} (hr : 0 < r) (hrD : r ≤ D)
    (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    ∃ Z : SymMatrix K D, Z.val.rank = r ∧ matrixSign K D Z = ξ := by
  classical
  have ha : ∃ a : K, a ≠ 0 ∧ quadraticChar K a = ξ := by
    rcases hξ with rfl | rfl
    · exact ⟨1, one_ne_zero, map_one _⟩
    · obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one (F := K) hK
      refine ⟨a, ?_, ha⟩
      intro haz
      simp [haz] at ha
  obtain ⟨a, ha, hax⟩ := ha
  let i₀ : Fin r := ⟨0, hr⟩
  let R : Matrix (Fin r) (Fin r) K :=
    Matrix.diagonal fun i => if i = i₀ then a else 1
  have hdet : R.det = a := by
    simp [R, Matrix.det_diagonal]
  obtain ⟨Z, hz, hs⟩ := exists_matrix_of_nonsingular K D hrD R
    (Matrix.isSymm_diagonal _) (hdet ▸ ha)
  exact ⟨Z, hz, hs.trans (hdet ▸ hax)⟩

noncomputable def signedLayer (r : ℕ) (ξ : ℤ) : Finset (SymMatrix K D) := by
  classical
  exact Finset.univ.filter fun Z => Z.val.rank = r ∧ matrixSign K D Z = ξ

noncomputable def layerMass (r : ℕ) (ξ : ℤ) : ℝ :=
  (signedLayer K D r ξ).card / (Fintype.card (SymMatrix K D) : ℝ)

noncomputable def rankKernel (r : ℕ) (ξ : ℤ) (Z : SymMatrix K D) : ℝ := by
  classical
  exact if Z ∈ signedLayer K D r ξ then (layerMass K D r ξ)⁻¹ else 0

theorem matrixSign_neg (Z : SymMatrix K D) :
    matrixSign K D (-Z) = quadraticChar K ((-1 : K) ^ Z.val.rank) *
      matrixSign K D Z := by
  have hs := discriminantSign_neg Z.val.toBilin'
    (Matrix.isSymm_toBilin'_iff_isSymm.mpr Z.property)
  simpa only [matrixSign, Submodule.coe_neg, map_neg, matrix_radical_quotient_rank] using hs

@[simp] theorem mem_signedLayer (r : ℕ) (ξ : ℤ) (Z : SymMatrix K D) :
    Z ∈ signedLayer K D r ξ ↔ Z.val.rank = r ∧ matrixSign K D Z = ξ := by
  classical
  simp [signedLayer]

theorem signedLayer_nonempty {r : ℕ} (hr : 0 < r) (hrD : r ≤ D)
    (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    (signedLayer K D r ξ).Nonempty := by
  obtain ⟨Z, hz, hs⟩ := exists_matrix_rank_sign K D hr hrD hK hξ
  exact ⟨Z, (mem_signedLayer K D r ξ Z).mpr ⟨hz, hs⟩⟩

theorem layerMass_pos {r : ℕ} (hr : 0 < r) (hrD : r ≤ D)
    (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    0 < layerMass K D r ξ := by
  apply div_pos
  · exact_mod_cast (signedLayer_nonempty K D hr hrD hK hξ).card_pos
  · exact_mod_cast Fintype.card_pos (α := SymMatrix K D)

theorem rankKernel_nonneg (r : ℕ) (ξ : ℤ) (Z : SymMatrix K D) :
    0 ≤ rankKernel K D r ξ Z := by
  classical
  unfold rankKernel layerMass
  split_ifs <;> positivity

theorem neg_mem_signedLayer (r : ℕ) (ξ : ℤ) (Z : SymMatrix K D) :
    -Z ∈ signedLayer K D r ξ ↔
      Z ∈ signedLayer K D r (quadraticChar K ((-1 : K) ^ r) * ξ) := by
  rw [mem_signedLayer, mem_signedLayer]
  have hc := quadraticChar_sq_one (F := K) (pow_ne_zero r (neg_ne_zero.mpr one_ne_zero))
  simp only [Submodule.coe_neg, matrix_rank_neg, matrixSign_neg]
  constructor
  · rintro ⟨hz, hs⟩
    rw [hz] at hs
    refine ⟨hz, ?_⟩
    linear_combination quadraticChar K ((-1 : K) ^ r) * hs -
      matrixSign K D Z * hc
  · rintro ⟨hz, hs⟩
    refine ⟨hz, ?_⟩
    rw [hz, hs]
    linear_combination ξ * hc

theorem signedLayer_card_neg (r : ℕ) (ξ : ℤ) :
    (signedLayer K D r ξ).card =
      (signedLayer K D r (quadraticChar K ((-1 : K) ^ r) * ξ)).card := by
  classical
  apply Finset.card_bij (fun Z _ => -Z)
  · intro Z hZ
    exact (neg_mem_signedLayer K D r ξ (-Z)).mp (by simpa using hZ)
  · intro Z _ W _ h
    exact neg_injective h
  · intro Z hZ
    exact ⟨-Z, (neg_mem_signedLayer K D r ξ Z).mpr hZ, neg_neg Z⟩

theorem rankKernel_neg (r : ℕ) (ξ : ℤ) (Z : SymMatrix K D) :
    rankKernel K D r ξ (-Z) =
      rankKernel K D r (quadraticChar K ((-1 : K) ^ r) * ξ) Z := by
  classical
  unfold rankKernel
  simp only [neg_mem_signedLayer]
  congr 1
  unfold layerMass
  rw [signedLayer_card_neg]

end FiniteLayer

/-- Expectation under the uniform law on a finite type. -/
noncomputable def uniformMean {A : Type*} [Fintype A] (f : A → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card A

theorem uniformMean_rankKernel {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (D r : ℕ) (hr : 0 < r) (hrD : r ≤ D) (hK : ringChar K ≠ 2)
    {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    uniformMean (rankKernel K D r ξ) = 1 := by
  classical
  have hs := (signedLayer_nonempty K D hr hrD hK hξ).card_pos
  have hc := Fintype.card_pos (α := SymMatrix K D)
  unfold uniformMean rankKernel
  rw [Finset.sum_ite_mem]
  simp only [Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  unfold layerMass
  have hs' : ((signedLayer K D r ξ).card : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hc' : (Fintype.card (SymMatrix K D) : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  field_simp

abbrev OddPrime := {q : ℕ // q.Prime ∧ q ≠ 2}
instance (q : OddPrime) : Fact q.val.Prime := ⟨q.property.1⟩

def primeInfinity : Filter OddPrime := Filter.comap Subtype.val Filter.atTop

def corners : Finset (Fin 13 × Fin 22) :=
  Finset.univ.filter fun c => c.1 ∈ faces c.2

def modelPointPairs : Finset (Finset (Fin 13)) :=
  Finset.univ.biUnion fun j => (faces j).powersetCard 2

abbrev ModelPair := {e : Finset (Fin 13) // e ∈ modelPointPairs}

noncomputable def layerCorrelation (D : ℕ) (q : OddPrime)
    (B : Finset (Fin 13 × Fin 22)) (ξ : Fin 13 × Fin 22 → ℤ) : ℝ :=
  uniformMean fun xy : (Fin 13 → SymMatrix (ZMod q.val) D) ×
      (Fin 22 → SymMatrix (ZMod q.val) D) =>
    ∏ c ∈ B, rankKernel (ZMod q.val) D (D / 2) (ξ c) (xy.1 c.1 - xy.2 c.2)

noncomputable def signModelCorrelation (D : ℕ) (q : OddPrime)
    (B : Finset (Fin 13 × Fin 22)) (ξ : Fin 13 × Fin 22 → ℤ) : ℝ := by
  classical
  let c₀ : ℝ := quadraticChar (ZMod q.val) ((-1) ^ (D / 2))
  exact uniformMean fun η : ModelPair → Bool =>
    ∏ j : Fin 22, ∏ e : ModelPair,
      if e.val ⊆ faces j ∧ (∀ i ∈ e.val, (i,j) ∈ B) then
        1 + c₀ * (if η e then 1 else -1) * ∏ i ∈ e.val, (ξ (i,j) : ℝ)
      else 1




def RankLayerLimit : Prop := ∃ D₀ : ℕ, 0 < D₀ ∧
  ∀ D : ℕ, D₀ ≤ D → Even D →
    ∀ B : Finset (Fin 13 × Fin 22), B ⊆ corners →
      ∀ ξ : Fin 13 × Fin 22 → ℤ, (∀ c ∈ B, ξ c = 1 ∨ ξ c = -1) →
        Filter.Tendsto (fun q : OddPrime =>
          layerCorrelation D q B ξ - signModelCorrelation D q B ξ)
          primeInfinity (nhds 0)

end SidorenkoCounterexample





namespace SidorenkoCounterexample
open Module LinearMap

private theorem range_sup_complement {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (f : V →ₗ[K] V) :
    LinearMap.range f ⊔ LinearMap.range (LinearMap.id - f) = ⊤ := by
  apply top_unique
  intro x _
  exact Submodule.mem_sup.mpr ⟨f x, ⟨x, rfl⟩, x-f x, ⟨x, rfl⟩, by abel⟩

/-- Equality in the dimension subadditivity for an operator and its complement
is equivalent to idempotence. -/
theorem complementary_rank_iff {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (f : V →ₗ[K] V) :
    finrank K (LinearMap.range f) + finrank K (LinearMap.range (LinearMap.id-f)) =
      finrank K V ↔ IsIdempotentElem f := by
  constructor
  · intro h
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.range f) (LinearMap.range (LinearMap.id-f))
    rw [range_sup_complement, finrank_top] at hsum
    have hz : finrank K (LinearMap.range f ⊓ LinearMap.range (LinearMap.id-f) :
        Submodule K V) = 0 := by omega
    have hinf := Submodule.finrank_eq_zero.mp hz
    change f*f = f
    ext x
    have hx₁ : f x-f (f x) ∈ LinearMap.range f := ⟨x-f x, map_sub f x (f x)⟩
    have hx₂ : f x-f (f x) ∈ LinearMap.range (LinearMap.id-f) := ⟨f x, rfl⟩
    have hx : f x-f (f x) ∈ (⊥ : Submodule K V) := by
      rw [← hinf]
      exact ⟨hx₁, hx₂⟩
    have hzero : f x-f (f x) = 0 := hx
    exact (sub_eq_zero.mp hzero).symm
  · intro h
    rw [← h.ker_eq_range]
    exact f.finrank_range_add_finrank_ker

/-- Matrix version of complementary_rank_iff. -/
theorem matrix_complementary_rank_iff {K n : Type*} [Field K] [Fintype n]
    [DecidableEq n] (P : Matrix n n K) :
    P.rank + (1-P).rank = Fintype.card n ↔ P*P=P := by
  have h := complementary_rank_iff (Matrix.toLin' P)
  have hdim : finrank K (n → K) = Fintype.card n := Module.finrank_fintype_fun_eq_card K
  rw [← Matrix.toLin'_one, ← map_sub Matrix.toLin'] at h
  change P.rank+(1-P).rank = finrank K (n → K) ↔ IsIdempotentElem (Matrix.toLin' P) at h
  rw [hdim] at h
  rw [h]
  change (Matrix.toLin' P).comp (Matrix.toLin' P) = Matrix.toLin' P ↔ _
  rw [← Matrix.toLin'_mul, Matrix.toLin'.injective.eq_iff]

/-- Exact complementary-images equivalence in the main proof. Nonsingularity
is determinant ≠ 0; no characteristic or symmetry hypothesis is discarded
from an application, since the equivalence holds without those restrictions. -/
theorem half_rank_projection {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (r : ℕ) (hdim : Fintype.card n = 2*r) (A B : Matrix n n K)
    (hB : B.det ≠ 0) (hA : A.rank = r) :
    (B-A).rank = r ↔ A*B⁻¹*A=A := by
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  have hBi : B⁻¹.det ≠ 0 := by simpa [Matrix.det_nonsing_inv] using inv_ne_zero hB
  have hPr : (A*B⁻¹).rank = r := (Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hBi).trans hA
  have hQr : (1-A*B⁻¹).rank = (B-A).rank := by
    rw [show 1-A*B⁻¹ = (B-A)*B⁻¹ by rw [sub_mul, Matrix.mul_nonsing_inv B hu]]
    exact Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hBi
  have hmain := matrix_complementary_rank_iff (A*B⁻¹)
  rw [hPr, hQr, hdim] at hmain
  have hsum : r+(B-A).rank=2*r ↔ (B-A).rank=r := by omega
  rw [hsum] at hmain
  rw [hmain]
  constructor
  · intro h
    have hm := congrArg (fun M => M*B) h
    simpa only [Matrix.mul_assoc, Matrix.nonsing_inv_mul B hu, Matrix.mul_one] using hm
  · intro h
    calc
      (A*B⁻¹)*(A*B⁻¹) = (A*B⁻¹*A)*B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = A*B⁻¹ := by rw [h]

end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Border
variable {K : Type*} [Field K]
def borderIndex (n : ℕ) : Fin (n+1) ≃ Fin n ⊕ PUnit.{1} :=
  (finSuccEquiv n).trans (Equiv.optionEquivSumPUnit (Fin n))

def borderRaw {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (z : Fin n → K) (a : K) :
    Matrix (Fin n ⊕ PUnit.{1}) (Fin n ⊕ PUnit.{1}) K :=
  Matrix.fromBlocks M (Matrix.of fun i _ => z i) (Matrix.of fun _ j => z j) (Matrix.of fun _ _ => a)

def symmetricBorder {n : ℕ} (M : SymMatrix K n) (z : Fin n → K) (a : K) : SymMatrix K (n+1) :=
  ⟨(borderRaw M.val z a).submatrix (borderIndex n) (borderIndex n), by
    ext i j
    change borderRaw M.val z a (borderIndex n j) (borderIndex n i) =
      borderRaw M.val z a (borderIndex n i) (borderIndex n j)
    cases borderIndex n i with
    | inl i => cases borderIndex n j with
      | inl j => exact M.property.apply i j
      | inr j => rfl
    | inr i => cases borderIndex n j <;> rfl⟩

def borderUnpack {n : ℕ} (M : SymMatrix K (n+1)) :
    SymMatrix K n × (Fin n → K) × K :=
  (⟨M.val.submatrix (fun i => (borderIndex n).symm (.inl i))
      (fun i => (borderIndex n).symm (.inl i)), by
      ext i j; exact M.property.apply _ _⟩,
   fun i => M.val ((borderIndex n).symm (.inl i)) ((borderIndex n).symm (.inr PUnit.unit)),
   M.val ((borderIndex n).symm (.inr PUnit.unit)) ((borderIndex n).symm (.inr PUnit.unit)))

def symmetricBorderEquiv (n : ℕ) :
    SymMatrix K (n+1) ≃ SymMatrix K n × (Fin n → K) × K where
  toFun := borderUnpack
  invFun x := symmetricBorder x.1 x.2.1 x.2.2
  left_inv M := by
    apply Subtype.ext
    ext i j
    obtain ⟨i,rfl⟩ := (borderIndex n).symm.surjective i
    obtain ⟨j,rfl⟩ := (borderIndex n).symm.surjective j
    cases i with
    | inl i => cases j with
      | inl j => simp [symmetricBorder,borderUnpack,borderRaw,Matrix.fromBlocks]
      | inr j => cases j; simp [symmetricBorder,borderUnpack,borderRaw,Matrix.fromBlocks]
    | inr i =>
      cases i
      cases j with
      | inl j =>
        simpa [symmetricBorder,borderUnpack,borderRaw,Matrix.fromBlocks] using
          (M.property.apply ((borderIndex n).symm (.inr PUnit.unit))
            ((borderIndex n).symm (.inl j)))
      | inr j => cases j; simp [symmetricBorder,borderUnpack,borderRaw,Matrix.fromBlocks]
  right_inv x := by
    rcases x with ⟨M,z,a⟩
    apply Prod.ext
    · apply Subtype.ext; ext i j; simp [symmetricBorder,borderUnpack,borderRaw,Matrix.fromBlocks]
    · apply Prod.ext
      · funext i; simp [symmetricBorder,borderUnpack,borderRaw,Matrix.fromBlocks]
      · simp [symmetricBorder,borderUnpack,borderRaw,Matrix.fromBlocks]

 theorem symmetricBorder_det {n : ℕ} (M : SymMatrix K n) (z : Fin n → K) (a : K)
    (hM : M.val.det ≠ 0) :
    (symmetricBorder M z a).val.det = M.val.det * (a - z ⬝ᵥ (M.val⁻¹.mulVec z)) := by
  classical
  let := Matrix.invertibleOfIsUnitDet M.val (isUnit_iff_ne_zero.mpr hM)
  rw [symmetricBorder,Matrix.det_submatrix_equiv_self]
  dsimp only [borderRaw]
  rw [Matrix.det_fromBlocks₁₁]
  congr 1
  rw [Matrix.det_unique]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply,
    Matrix.invOf_eq_nonsing_inv, dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

end Border
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open scoped BigOperators
section Mean
variable {A B : Type*} [Fintype A] [Fintype B]
theorem uniformMean_congr {f g : A → ℝ} (h : ∀ a, f a = g a) :
    uniformMean f = uniformMean g := by
  unfold uniformMean
  congr 1
  exact Finset.sum_congr rfl fun a _ => h a

theorem uniformMean_equiv (e : A ≃ B) (f : B → ℝ) :
    uniformMean (f ∘ e) = uniformMean f := by
  unfold uniformMean
  dsimp only [Function.comp_def]
  rw [Fintype.card_congr e, Equiv.sum_comp e f]

theorem uniformMean_prod (f : A × B → ℝ) :
    uniformMean f = uniformMean fun a => uniformMean fun b => f (a,b) := by
  unfold uniformMean
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  simp_rw [← Finset.sum_div]
  ring

theorem uniformMean_const [Nonempty A] (c : ℝ) : uniformMean (fun _ : A => c) = c := by
  simp [uniformMean, (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := A)) :
    (Fintype.card A : ℝ) ≠ 0)]

theorem uniformMean_add (f g : A → ℝ) :
    uniformMean (fun a => f a + g a) = uniformMean f + uniformMean g := by
  simp [uniformMean, Finset.sum_add_distrib, add_div]

theorem uniformMean_sub (f g : A → ℝ) :
    uniformMean (fun a => f a - g a) = uniformMean f - uniformMean g := by
  simp [uniformMean, Finset.sum_sub_distrib, sub_div]

theorem uniformMean_mul (c : ℝ) (f : A → ℝ) :
    uniformMean (fun a => c * f a) = c * uniformMean f := by
  simp [uniformMean, ← Finset.mul_sum, mul_div_assoc]

theorem uniformMean_mono {f g : A → ℝ} (h : ∀ a, f a ≤ g a) :
    uniformMean f ≤ uniformMean g := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum fun a _ => h a

theorem uniformMean_nonneg {f : A → ℝ} (h : ∀ a, 0 ≤ f a) : 0 ≤ uniformMean f :=
  div_nonneg (Finset.sum_nonneg fun a _ => h a) (Nat.cast_nonneg _)

theorem abs_uniformMean_le (f : A → ℝ) :
    |uniformMean f| ≤ uniformMean fun a => |f a| := by
  unfold uniformMean
  rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ Fintype.card A from Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs ..) (Nat.cast_nonneg _)

theorem uniformMean_bound [Nonempty A] {f : A → ℝ} {c : ℝ} (h : ∀ a, f a ≤ c) :
    uniformMean f ≤ c := by
  simpa only [uniformMean_const] using uniformMean_mono h

theorem uniformMean_indicator (p : A → Prop) [DecidablePred p] :
    uniformMean (fun a => if p a then 1 else 0) =
      (Fintype.card {a // p a} : ℝ) / Fintype.card A := by
  simp [uniformMean, Fintype.card_subtype, Finset.sum_boole]
end Mean
end SidorenkoCounterexample

end

end OAI
