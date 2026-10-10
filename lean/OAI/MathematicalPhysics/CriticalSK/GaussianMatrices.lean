import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace
open Module
namespace CriticalSK


section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def alignIsometry (e v : E) : E ≃ₗᵢ[ℝ] E :=
  Submodule.reflection (ℝ ∙ (v - ‖v‖ • e))ᗮ

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma alignIsometry_apply (e v x : E) :
    alignIsometry e v x = x -
      (2 * (inner ℝ (v - ‖v‖ • e) x / ‖v - ‖v‖ • e‖ ^ 2)) • (v - ‖v‖ • e) := by
  rw [alignIsometry, Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq, neg_sub, two_smul]
  rw [two_mul, add_smul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma alignIsometry_align (e v : E) (he : ‖e‖ = 1) :
    alignIsometry e v v = ‖v‖ • e := by
  apply Submodule.reflection_sub
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), he, mul_one]

lemma alignIsometry_measurable (e : E) :
    Measurable (fun p : E × E => alignIsometry e p.1 p.2) := by
  simp_rw [alignIsometry_apply]
  fun_prop

lemma random_isometry_gaussian_preserving {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (U : Ω → E ≃ₗᵢ[ℝ] E)
    (hU : Measurable (fun p : Ω × E => U p.1 p.2)) :
    MeasurePreserving (fun p : Ω × E => (p.1, U p.1 p.2))
      (μ.prod (stdGaussian E)) (μ.prod (stdGaussian E)) := by
  exact (MeasurePreserving.id μ).skew_product (g := fun ω x => U ω x)
    (μc := stdGaussian E) (μd := stdGaussian E) hU
    (Filter.Eventually.of_forall (fun ω => stdGaussian_map (U ω)))

lemma exposed_gaussian_alignment (e : E) :
    MeasurePreserving (fun p : E × E => (p.1, alignIsometry e p.1 p.2))
      ((stdGaussian E).prod (stdGaussian E)) ((stdGaussian E).prod (stdGaussian E)) :=
  random_isometry_gaussian_preserving _ _ (alignIsometry_measurable e)

lemma covariance_inner_stdGaussian (v w : E) :
    cov[fun x => inner ℝ v x, fun x => inner ℝ w x; stdGaussian E] = inner ℝ v w := by
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian]
  rfl

lemma inner_stdGaussian_law (v : E) :
    (stdGaussian E).map (fun x => inner ℝ v x) =
      gaussianReal 0 (‖v‖ ^ 2).toNNReal := by
  have hG : HasGaussianLaw (fun x : E => inner ℝ v x) (stdGaussian E) :=
    IsGaussian.hasGaussianLaw_id.map_fun (innerSL ℝ v)
  rw [hG.map_eq_gaussianReal]
  congr 1
  · exact integral_strongDual_stdGaussian (innerSL ℝ v)
  · rw [← covariance_self (by fun_prop), covariance_inner_stdGaussian, real_inner_self_eq_norm_sq]

lemma gaussian_orthogonal_independent {κ : Type*} [Fintype κ] (v : κ → E)
    (hv : Pairwise (fun i j => inner ℝ (v i) (v j) = 0)) :
    iIndepFun (fun i x => inner ℝ (v i) x) (stdGaussian E) := by
  have hG : HasGaussianLaw (fun x : E => fun i => inner ℝ (v i) x) (stdGaussian E) :=
    IsGaussian.hasGaussianLaw_id.map_fun (ContinuousLinearMap.pi (fun i => innerSL ℝ (v i)))
  apply hG.iIndepFun_of_covariance_eq_zero
  intro i j hij
  rw [covariance_inner_stdGaussian]
  exact hv hij

variable {ι : Type*} [Fintype ι]

abbrev GaussianMatrix (ι : Type*) [Fintype ι] :=
  PiLp 2 (fun _ : ι => EuclideanSpace ℝ ι)

def transposeGaussianMatrix : GaussianMatrix ι ≃ₗᵢ[ℝ] GaussianMatrix ι where
  toFun A := WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => A j i))
  invFun A := WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => A j i))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' A := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_comm

@[simp] lemma transposeGaussianMatrix_apply (A : GaussianMatrix ι) (i j : ι) :
    transposeGaussianMatrix A i j = A j i := rfl

def rowIsometry (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    GaussianMatrix ι ≃ₗᵢ[ℝ] GaussianMatrix ι :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : ι => U)

@[simp] lemma rowIsometry_apply (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (A : GaussianMatrix ι) (i : ι) : rowIsometry U A i = U (A i) := rfl

def conjugateGaussianMatrix (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    GaussianMatrix ι ≃ₗᵢ[ℝ] GaussianMatrix ι :=
  (rowIsometry U).trans (transposeGaussianMatrix.trans
    ((rowIsometry U).trans transposeGaussianMatrix))

lemma conjugateGaussianMatrix_preserves (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    (stdGaussian (GaussianMatrix ι)).map (conjugateGaussianMatrix U) =
      stdGaussian (GaussianMatrix ι) :=
  stdGaussian_map _

lemma euclidean_isometry_apply_eq_sum
    (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (v : EuclideanSpace ℝ ι) (i : ι) :
    U v i = ∑ j, v j * U (EuclideanSpace.basisFun ι ℝ j) i := by
  conv_lhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr v, map_sum]
  simp

lemma conjugateGaussianMatrix_apply
    (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (A : GaussianMatrix ι) (i j : ι) :
    conjugateGaussianMatrix U A i j =
      ∑ k, ∑ l, U (EuclideanSpace.basisFun ι ℝ k) i * A k l *
        U (EuclideanSpace.basisFun ι ℝ l) j := by
  simp only [conjugateGaussianMatrix, LinearIsometryEquiv.trans_apply,
    transposeGaussianMatrix_apply, rowIsometry_apply]
  rw [euclidean_isometry_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [transposeGaussianMatrix_apply, rowIsometry_apply]
  rw [euclidean_isometry_apply_eq_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma conjugateGaussianMatrix_transpose
    (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) (A : GaussianMatrix ι) :
    conjugateGaussianMatrix U (transposeGaussianMatrix A) =
      transposeGaussianMatrix (conjugateGaussianMatrix U A) := by
  ext i j
  simp only [conjugateGaussianMatrix_apply, transposeGaussianMatrix_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

def symmetrizeGaussianMatrix (s : ℝ) (A : GaussianMatrix ι) : GaussianMatrix ι :=
  s • (A + transposeGaussianMatrix A)

lemma symmetrizeGaussianMatrix_continuous (s : ℝ) :
    Continuous (symmetrizeGaussianMatrix (ι := ι) s) := by
  unfold symmetrizeGaussianMatrix
  fun_prop

lemma conjugate_symmetrize (s : ℝ)
    (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) (A : GaussianMatrix ι) :
    conjugateGaussianMatrix U (symmetrizeGaussianMatrix s A) =
      symmetrizeGaussianMatrix s (conjugateGaussianMatrix U A) := by
  simp only [symmetrizeGaussianMatrix, map_smul, map_add,
    conjugateGaussianMatrix_transpose]

def goeLaw (ι : Type*) [Fintype ι] (s : ℝ) : Measure (GaussianMatrix ι) :=
  (stdGaussian (GaussianMatrix ι)).map (symmetrizeGaussianMatrix s)

lemma goeLaw_conjugate (s : ℝ)
    (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    (goeLaw ι s).map (conjugateGaussianMatrix U) = goeLaw ι s := by
  unfold goeLaw
  rw [Measure.map_map (by fun_prop) (symmetrizeGaussianMatrix_continuous s).measurable]
  simp only [Function.comp_def, conjugate_symmetrize]
  calc
    _ = ((stdGaussian (GaussianMatrix ι)).map (conjugateGaussianMatrix U)).map
        (symmetrizeGaussianMatrix s) :=
      (Measure.map_map (symmetrizeGaussianMatrix_continuous s).measurable
        (conjugateGaussianMatrix U).continuous.measurable).symm
    _ = _ := by rw [conjugateGaussianMatrix_preserves]

lemma conjugateGaussianMatrix_measurable {Ω : Type*} [MeasurableSpace Ω]
    (U : Ω → EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (hU : Measurable (fun p : Ω × EuclideanSpace ℝ ι => U p.1 p.2)) :
    Measurable (fun p : Ω × GaussianMatrix ι => conjugateGaussianMatrix (U p.1) p.2) := by
  have hc (k i : ι) : Measurable (fun ω => U ω (EuclideanSpace.basisFun ι ℝ k) i) :=
    (by fun_prop : Measurable (fun x : EuclideanSpace ℝ ι => x i)).comp
      (hU.comp (measurable_id.prodMk measurable_const))
  change Measurable (fun p : Ω × GaussianMatrix ι => WithLp.toLp 2
    (fun i => WithLp.toLp 2 (fun j => conjugateGaussianMatrix (U p.1) p.2 i j)))
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro i
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro j
  simp only [conjugateGaussianMatrix_apply]
  apply Finset.measurable_sum
  intro k _
  apply Finset.measurable_sum
  intro l _
  exact ((hc k i).comp measurable_fst |>.mul
    ((by fun_prop : Measurable (fun A : GaussianMatrix ι => A k l)).comp measurable_snd)).mul
      ((hc l j).comp measurable_fst)

lemma random_goe_conjugation_preserving {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (s : ℝ)
    (U : Ω → EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (hU : Measurable (fun p : Ω × EuclideanSpace ℝ ι => U p.1 p.2)) :
    MeasurePreserving (fun p : Ω × GaussianMatrix ι =>
      (p.1, conjugateGaussianMatrix (U p.1) p.2))
      (μ.prod (goeLaw ι s)) (μ.prod (goeLaw ι s)) := by
  let : IsProbabilityMeasure (goeLaw ι s) :=
    (Measure.isProbabilityMeasure_map_iff
      (symmetrizeGaussianMatrix_continuous s).measurable.aemeasurable).2 inferInstance
  exact (MeasurePreserving.id μ).skew_product
    (g := fun ω A => conjugateGaussianMatrix (U ω) A)
    (conjugateGaussianMatrix_measurable U hU)
    (Filter.Eventually.of_forall (fun ω => goeLaw_conjugate s (U ω)))

noncomputable def matrixUnit (i j : ι) : GaussianMatrix ι := by
  classical
  exact PiLp.single 2 i (EuclideanSpace.single j 1)

@[simp] lemma matrixUnit_inner (i j : ι) (A : GaussianMatrix ι) :
    inner ℝ (matrixUnit i j) A = A i j := by
  classical
  rw [PiLp.inner_apply]
  rw [Finset.sum_eq_single i]
  · simp [matrixUnit, EuclideanSpace.inner_single_left]
  · intro k _ hki
    simp [matrixUnit, hki]
  · simp

@[simp] lemma matrixUnit_apply [DecidableEq ι] (i j k l : ι) :
    matrixUnit i j k l = if k = i ∧ l = j then 1 else 0 := by
  classical
  simp [matrixUnit]
  split_ifs <;> simp_all

def goeEntryVector (s : ℝ) (i j : ι) : GaussianMatrix ι :=
  s • (matrixUnit i j + matrixUnit j i)

lemma goeEntryVector_inner (s : ℝ) (i j : ι) (A : GaussianMatrix ι) :
    inner ℝ (goeEntryVector s i j) A = symmetrizeGaussianMatrix s A i j := by
  simp [goeEntryVector, symmetrizeGaussianMatrix, inner_smul_left, inner_add_left]

lemma goe_entry_variance [DecidableEq ι] (s : ℝ) (i j : ι) :
    ‖goeEntryVector s i j‖ ^ 2 = if i = j then 4 * s ^ 2 else 2 * s ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp only [goeEntryVector, real_inner_smul_left, real_inner_smul_right,
    inner_add_left, inner_add_right, matrixUnit_inner, matrixUnit_apply]
  by_cases hij : i = j
  · subst j
    simp only [and_self, ite_true]
    ring
  · have hji : j ≠ i := Ne.symm hij
    simp only [hij, hji, and_self, ite_true, ite_false]
    ring

lemma goe_entry_law [DecidableEq ι] (s : ℝ) (i j : ι) :
    (goeLaw ι s).map (fun A => A i j) =
      gaussianReal 0 (if i = j then (4 * s ^ 2).toNNReal else (2 * s ^ 2).toNNReal) := by
  classical
  unfold goeLaw
  rw [Measure.map_map (by fun_prop) (symmetrizeGaussianMatrix_continuous s).measurable]
  simp only [Function.comp_def, ← goeEntryVector_inner]
  rw [inner_stdGaussian_law, goe_entry_variance]
  split_ifs <;> rfl

variable [LinearOrder ι]

abbrev UpperEntry (ι : Type*) [LinearOrder ι] := {p : ι × ι // p.1 ≤ p.2}

lemma goeEntryVector_orthogonal (s : ℝ) :
    Pairwise (fun p q : UpperEntry ι =>
      inner ℝ (goeEntryVector s p.1.1 p.1.2) (goeEntryVector s q.1.1 q.1.2) = 0) := by
  rintro ⟨⟨i, j⟩, hij⟩ ⟨⟨k, l⟩, hkl⟩ hpq
  have h1 : ¬(i = k ∧ j = l) := by
    rintro ⟨rfl, rfl⟩
    exact hpq rfl
  have h2 : ¬(i = l ∧ j = k) := by
    intro hs
    have he : i = j := le_antisymm hij (by simpa only [hs.1, hs.2] using hkl)
    apply hpq
    apply Subtype.ext
    exact Prod.ext (he.trans hs.2) (he.symm.trans hs.1)
  simp only [goeEntryVector, real_inner_smul_left, real_inner_smul_right,
    inner_add_left, inner_add_right, matrixUnit_inner, matrixUnit_apply]
  simp only [h1, h2, ite_false, add_zero, mul_zero,
    show ¬(j = k ∧ i = l) from fun h => h2 ⟨h.2, h.1⟩,
    show ¬(j = l ∧ i = k) from fun h => h1 ⟨h.2, h.1⟩]

lemma goe_entries_independent (s : ℝ) :
    iIndepFun (fun p : UpperEntry ι => fun A : GaussianMatrix ι => A p.1.1 p.1.2)
      (goeLaw ι s) := by
  have h := gaussian_orthogonal_independent
    (fun p : UpperEntry ι => goeEntryVector s p.1.1 p.1.2) (goeEntryVector_orthogonal s)
  simp only [goeEntryVector_inner] at h
  let : IsProbabilityMeasure (goeLaw ι s) :=
    (Measure.isProbabilityMeasure_map_iff
      (symmetrizeGaussianMatrix_continuous s).measurable.aemeasurable).2 inferInstance
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun _ => by fun_prop)).2
  unfold goeLaw
  rw [Measure.map_map (by fun_prop) (symmetrizeGaussianMatrix_continuous s).measurable]
  have hh := h.map_fun_eq_pi_map (fun _ => by fun_prop)
  simp only [Function.comp_def] at *
  rw [hh]
  congr 1
  ext p : 1
  exact (Measure.map_map (g := fun A : GaussianMatrix ι => A p.1.1 p.1.2) (by fun_prop)
    (symmetrizeGaussianMatrix_continuous s).measurable).symm

end

section

open scoped NNReal

section Upper

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def upperRead (A : GaussianMatrix ι) : UpperEntry ι → ℝ := fun p => A p.1.1 p.1.2

def upperWrite (a : UpperEntry ι → ℝ) : GaussianMatrix ι :=
  WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j =>
    if h : i ≤ j then a ⟨(i, j), h⟩ else a ⟨(j, i), (le_of_not_ge h)⟩))

lemma upperRead_measurable : Measurable (upperRead (ι := ι)) := by
  apply Measurable.of_eval
  intro p
  fun_prop [upperRead]

lemma upperWrite_measurable : Measurable (upperWrite (ι := ι)) := by
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro i
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro j
  dsimp [upperWrite]
  split_ifs <;> fun_prop

lemma upperWrite_upperRead (A : GaussianMatrix ι) (hA : ∀ i j, A i j = A j i) :
    upperWrite (upperRead A) = A := by
  ext i j
  dsimp [upperWrite, upperRead]
  split_ifs
  · rfl
  · exact hA j i

@[simp] lemma upperRead_upperWrite (a : UpperEntry ι → ℝ) :
    upperRead (upperWrite a) = a := by
  funext p
  exact dite_eq_left p.2

lemma goe_symmetric_ae (s : ℝ) : ∀ᵐ A ∂goeLaw ι s, ∀ i j, A i j = A j i := by
  rw [goeLaw]
  apply (ae_map_iff (symmetrizeGaussianMatrix_continuous s).measurable.aemeasurable (by measurability)).2
  filter_upwards [] with A i j
  simp only [symmetrizeGaussianMatrix, PiLp.smul_apply, PiLp.add_apply,
    transposeGaussianMatrix_apply, smul_eq_mul]
  ring

lemma goe_upper_law (s : ℝ) :
    (goeLaw ι s).map upperRead = Measure.pi (fun p : UpperEntry ι =>
      gaussianReal 0 (if p.1.1 = p.1.2 then (4 * s^2).toNNReal else (2 * s^2).toNNReal)) := by
  unfold upperRead
  rw [(goe_entries_independent (ι := ι) s).map_fun_eq_pi_map (fun _ => by fun_prop)]
  congr 1
  funext p
  exact goe_entry_law s p.1.1 p.1.2

lemma goeLaw_eq_upper_product (s : ℝ) :
    goeLaw ι s = (Measure.pi (fun p : UpperEntry ι =>
      gaussianReal 0 (if p.1.1 = p.1.2 then (4 * s^2).toNNReal else (2 * s^2).toNNReal))).map
        upperWrite := by
  rw [← goe_upper_law, Measure.map_map upperWrite_measurable upperRead_measurable]
  have heq : (upperWrite ∘ upperRead : GaussianMatrix ι → GaussianMatrix ι) =ᵐ[goeLaw ι s] id := by
    filter_upwards [goe_symmetric_ae (ι := ι) s] with A hA
    exact upperWrite_upperRead A hA
  rw [Measure.map_congr heq, Measure.map_id]

end Upper

def upperSplit (n : ℕ) : Unit ⊕ (Fin n ⊕ UpperEntry (Fin n)) ≃ UpperEntry (Fin (n + 1)) :=
  Equiv.ofBijective
    (fun x => match x with
      | Sum.inl _ => ⟨(0, 0), le_rfl⟩
      | Sum.inr (Sum.inl i) => ⟨(0, i.succ), Fin.zero_le _⟩
      | Sum.inr (Sum.inr p) => ⟨(p.1.1.succ, p.1.2.succ), Fin.succ_le_succ_iff.mpr p.2⟩)
    ⟨by
      intro x y h
      have hz (i : Fin n) : (0 : Fin (n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
      rcases x with u | (i | p) <;> rcases y with v | (j | q)
      all_goals simp_all [Subtype.ext_iff, Prod.ext_iff]
    , by
      rintro ⟨⟨i, j⟩, hij⟩
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact ⟨Sum.inl (), rfl⟩
        | succ j => exact ⟨Sum.inr (Sum.inl j), rfl⟩
      | succ i =>
        cases j using Fin.cases with
        | zero => simp at hij
        | succ j => exact ⟨Sum.inr (Sum.inr ⟨(i, j), Fin.succ_le_succ_iff.mp hij⟩), rfl⟩⟩

@[simp] lemma upperSplit_diag (n : ℕ) : upperSplit n (Sum.inl ()) = ⟨(0, 0), le_rfl⟩ := rfl

@[simp] lemma upperSplit_column (n : ℕ) (i : Fin n) :
    upperSplit n (Sum.inr (Sum.inl i)) = ⟨(0, i.succ), Fin.zero_le _⟩ := rfl

@[simp] lemma upperSplit_tail (n : ℕ) (p : UpperEntry (Fin n)) :
    upperSplit n (Sum.inr (Sum.inr p)) =
      ⟨(p.1.1.succ, p.1.2.succ), Fin.succ_le_succ_iff.mpr p.2⟩ := rfl

def goeUpperMarginal {ι : Type*} [LinearOrder ι] (s : ℝ) (p : UpperEntry ι) : Measure ℝ :=
  gaussianReal 0 (if p.1.1 = p.1.2 then (4 * s^2).toNNReal else (2 * s^2).toNNReal)

instance goeUpperMarginal_probability {ι : Type*} [LinearOrder ι] (s : ℝ) (p : UpperEntry ι) :
    IsProbabilityMeasure (goeUpperMarginal s p) := by
  unfold goeUpperMarginal
  infer_instance

def splitUpper (n : ℕ) (a : UpperEntry (Fin (n + 1)) → ℝ) :
    ℝ × ((Fin n → ℝ) × (UpperEntry (Fin n) → ℝ)) :=
  (a ⟨(0, 0), le_rfl⟩, ((fun i => a ⟨(0, i.succ), Fin.zero_le _⟩),
    fun p => a ⟨(p.1.1.succ, p.1.2.succ), Fin.succ_le_succ_iff.mpr p.2⟩))

lemma splitUpper_preserving (n : ℕ) (s : ℝ) :
    MeasurePreserving (splitUpper n) (Measure.pi (goeUpperMarginal (ι := Fin (n + 1)) s))
      ((gaussianReal 0 (4 * s^2).toNNReal).prod
        ((Measure.pi fun _ : Fin n => gaussianReal 0 (2 * s^2).toNNReal).prod
          (Measure.pi (goeUpperMarginal (ι := Fin n) s)))) := by
  let μ := goeUpperMarginal (ι := Fin (n + 1)) s
  have h1 := (measurePreserving_piCongrLeft μ (upperSplit n)).symm
  have h2 := measurePreserving_sumPiEquivProdPi (fun i => μ (upperSplit n i))
  have h3 := (measurePreserving_piUnique (fun u : Unit => μ (upperSplit n (Sum.inl u)))).prod
    (measurePreserving_sumPiEquivProdPi (fun i => μ (upperSplit n (Sum.inr i))))
  have h := h3.comp (h2.comp h1)
  convert h using 1
  · rfl
  · dsimp [μ, goeUpperMarginal]
    simp only [Fin.succ_inj, (Ne.symm (Fin.succ_ne_zero _)), ite_false]
    rfl

open scoped BigOperators

def extendTailIsometry {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) where
  toFun x := WithLp.toLp 2 (Fin.cases (x 0) (U (WithLp.toLp 2 (fun i => x i.succ))))
  invFun x := WithLp.toLp 2 (Fin.cases (x 0) (U.symm (WithLp.toLp 2 (fun i => x i.succ))))
  left_inv x := by
    ext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => change U.symm (U (WithLp.toLp 2 (fun j => x j.succ))) i = x i.succ; simp
  right_inv x := by
    ext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => change U (U.symm (WithLp.toLp 2 (fun j => x j.succ))) i = x i.succ; simp
  map_add' x y := by
    ext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      change U ((WithLp.toLp 2 (fun j => x j.succ)) + (WithLp.toLp 2 (fun j => y j.succ))) i = _
      simp
  map_smul' c x := by
    ext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      change U (c • WithLp.toLp 2 (fun j => x j.succ)) i = _
      simp
  norm_map' x := by
    change ‖(WithLp.toLp 2 (Fin.cases (x 0) (U (WithLp.toLp 2 (fun i => x i.succ)))) : EuclideanSpace ℝ (Fin (n + 1)))‖ = ‖x‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have h := congrArg (fun r : ℝ => r^2) (U.norm_map (WithLp.toLp 2 (fun j => x j.succ)))
    simp only [PiLp.norm_sq_eq_of_L2] at h ⊢
    simpa only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ, PiLp.toLp_apply] using
      congrArg (fun t : ℝ => ‖x 0‖ ^ 2 + t) h

@[simp] lemma extendTailIsometry_zero {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin (n + 1))) : extendTailIsometry U x 0 = x 0 := rfl

@[simp] lemma extendTailIsometry_succ {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
    extendTailIsometry U x i.succ = U (WithLp.toLp 2 (fun j => x j.succ)) i := rfl

@[simp] lemma extendTailIsometry_basis_zero {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    extendTailIsometry U (EuclideanSpace.basisFun (Fin (n + 1)) ℝ 0) =
      EuclideanSpace.basisFun (Fin (n + 1)) ℝ 0 := by
  ext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp only [extendTailIsometry_succ, EuclideanSpace.basisFun_apply]
    have h : (WithLp.toLp 2 fun j : Fin n => (EuclideanSpace.single 0 (1 : ℝ)) j.succ) = 0 := by
      ext j; simp
    rw [h, map_zero]
    simp

lemma extendTailIsometry_basis_succ {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (k : Fin n) :
    extendTailIsometry U (EuclideanSpace.basisFun (Fin (n + 1)) ℝ k.succ) =
      WithLp.toLp 2 (Fin.cases 0 (U (EuclideanSpace.basisFun (Fin n) ℝ k))) := by
  ext i
  cases i using Fin.cases with
  | zero => simp
  | succ i =>
    simp only [extendTailIsometry_succ, Fin.cases_succ]
    apply congrArg (fun w : EuclideanSpace ℝ (Fin n) => U w i)
    ext j
    simp

def borderMatrix {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n))
    (B : GaussianMatrix (Fin n)) : GaussianMatrix (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.cases (WithLp.toLp 2 (Fin.cases a v))
    (fun i => WithLp.toLp 2 (Fin.cases (v i) (B i))))

@[simp] lemma borderMatrix_zero_zero {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n))
    (B : GaussianMatrix (Fin n)) : borderMatrix a v B 0 0 = a := rfl

@[simp] lemma borderMatrix_zero_succ {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n))
    (B : GaussianMatrix (Fin n)) (i : Fin n) : borderMatrix a v B 0 i.succ = v i := rfl

@[simp] lemma borderMatrix_succ_zero {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n))
    (B : GaussianMatrix (Fin n)) (i : Fin n) : borderMatrix a v B i.succ 0 = v i := rfl

@[simp] lemma borderMatrix_succ_succ {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n))
    (B : GaussianMatrix (Fin n)) (i j : Fin n) : borderMatrix a v B i.succ j.succ = B i j := rfl

lemma extendTailIsometry_border {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (a : ℝ) (v : EuclideanSpace ℝ (Fin n)) (B : GaussianMatrix (Fin n)) :
    conjugateGaussianMatrix (extendTailIsometry U) (borderMatrix a v B) =
      borderMatrix a (U v) (conjugateGaussianMatrix U B) := by
  classical
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases
  all_goals simp only [conjugateGaussianMatrix_apply, Fin.sum_univ_succ]
  all_goals simp only [extendTailIsometry_basis_zero, extendTailIsometry_basis_succ]
  all_goals simp only [Fin.cases_zero, Fin.cases_succ,
    EuclideanSpace.basisFun_apply]
  all_goals simp only [PiLp.single_apply, Fin.succ_ne_zero,
    ite_true, ite_false, borderMatrix_zero_zero, borderMatrix_zero_succ,
    borderMatrix_succ_zero, borderMatrix_succ_succ, zero_mul, mul_zero,
    one_mul, mul_one, Finset.sum_const_zero, add_zero, zero_add]
  · simpa only [EuclideanSpace.basisFun_apply] using (euclidean_isometry_apply_eq_sum U v _).symm
  · rw [euclidean_isometry_apply_eq_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [EuclideanSpace.basisFun_apply, mul_comm]
  · simpa only [EuclideanSpace.basisFun_apply] using (conjugateGaussianMatrix_apply U B _ _).symm

instance goeLaw_probability {ι : Type*} [Fintype ι] (s : ℝ) :
    IsProbabilityMeasure (goeLaw ι s) :=
  (Measure.isProbabilityMeasure_map_iff
    (symmetrizeGaussianMatrix_continuous s).measurable.aemeasurable).2 inferInstance

def matrixTail {n : ℕ} (A : GaussianMatrix (Fin (n + 1))) : GaussianMatrix (Fin n) :=
  WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => A i.succ j.succ))

def goeBlocks {n : ℕ} (A : GaussianMatrix (Fin (n + 1))) :
    ℝ × ((Fin n → ℝ) × GaussianMatrix (Fin n)) :=
  (A 0 0, (fun i => A 0 i.succ, matrixTail A))

lemma matrixTail_measurable (n : ℕ) : Measurable (matrixTail (n := n)) := by
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro i
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro j
  fun_prop [matrixTail]

lemma goeBlocks_measurable (n : ℕ) : Measurable (goeBlocks (n := n)) := by
  exact (by fun_prop : Measurable fun A : GaussianMatrix (Fin (n+1)) => A 0 0).prodMk
    ((Measurable.of_eval (fun _ => by fun_prop)).prodMk (matrixTail_measurable n))

lemma borderMatrix_blocks {n : ℕ} (A : GaussianMatrix (Fin (n + 1)))
    (hA : ∀ i j, A i j = A j i) :
    borderMatrix (goeBlocks A).1 (WithLp.toLp 2 (goeBlocks A).2.1) (goeBlocks A).2.2 = A := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases
  · rfl
  · rfl
  · exact hA _ _
  · rfl

lemma goeBlocks_preserving (n : ℕ) (s : ℝ) :
    MeasurePreserving (goeBlocks (n := n)) (goeLaw (Fin (n + 1)) s)
      ((gaussianReal 0 (4 * s^2).toNNReal).prod
        ((Measure.pi fun _ : Fin n => gaussianReal 0 (2 * s^2).toNNReal).prod
          (goeLaw (Fin n) s))) := by
  let μ := Measure.pi (goeUpperMarginal (ι := Fin (n+1)) s)
  have hw : MeasurePreserving (upperWrite (ι := Fin n))
      (Measure.pi (goeUpperMarginal s)) (goeLaw (Fin n) s) :=
    ⟨upperWrite_measurable, (goeLaw_eq_upper_product s).symm⟩
  have hr : MeasurePreserving (upperRead (ι := Fin (n+1))) (goeLaw (Fin (n+1)) s) μ :=
    ⟨upperRead_measurable, goe_upper_law s⟩
  have hp := (MeasurePreserving.id (gaussianReal 0 (4 * s^2).toNNReal)).prod
    ((MeasurePreserving.id (Measure.pi fun _ : Fin n => gaussianReal 0 (2 * s^2).toNNReal)).prod hw)
  have h := hp.comp ((splitUpper_preserving n s).comp hr)
  refine ⟨goeBlocks_measurable n, ?_⟩
  rw [← h.map_eq]
  apply Measure.map_congr
  filter_upwards [goe_symmetric_ae (ι := Fin (n+1)) s] with A hA
  dsimp only [Function.comp_apply, Prod.map_apply, id_eq, splitUpper, upperRead, goeBlocks]
  refine Prod.ext rfl (Prod.ext rfl ?_)
  change matrixTail A = upperWrite (upperRead (matrixTail A))
  exact (upperWrite_upperRead _ (fun i j => hA i.succ j.succ)).symm

lemma aligned_goeBlock_preserving (n : ℕ) (s : ℝ)
    (e : EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (fun p : (Fin n → ℝ) × GaussianMatrix (Fin n) =>
      (p.1, conjugateGaussianMatrix (alignIsometry e (WithLp.toLp 2 p.1)) p.2))
      ((Measure.pi fun _ : Fin n => gaussianReal 0 (2 * s^2).toNNReal).prod (goeLaw (Fin n) s))
      ((Measure.pi fun _ : Fin n => gaussianReal 0 (2 * s^2).toNNReal).prod (goeLaw (Fin n) s)) := by
  have hm : Measurable (fun p : (Fin n → ℝ) × EuclideanSpace ℝ (Fin n) =>
      alignIsometry e (WithLp.toLp 2 p.1) p.2) := by
    simp_rw [alignIsometry_apply]
    fun_prop
  exact random_goe_conjugation_preserving
    (Measure.pi fun _ : Fin n => gaussianReal 0 (2 * s^2).toNNReal) s
    (fun v : Fin n → ℝ => alignIsometry e (WithLp.toLp 2 v)) hm

lemma exposed_column_tail_law (n : ℕ) (s : ℝ) (e : EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (fun A : GaussianMatrix (Fin (n+1)) =>
      (A 0 0, (fun i => A 0 i.succ,
        conjugateGaussianMatrix (alignIsometry e (WithLp.toLp 2 (fun i => A 0 i.succ)))
          (matrixTail A))))
      (goeLaw (Fin (n+1)) s)
      ((gaussianReal 0 (4 * s^2).toNNReal).prod
        ((Measure.pi fun _ : Fin n => gaussianReal 0 (2 * s^2).toNNReal).prod
          (goeLaw (Fin n) s))) :=
  ((MeasurePreserving.id _).prod (aligned_goeBlock_preserving n s e)).comp (goeBlocks_preserving n s)

lemma goe_step_conjugate {n : ℕ} (e : EuclideanSpace ℝ (Fin n)) (he : ‖e‖ = 1)
    (A : GaussianMatrix (Fin (n+1))) (hA : ∀ i j, A i j = A j i) :
    conjugateGaussianMatrix
      (extendTailIsometry (alignIsometry e (WithLp.toLp 2 (fun i => A 0 i.succ)))) A =
      borderMatrix (A 0 0) (‖(WithLp.toLp 2 (fun i => A 0 i.succ) : EuclideanSpace ℝ (Fin n))‖ • e)
        (conjugateGaussianMatrix (alignIsometry e (WithLp.toLp 2 (fun i => A 0 i.succ)))
          (matrixTail A)) := by
  conv_lhs => arg 2; rw [← borderMatrix_blocks A hA]
  rw [extendTailIsometry_border]
  dsimp only [goeBlocks]
  rw [alignIsometry_align _ _ he]

end

section

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def orthoMatrix (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) : Matrix ι ι ℝ :=
  fun i j => U (EuclideanSpace.basisFun ι ℝ j) i

def matrixOfGaussian (A : GaussianMatrix ι) : Matrix ι ι ℝ := fun i j => A i j

lemma matrixOfGaussian_injective : Function.Injective (matrixOfGaussian (ι := ι)) := by
  intro A B h
  ext i j
  exact congrFun (congrFun h i) j

lemma orthoMatrix_trans (U V : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    orthoMatrix (U.trans V) = orthoMatrix V * orthoMatrix U := by
  ext i j
  change V (U (EuclideanSpace.basisFun ι ℝ j)) i = _
  rw [euclidean_isometry_apply_eq_sum]
  simp only [Matrix.mul_apply, orthoMatrix]
  apply Finset.sum_congr rfl
  intros
  ring

lemma matrixOfGaussian_conjugate (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (A : GaussianMatrix ι) :
    matrixOfGaussian (conjugateGaussianMatrix U A) =
      orthoMatrix U * matrixOfGaussian A * (orthoMatrix U).transpose := by
  ext i j
  simp only [matrixOfGaussian, conjugateGaussianMatrix_apply, Matrix.mul_apply,
    Matrix.transpose_apply, orthoMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma conjugateGaussianMatrix_trans (U V : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (A : GaussianMatrix ι) :
    conjugateGaussianMatrix (U.trans V) A =
      conjugateGaussianMatrix V (conjugateGaussianMatrix U A) := by
  apply matrixOfGaussian_injective
  simp only [matrixOfGaussian_conjugate, orthoMatrix_trans, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

lemma conjugate_symmetric (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (A : GaussianMatrix ι) (hA : ∀ i j, A i j = A j i) :
    ∀ i j, conjugateGaussianMatrix U A i j = conjugateGaussianMatrix U A j i := by
  have hT : transposeGaussianMatrix A = A := by ext i j; exact hA j i
  have h := conjugateGaussianMatrix_transpose U A
  rw [hT] at h
  intro i j
  exact congrArg (fun B : GaussianMatrix ι => B i j) h

end

open scoped BigOperators

def firstAxis (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => if i.val = 0 then 1 else 0)

lemma firstAxis_succ (n : ℕ) : firstAxis (n+1) = EuclideanSpace.basisFun (Fin (n+1)) ℝ 0 := by
  ext i
  cases i using Fin.cases <;> simp [firstAxis, EuclideanSpace.basisFun_apply]

lemma firstAxis_norm_succ (n : ℕ) : ‖firstAxis (n+1)‖ = 1 := by
  rw [firstAxis_succ]
  exact (EuclideanSpace.basisFun (Fin (n+1)) ℝ).orthonormal.norm_eq_one 0

lemma align_firstAxis (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    alignIsometry (firstAxis n) v v = ‖v‖ • firstAxis n := by
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ n => exact alignIsometry_align _ _ (firstAxis_norm_succ n)

lemma extendTailIsometry_firstAxis {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    extendTailIsometry U (firstAxis (n+1)) = firstAxis (n+1) := by
  rw [firstAxis_succ]
  exact extendTailIsometry_basis_zero U

def firstColumn {n : ℕ} (A : GaussianMatrix (Fin (n+1))) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => A 0 i.succ)

def reducedTail {n : ℕ} (A : GaussianMatrix (Fin (n+1))) : GaussianMatrix (Fin n) :=
  conjugateGaussianMatrix (alignIsometry (firstAxis n) (firstColumn A)) (matrixTail A)

lemma reducedTail_symmetric {n : ℕ} (A : GaussianMatrix (Fin (n+1)))
    (hA : ∀ i j, A i j = A j i) : ∀ i j, reducedTail A i j = reducedTail A j i :=
  conjugate_symmetric _ _ (fun i j => hA i.succ j.succ)

@[fun_prop] lemma firstColumn_measurable (n : ℕ) : Measurable (firstColumn (n := n)) := by
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro i
  fun_prop [firstColumn]

lemma reducedTail_measurable (n : ℕ) : Measurable (reducedTail (n := n)) := by
  have hm := (exposed_column_tail_law n 1 (firstAxis n)).measurable
  have ht : Measurable (fun p : ℝ × ((Fin n → ℝ) × GaussianMatrix (Fin n)) => p.2.2) :=
    measurable_snd.comp measurable_snd
  exact ht.comp hm

lemma first_step_conjugate {n : ℕ} (A : GaussianMatrix (Fin (n+1)))
    (hA : ∀ i j, A i j = A j i) :
    conjugateGaussianMatrix (extendTailIsometry (alignIsometry (firstAxis n) (firstColumn A))) A =
      borderMatrix (A 0 0) (‖firstColumn A‖ • firstAxis n) (reducedTail A) := by
  conv_lhs => arg 2; rw [← borderMatrix_blocks A hA]
  rw [extendTailIsometry_border]
  dsimp only [goeBlocks]
  change borderMatrix (A 0 0) (alignIsometry (firstAxis n) (firstColumn A) (firstColumn A))
    (reducedTail A) = _
  rw [align_firstAxis]

def triReduce : (n : ℕ) → GaussianMatrix (Fin n) → GaussianMatrix (Fin n)
  | 0, A => A
  | n+1, A => borderMatrix (A 0 0) (‖firstColumn A‖ • firstAxis n) (triReduce n (reducedTail A))

def triIsometry : (n : ℕ) → GaussianMatrix (Fin n) →
    (EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
  | 0, _ => LinearIsometryEquiv.refl _ _
  | n+1, A => (extendTailIsometry (alignIsometry (firstAxis n) (firstColumn A))).trans
      (extendTailIsometry (triIsometry n (reducedTail A)))

lemma triIsometry_firstAxis (n : ℕ) (A : GaussianMatrix (Fin n)) :
    triIsometry n A (firstAxis n) = firstAxis n := by
  cases n with
  | zero => rfl
  | succ n => simp only [triIsometry, LinearIsometryEquiv.trans_apply, extendTailIsometry_firstAxis]

lemma triReduce_conjugate (n : ℕ) (A : GaussianMatrix (Fin n))
    (hA : ∀ i j, A i j = A j i) :
    triReduce n A = conjugateGaussianMatrix (triIsometry n A) A := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    rw [triIsometry, conjugateGaussianMatrix_trans, first_step_conjugate A hA,
      extendTailIsometry_border]
    simp only [map_smul, triIsometry_firstAxis]
    rw [← ih _ (reducedTail_symmetric A hA)]
    rfl

lemma borderMatrix_measurable (n : ℕ) :
    Measurable (fun p : ℝ × (EuclideanSpace ℝ (Fin n) × GaussianMatrix (Fin n)) =>
      borderMatrix p.1 p.2.1 p.2.2) := by
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro i
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro j
  change Measurable (fun p : ℝ × (EuclideanSpace ℝ (Fin n) × GaussianMatrix (Fin n)) =>
    borderMatrix p.1 p.2.1 p.2.2 i j)
  cases i using Fin.cases <;> cases j using Fin.cases
  all_goals simp only [borderMatrix_zero_zero, borderMatrix_zero_succ,
    borderMatrix_succ_zero, borderMatrix_succ_succ]
  all_goals fun_prop

lemma triReduce_measurable (n : ℕ) : Measurable (triReduce n) := by
  induction n with
  | zero => exact measurable_id
  | succ n ih =>
    exact (borderMatrix_measurable n).comp
      ((by fun_prop : Measurable fun A : GaussianMatrix (Fin (n+1)) => A 0 0).prodMk
        (((firstColumn_measurable n).norm.smul measurable_const).prodMk
          (ih.comp (reducedTail_measurable n))))

def columnNormLaw (n : ℕ) (s : ℝ) : Measure ℝ :=
  (Measure.pi fun _ : Fin n => gaussianReal 0 (2*s^2).toNNReal).map
    (fun v : Fin n → ℝ => ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖)

def assembleTri (n : ℕ) (p : ℝ × (ℝ × GaussianMatrix (Fin n))) : GaussianMatrix (Fin (n+1)) :=
  borderMatrix p.1 (p.2.1 • firstAxis n) p.2.2

lemma assembleTri_measurable (n : ℕ) : Measurable (assembleTri n) :=
  (borderMatrix_measurable n).comp
    (measurable_fst.prodMk ((measurable_fst.comp measurable_snd |>.smul measurable_const).prodMk
      (measurable_snd.comp measurable_snd)))

def triMatrixLaw : (n : ℕ) → ℝ → Measure (GaussianMatrix (Fin n))
  | 0, s => goeLaw (Fin 0) s
  | n+1, s => ((gaussianReal 0 (4*s^2).toNNReal).prod
      ((columnNormLaw n s).prod (triMatrixLaw n s))).map (assembleTri n)

lemma columnNorm_preserving (n : ℕ) (s : ℝ) :
    MeasurePreserving (fun v : Fin n → ℝ => ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖)
      (Measure.pi fun _ : Fin n => gaussianReal 0 (2*s^2).toNNReal) (columnNormLaw n s) :=
  ⟨(WithLp.measurable_toLp _ _).norm, rfl⟩

instance columnNormLaw_probability (n : ℕ) (s : ℝ) : IsProbabilityMeasure (columnNormLaw n s) :=
  (Measure.isProbabilityMeasure_map_iff
    (columnNorm_preserving n s).measurable.aemeasurable).2 inferInstance

instance triMatrixLaw_probability (n : ℕ) (s : ℝ) : IsProbabilityMeasure (triMatrixLaw n s) := by
  induction n with
  | zero => exact goeLaw_probability s
  | succ n ih =>
    have := ih
    exact (Measure.isProbabilityMeasure_map_iff (assembleTri_measurable n).aemeasurable).2 inferInstance

lemma triReduce_preserving (n : ℕ) (s : ℝ) :
    MeasurePreserving (triReduce n) (goeLaw (Fin n) s) (triMatrixLaw n s) := by
  induction n with
  | zero => exact MeasurePreserving.id _
  | succ n ih =>
    have hp := (MeasurePreserving.id (gaussianReal 0 (4*s^2).toNNReal)).prod
      ((columnNorm_preserving n s).prod ih)
    have ha : MeasurePreserving (assembleTri n)
        ((gaussianReal 0 (4*s^2).toNNReal).prod ((columnNormLaw n s).prod (triMatrixLaw n s)))
        (triMatrixLaw (n+1) s) := ⟨assembleTri_measurable n, rfl⟩
    exact ha.comp (hp.comp (exposed_column_tail_law n s (firstAxis n)))

end CriticalSK

end

end OAI
