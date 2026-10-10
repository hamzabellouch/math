import Mathlib
import OAI.Probability.Subsphere.Regression.Geometry

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
namespace SubsphereRegression
open scoped Topology
open InnerProductSpace
section GramFactorization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι : Type*} [Fintype ι]
lemma gram_linear_combination (w : ι → E) (T : Matrix ι ι ℝ) :
    Matrix.gram ℝ (fun j => ∑ i, (T i j) • w i) =
      T.transpose * Matrix.gram ℝ w * T := by
  ext a b
  simp only [Matrix.gram_apply, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, Matrix.mul_apply, Matrix.transpose_apply]
  simp only [Finset.sum_mul]
  congr 1
  ext j
  congr 1
  ext i
  ring

variable (n : ℕ)
def gsUpper (v : Fin n → E) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  (if i = j then 1 else 0) +
    if i < j then ⟪gramSchmidt ℝ v i, v j⟫ / ‖gramSchmidt ℝ v i‖ ^ 2 else 0

lemma gsUpper_expansion (v : Fin n → E) (j : Fin n) :
    ∑ i, (gsUpper n v i j) • gramSchmidt ℝ v i = v j := by
  simp only [gsUpper, add_smul, Finset.sum_add_distrib]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  conv_rhs => rw [gramSchmidt_def'' ℝ v j]
  congr 1
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

lemma gsUpper_det (v : Fin n → E) : (gsUpper n v).det = 1 := by
  have htri : (gsUpper n v).IsUpperTriangular := by
    intro i j hij
    change j < i at hij
    simp [gsUpper, (ne_of_gt hij), (not_lt_of_ge hij.le)]
  rw [Matrix.det_of_isUpperTriangular htri]
  simp [gsUpper]

lemma gram_gramSchmidt_diagonal (v : Fin n → E) :
    Matrix.gram ℝ (gramSchmidt ℝ v) = Matrix.diagonal (fun i => ‖gramSchmidt ℝ v i‖ ^ 2) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.gram_apply]
  · simp [Matrix.gram_apply, hij,
      gramSchmidt_orthogonal ℝ v hij]

/-- The Gram determinant is the product of the squared Gram--Schmidt lengths,
including tuples containing dependent vectors. -/
theorem det_gram_eq_prod_gramSchmidt (v : Fin n → E) :
    (Matrix.gram ℝ v).det = ∏ i, ‖gramSchmidt ℝ v i‖ ^ 2 := by
  have hv : (fun j => ∑ i, (gsUpper n v i j) • gramSchmidt ℝ v i) = v :=
    funext (gsUpper_expansion n v)
  have h := gram_linear_combination (gramSchmidt ℝ v) (gsUpper n v)
  rw [hv] at h
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, gsUpper_det,
    one_mul, mul_one, gram_gramSchmidt_diagonal, Matrix.det_diagonal]
end GramFactorization

section GramDistances
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}
omit [FiniteDimensional ℝ E] in
lemma sub_gramSchmidt_mem_span (v : Fin n → E) (j : Fin n) :
    v j - gramSchmidt ℝ v j ∈ Submodule.span ℝ (v '' Set.Iio j) := by
  rw [← span_gramSchmidt_Iio ℝ v j]
  conv => arg 2; lhs; rw [gramSchmidt_def'' ℝ v j]
  rw [add_sub_cancel_left]
  exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, Finset.mem_Iio.mp hi, rfl⟩)

omit [FiniteDimensional ℝ E] in
lemma gramSchmidt_mem_span_orthogonal (v : Fin n → E) (j : Fin n) :
    gramSchmidt ℝ v j ∈ (Submodule.span ℝ (v '' Set.Iio j))ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨i, hi, rfl⟩
    exact gramSchmidt_inv_triangular ℝ v hi
  | zero => simp
  | add x y _ _ hx hy => simp [inner_add_right, hx, hy]
  | smul c x _ hx => simp [inner_smul_right, hx]

lemma gramSchmidt_eq_sub_starProjection (v : Fin n → E) (j : Fin n) :
    gramSchmidt ℝ v j = v j -
      (Submodule.span ℝ (v '' Set.Iio j)).starProjection (v j) := by
  have h := (Submodule.span ℝ (v '' Set.Iio j)).eq_starProjection_of_mem_orthogonal
    (u := v j) (sub_gramSchmidt_mem_span v j)
    (by simpa using gramSchmidt_mem_span_orthogonal v j)
  rw [h, sub_sub_cancel]

lemma norm_gramSchmidt_eq_infDist (v : Fin n → E) (j : Fin n) :
    ‖gramSchmidt ℝ v j‖ = Metric.infDist (v j)
      (Submodule.span ℝ (v '' Set.Iio j) : Set E) := by
  rw [gramSchmidt_eq_sub_starProjection, Submodule.starProjection_minimal,
    Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  rfl
lemma infDist_affine_mk' (p x : E) (K : Submodule ℝ E) :
    Metric.infDist x (AffineSubspace.mk' p K : Set E) =
      Metric.infDist (x - p) (K : Set E) := by
  rw [← EuclideanGeometry.dist_orthogonalProjection_eq_infDist,
    EuclideanGeometry.orthogonalProjection_apply_mem _ (AffineSubspace.self_mem_mk' p K),
    dist_eq_norm, Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  change ‖x - _‖ = ⨅ y : K, ‖(x - p) - y‖
  rw [← Submodule.starProjection_minimal]
  simp only [AffineSubspace.direction_mk', vsub_eq_sub, vadd_eq_add,
    Submodule.coe_orthogonalProjectionOnto_apply]
  congr 1
  abel

lemma norm_gramSchmidt_sub_eq_affine_infDist (p : E) (t : Fin n → E) (j : Fin n) :
    ‖gramSchmidt ℝ (fun i => t i - p) j‖ =
      Metric.infDist (t j) (AffineSubspace.mk' p
        (Submodule.span ℝ ((fun i => t i - p) '' Set.Iio j)) : Set E) := by
  rw [infDist_affine_mk', norm_gramSchmidt_eq_infDist]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma image_Iio_castSucc (v : Fin (n+1) → E) (j : Fin n) :
    v '' Set.Iio j.castSucc = (fun i => v i.castSucc) '' Set.Iio j := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hin : i.val < n := lt_trans hi j.isLt
    exact ⟨⟨i.val, hin⟩, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.castSucc, hi, rfl⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma image_Iio_last (v : Fin (n+1) → E) :
    v '' Set.Iio (Fin.last n) = Set.range (fun i : Fin n => v i.castSucc) := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i.val, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.castSucc, i.isLt, rfl⟩

lemma gramSchmidt_castSucc (v : Fin (n+1) → E) (j : Fin n) :
    gramSchmidt ℝ v j.castSucc = gramSchmidt ℝ (fun i => v i.castSucc) j := by
  rw [gramSchmidt_eq_sub_starProjection, gramSchmidt_eq_sub_starProjection,
    image_Iio_castSucc]

variable [MeasurableSpace E] [BorelSpace E]
lemma measurable_gramSchmidt (j : Fin n) :
    Measurable (fun v : Fin n → E => gramSchmidt ℝ v j) := by
  refine (wellFounded_lt : WellFounded ((· < ·) : Fin n → Fin n → Prop)).induction
    (C := fun j : Fin n => Measurable (fun v : Fin n → E => gramSchmidt ℝ v j)) j ?_
  intro j ih
  have heq : (fun v : Fin n → E => gramSchmidt ℝ v j) =
      fun v => v j - ∑ i ∈ Finset.Iio j,
        (⟪gramSchmidt ℝ v i, v j⟫ / ‖gramSchmidt ℝ v i‖ ^ 2) • gramSchmidt ℝ v i := by
    ext v
    rw [gramSchmidt_def]
    simp only [Submodule.starProjection_singleton]
    rfl
  rw [heq]
  apply (measurable_pi_apply j).sub
  apply Finset.measurable_sum
  intro i hi
  have hi' := ih i (Finset.mem_Iio.mp hi)
  exact ((hi'.inner (measurable_pi_apply j)).div (hi'.norm.pow_const 2)).smul hi'
end GramDistances

section PiLast
variable {E : Type*} [MeasurableSpace E] {n : ℕ} (ν : Measure E) [SigmaFinite ν]
lemma lintegral_pi_snoc (f : (Fin (n+1) → E) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ v, f v ∂Measure.pi (fun _ => ν) =
      ∫⁻ v : Fin n → E, ∫⁻ x, f (Fin.snoc v x) ∂ν ∂Measure.pi (fun _ => ν) := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) (Fin.last n)).symm
  rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) f,
    lintegral_prod_symm]
  · congr 1
    ext v
    congr 1
    ext x
    congr 1
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    exact Fin.insertNth_last' x v
  · exact (hf.comp (MeasurableEquiv.measurable _)).aemeasurable
end PiLast

section ReplicaMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def replicaWeight (m : ℕ) (p : E) {n : ℕ} (v : Fin n → E) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal ((‖gramSchmidt ℝ (fun j => v j - p) i‖)⁻¹ ^ m)

lemma measurable_replicaWeight (m : ℕ) (p : E) (n : ℕ) :
    Measurable (replicaWeight m p (n := n)) := by
  have hs : Measurable (fun v : Fin n → E => fun j => v j - p) := by fun_prop
  exact Finset.measurable_prod _ fun i _ =>
    (((measurable_gramSchmidt i).comp hs).norm.inv.pow_const m).ennreal_ofReal

omit [MeasurableSpace E] [BorelSpace E] in
lemma replicaWeight_snoc (m : ℕ) (p : E) {n : ℕ} (v : Fin n → E) (x : E) :
    replicaWeight m p (Fin.snoc v x) = replicaWeight m p v *
      ENNReal.ofReal ((Metric.infDist x (AffineSubspace.mk' p
        (Submodule.span ℝ (Set.range (fun i => v i - p))) : Set E))⁻¹ ^ m) := by
  unfold replicaWeight
  rw [Fin.prod_univ_castSucc]
  simp only [gramSchmidt_castSucc, Fin.snoc_castSucc]
  rw [norm_gramSchmidt_sub_eq_affine_infDist, image_Iio_last]
  simp only [Fin.snoc_last, Fin.snoc_castSucc]

def replicaConstant (ν : Measure E) (a : ℝ) (m : ℕ) : ℝ≥0∞ :=
  ν Set.univ + ENNReal.ofReal ((3 : ℝ) ^ Module.finrank ℝ E * (4 : ℝ) ^ a) *
    (2 : ℝ≥0∞) ^ (m+1)

lemma affine_inverse_moment_le_replicaConstant {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (L : AffineSubspace ℝ E) [Nonempty L] (m : ℕ)
    (hmargin : (Module.finrank ℝ L.direction : ℝ) + (m + 1 : ℕ) ≤ a) :
    ∫⁻ x, ENNReal.ofReal ((Metric.infDist x L)⁻¹ ^ m) ∂ν ≤ replicaConstant ν a m := by
  apply (hν.affine_inverse_moment hsupport L m hmargin).trans
  dsimp [replicaConstant]
  gcongr
  · norm_num
  · exact Submodule.finrank_le L.direction

/-- Tonelli integration of the Gram--Schmidt inverse-distance product.
The first replica p is fixed; n further replicas are integrated. -/
theorem replica_integral_bound {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1) (m : ℕ) (p : E)
    (n : ℕ) (hmargin : (n : ℝ) + m ≤ a) :
    ∫⁻ v : Fin n → E, replicaWeight m p v ∂Measure.pi (fun _ => ν) ≤
      (replicaConstant ν a m) ^ n := by
  induction n with
  | zero => simp [replicaWeight]
  | succ n ih =>
    have hmargin' : (n : ℝ) + m ≤ a := by exact le_trans (by push_cast; linarith) hmargin
    have hinner (v : Fin n → E) :
        ∫⁻ x, replicaWeight m p (Fin.snoc v x) ∂ν ≤
          replicaWeight m p v * replicaConstant ν a m := by
      simp_rw [replicaWeight_snoc]
      rw [lintegral_const_mul _ (by fun_prop)]
      gcongr
      apply affine_inverse_moment_le_replicaConstant hν hsupport
      have hdim := finrank_range_le_card (R := ℝ) (fun i : Fin n => v i - p)
      simp only [Fintype.card_fin] at hdim
      have hdim' : (Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i => v i - p))) : ℝ) ≤ n :=
        by exact_mod_cast hdim
      rw [AffineSubspace.direction_mk']
      push_cast at hmargin ⊢
      linarith
    calc
      _ = ∫⁻ v : Fin n → E, ∫⁻ x, replicaWeight m p (Fin.snoc v x) ∂ν
          ∂Measure.pi (fun _ => ν) := lintegral_pi_snoc ν _ (measurable_replicaWeight m p (n+1))
      _ ≤ ∫⁻ v : Fin n → E, replicaWeight m p v * replicaConstant ν a m
          ∂Measure.pi (fun _ => ν) := lintegral_mono hinner
      _ = (∫⁻ v : Fin n → E, replicaWeight m p v ∂Measure.pi (fun _ => ν)) *
          replicaConstant ν a m := lintegral_mul_const _ (measurable_replicaWeight m p n)
      _ ≤ (replicaConstant ν a m)^n * replicaConstant ν a m :=
          mul_le_mul' (ih hmargin') le_rfl
      _ = _ := (pow_succ _ _).symm
end ReplicaMoments
section AePiLast
variable {E : Type*} [MeasurableSpace E] {n : ℕ} (ν : Measure E) [SigmaFinite ν]
lemma ae_pi_snoc {P : (Fin (n+1) → E) → Prop} (hP : MeasurableSet {v | P v}) :
    (∀ᵐ v ∂Measure.pi (fun _ => ν), P v) ↔
      ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => ν), ∀ᵐ x ∂ν, P (Fin.snoc v x) := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) (Fin.last n)).symm
  rw [← hp.map_eq, MeasurableEmbedding.ae_map_iff (MeasurableEquiv.measurableEmbedding _)]
  have heq : (fun z : E × (Fin n → E) =>
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E) (Fin.last n)).symm z) =
      fun z => Fin.snoc z.2 z.1 := by
    ext z : 1
    change (Fin.last n).insertNth (α := fun _ => E) z.1 z.2 = _
    exact Fin.insertNth_last' z.1 z.2
  have hm : Measurable (fun z : E × (Fin n → E) => Fin.snoc (α := fun _ => E) z.2 z.1) := by
    rw [← heq]
    exact hp.measurable
  change (∀ᵐ z ∂ν.prod (Measure.pi (fun _ : Fin n => ν)),
      P ((fun z => (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E)
        (Fin.last n)).symm z) z)) ↔ _
  have hPP : MeasurableSet {z : E × (Fin n → E) | P (Fin.snoc z.2 z.1)} := hP.preimage hm
  rw [heq, Measure.ae_prod_iff_ae_ae hPP]
  exact Measure.ae_ae_comm hPP
end AePiLast

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma measurableSet_gramSchmidt_ne_zero (p : E) (n : ℕ) :
    MeasurableSet {v : Fin n → E | ∀ i, gramSchmidt ℝ (fun j => v j - p) i ≠ 0} := by
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  have h := (measurable_gramSchmidt i).comp
    (show Measurable (fun v : Fin n → E => fun j => v j - p) by fun_prop)
  exact (measurableSet_eq_fun h measurable_const).compl

/-- Successive affine degeneracies have product measure zero. -/
theorem ae_gramSchmidt_ne_zero {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1) (p : E)
    (n : ℕ) (hmargin : (n : ℝ) ≤ a) :
    ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => ν),
      ∀ i, gramSchmidt ℝ (fun j => v j - p) i ≠ 0 := by
  induction n with
  | zero => exact Filter.Eventually.of_forall fun _ i => Fin.elim0 i
  | succ n ih =>
    rw [ae_pi_snoc ν (measurableSet_gramSchmidt_ne_zero p (n+1))]
    have hn : (n : ℝ) ≤ a := by push_cast at hmargin; linarith
    filter_upwards [ih hn] with v hv
    let L := AffineSubspace.mk' p (Submodule.span ℝ (Set.range (fun i : Fin n => v i - p)))
    have hdim : (Module.finrank ℝ L.direction : ℝ) ≤ n := by
      dsimp [L]
      rw [AffineSubspace.direction_mk']
      have hh := finrank_range_le_card (R := ℝ) (fun i : Fin n => v i - p)
      simp only [Fintype.card_fin, Set.finrank] at hh
      exact_mod_cast hh
    have hnull : ν L = 0 := hν.affine_null hsupport L (by push_cast at hmargin; linarith)
    have ha : ∀ᵐ x ∂ν, x ∉ L := by
      rw [ae_iff]
      convert hnull using 2
      ext x
      simp
    filter_upwards [ha] with x hx
    intro i
    induction i using Fin.lastCases with
    | last =>
      apply norm_ne_zero_iff.mp
      rw [norm_gramSchmidt_sub_eq_affine_infDist, image_Iio_last]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact ne_of_gt ((L.closed_of_finiteDimensional.notMem_iff_infDist_pos
        ⟨p, AffineSubspace.self_mem_mk' _ _⟩).mp hx)
    | cast j => simpa only [gramSchmidt_castSucc, Fin.snoc_castSucc] using hv j

/-- The replica difference matrix has full column rank almost everywhere. -/
theorem ae_replica_linearIndependent {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1) (p : E)
    (n : ℕ) (hmargin : (n : ℝ) ≤ a) :
    ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => ν),
      LinearIndependent ℝ (fun j => v j - p) := by
  filter_upwards [ae_gramSchmidt_ne_zero hν hsupport p n hmargin] with v hv
  apply Matrix.linearIndependent_of_det_gram_ne_zero
  rw [det_gram_eq_prod_gramSchmidt]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (norm_ne_zero_iff.mpr (hv i))

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma sqrt_det_gram (n : ℕ) (v : Fin n → E) :
    Real.sqrt (Matrix.gram ℝ v).det = ∏ i, ‖gramSchmidt ℝ v i‖ := by
  rw [det_gram_eq_prod_gramSchmidt, Real.sqrt_prod _ (fun _ _ => sq_nonneg _)]
  simp only [Real.sqrt_sq (norm_nonneg _)]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma replicaWeight_eq_det (m : ℕ) (p : E) {n : ℕ} (v : Fin n → E) :
    replicaWeight m p v = ENNReal.ofReal
      ((Real.sqrt (Matrix.gram ℝ (fun j => v j - p)).det)⁻¹ ^ m) := by
  rw [sqrt_det_gram, ← Finset.prod_inv_distrib, ← Finset.prod_pow]
  exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)).symm

theorem gram_integral_bound {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1) (m : ℕ) (p : E)
    (n : ℕ) (hmargin : (n : ℝ) + m ≤ a) :
    ∫⁻ v : Fin n → E, ENNReal.ofReal
      ((Real.sqrt (Matrix.gram ℝ (fun j => v j - p)).det)⁻¹ ^ m)
      ∂Measure.pi (fun _ => ν) ≤ (replicaConstant ν a m)^n := by
  simpa only [← replicaWeight_eq_det] using replica_integral_bound hν hsupport m p n hmargin

end SubsphereRegression

end

end OAI
