import Mathlib
import OAI.Probability.JammingConcavity.Deletion

namespace OAI

/-! Deletion Uniform Gap Count Failure Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open scoped Topology BigOperators
open scoped ENNReal NNReal
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
open Classical
open scoped ENNReal NNReal Topology BigOperators MatrixOrder
open scoped NNReal BigOperators
open MeasureTheory Metric Set
open Metric
open scoped RealInnerProductSpace
namespace MicroscopicJamming

def varianceMark (ε : ℝ) (b : Bool) : ℝ≥0 :=
  Real.toNNReal (if b then 1+ε else 1-ε)

lemma coordinateLaw_sum (ε : ℝ) : coordinateLaw ε =
    ∑ b : Bool, (1/2 : ℝ≥0∞) • gaussianReal 0 (varianceMark ε b) := by
  simp [coordinateLaw, varianceMark, add_comm]

lemma coordinateLaw_apply_sum (ε : ℝ) (s : Set ℝ) :
    coordinateLaw ε s = ∑ b : Bool, (1/2:ℝ≥0∞) * gaussianReal 0 (varianceMark ε b) s := by
  rw [coordinateLaw_sum]
  exact Measure.finsetSum_apply _ _ _

lemma binary_product_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Bool → ℝ≥0∞) :
    (∑ σ : ι → Bool, (1/2:ℝ≥0∞)^Fintype.card ι * ∏ i, f i (σ i)) =
      ∏ i, ∑ b : Bool, (1/2:ℝ≥0∞) * f i b := by
  calc
    _ = ∑ σ : ι → Bool, ∏ i, ((1/2:ℝ≥0∞) * f i (σ i)) := by
      apply Finset.sum_congr rfl
      intro σ _
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    _ = _ := (Fintype.prod_sum (fun i b => (1/2:ℝ≥0∞) * f i b)).symm

lemma product_mixture_expansion {ι : Type*} [Fintype ι] [DecidableEq ι] (ε : ℝ) :
    (Measure.pi fun _ : ι => coordinateLaw ε) =
      ∑ σ : ι → Bool, (1/2 : ℝ≥0∞)^Fintype.card ι •
        Measure.pi (fun i => gaussianReal 0 (varianceMark ε (σ i))) := by
  classical
  refine Measure.pi_eq (μ := fun _ : ι => coordinateLaw ε) ?_
  intro s _
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  calc
    _ = ∑ σ : ι → Bool, (1/2:ℝ≥0∞)^Fintype.card ι *
        ∏ i, gaussianReal 0 (varianceMark ε (σ i)) (s i) := by
      apply Finset.sum_congr rfl
      intro σ _
      congr 1
      exact Measure.pi_pi _ _
    _ = ∏ i, ∑ b : Bool, (1/2:ℝ≥0∞) * gaussianReal 0 (varianceMark ε b) (s i) :=
      binary_product_expansion (fun i b => gaussianReal 0 (varianceMark ε b) (s i))
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact (coordinateLaw_apply_sum ε (s i)).symm

lemma gaussian_projection {ι : Type*} [Fintype ι] (v : ι → ℝ≥0) (w : ι → ℝ) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).map (fun a => ∑ i, w i * a i) =
      gaussianReal 0 (∑ i, NNReal.mk ((w i)^2) (sq_nonneg (w i)) * v i) := by
  classical
  let μ : Measure (ι → ℝ) := Measure.pi (fun i => gaussianReal 0 (v i))
  have hi : iIndepFun (fun i (a : ι → ℝ) => w i * a i) μ :=
    iIndepFun_pi (X := fun i x => w i * x) (fun _ => by fun_prop)
  have hmap : ∀ i, μ.map (fun a => w i * a i) =
      gaussianReal 0 (NNReal.mk ((w i)^2) (sq_nonneg (w i)) * v i) := by
    intro i
    rw [show (fun a => w i * a i) = (fun x => w i*x) ∘ (fun a : ι → ℝ => a i) from rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop),
      (measurePreserving_eval (fun i => gaussianReal 0 (v i)) i).map_eq,
      gaussianReal_map_const_mul]
    simp only [mul_zero]
  apply Measure.ext_of_charFun
  have hchar : charFun (μ.map (fun a => ∑ i, w i * a i)) =
      ∏ i, charFun (μ.map (fun a => w i * a i)) :=
    iIndepFun.charFun_map_fun_sum_eq_prod
      (fun i => (measurable_const.mul (measurable_pi_apply i)).aemeasurable) hi
  refine hchar.trans ?_
  ext t
  simp only [Finset.prod_apply, hmap, charFun_gaussianReal, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  rw [← Complex.exp_sum]
  congr 1
  simp only [NNReal.coe_sum, Complex.ofReal_sum]
  rw [Finset.sum_mul, Finset.sum_div, Finset.sum_neg_distrib]

lemma varianceMark_lower {ε : ℝ} (he : ε ∈ Set.Icc (0:ℝ) (1/2)) (b : Bool) :
    (1/2:ℝ) ≤ varianceMark ε b := by
  cases b <;> simp only [varianceMark, Bool.false_eq_true, ↓reduceIte]
  · rw [Real.coe_toNNReal _ (by linarith [he.2])]
    linarith [he.2]
  · rw [Real.coe_toNNReal _ (by linarith [he.1])]
    linarith [he.1]

lemma projectedVariance_lower {ι : Type*} [Fintype ι] {ε : ℝ}
    (he : ε ∈ Set.Icc (0:ℝ) (1/2)) (w : ι → ℝ) (hw : ∑ i, (w i)^2 = 1) (σ : ι → Bool) :
    (1/2:ℝ) ≤ (∑ i, NNReal.mk ((w i)^2) (sq_nonneg (w i)) * varianceMark ε (σ i) : ℝ≥0) := by
  simp only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_mk]
  calc
    (1/2:ℝ) = ∑ i, (w i)^2 * (1/2) := by rw [← Finset.sum_mul, hw, one_mul]
    _ ≤ _ := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (varianceMark_lower he (σ i)) (sq_nonneg (w i)))

 

lemma gaussianPDFReal_le_one {v : ℝ≥0} (hv : (1/2 : ℝ) ≤ v) (x : ℝ) :
    gaussianPDFReal 0 v x ≤ 1 := by
  have hroot : 1 ≤ Real.sqrt (2 * Real.pi * v) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    have hpi := Real.pi_gt_three
    nlinarith
  have hi : (Real.sqrt (2 * Real.pi * v))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hroot
  have he : Real.exp (-(x - 0)^2 / (2 * v)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  exact (mul_le_mul hi he (Real.exp_nonneg _) (by norm_num)).trans_eq (one_mul 1)

lemma gaussian_interval_bound {v : ℝ≥0} (hv : (1/2 : ℝ) ≤ v) (a b : ℝ) :
    gaussianReal 0 v (Set.Icc a b) ≤ ENNReal.ofReal (b - a) := by
  have hv0 : v ≠ 0 := by intro h; simp only [h, NNReal.coe_zero] at hv; norm_num at hv
  rw [gaussianReal_apply _ hv0]
  calc
    _ ≤ ∫⁻ _x in Set.Icc a b, (1 : ℝ≥0∞) := by
      apply lintegral_mono
      intro x
      exact ENNReal.ofReal_le_one.mpr (gaussianPDFReal_le_one hv x)
    _ = _ := by simp

lemma mixture_projection_interval_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {ε : ℝ}
    (he : ε ∈ Set.Icc (0 : ℝ) (1/2)) (w : ι → ℝ) (hw : ∑ i, (w i)^2 = 1)
    (a b : ℝ) :
    (Measure.pi fun _ : ι => coordinateLaw ε)
      {x | ∑ i, w i * x i ∈ Set.Icc a b} ≤ ENNReal.ofReal (b - a) := by
  classical
  have hwts : (∑ σ : ι → Bool, (1/2:ℝ≥0∞)^Fintype.card ι) = 1 := by
    have h := congrArg (fun ν : Measure (ι → ℝ) => ν univ)
      (product_mixture_expansion (ι := ι) ε)
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
      measure_univ, mul_one] at h
    exact h.symm
  rw [product_mixture_expansion, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  calc
    _ ≤ ∑ σ : ι → Bool, (1/2:ℝ≥0∞)^Fintype.card ι * ENNReal.ofReal (b-a) := by
      apply Finset.sum_le_sum
      intro σ _
      apply mul_le_mul' le_rfl
      have hmap := gaussian_projection (fun i => varianceMark ε (σ i)) w
      have hset : MeasurableSet (Set.Icc a b) := measurableSet_Icc
      have hh := congrArg (fun μ : Measure ℝ => μ (Set.Icc a b)) hmap
      rw [Measure.map_apply (by fun_prop) hset] at hh
      exact hh.trans_le (gaussian_interval_bound (projectedVariance_lower he w hw σ) a b)
    _ = _ := by rw [← Finset.sum_mul, hwts, one_mul]

def countHits {ι Ω : Type*} [Fintype ι] (s : Set Ω) (a : ι → Ω) : ℕ := by
  classical
  exact (Finset.univ.filter fun j => a j ∈ s).card

 

lemma iid_count_ge_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω) (m k : ℕ)
    (p : ℝ≥0∞) (hs : μ s ≤ p) :
    (Measure.pi fun _ : Fin m => μ)
      {a | k ≤ countHits s a} ≤
        (2 : ℝ≥0∞)^m * p^k := by
  classical
  let ν := Measure.pi fun _ : Fin m => μ
  let T := (Finset.univ : Finset (Fin m)).powersetCard k
  have hsub : {a : Fin m → Ω | k ≤ (Finset.univ.filter fun j => a j ∈ s).card} ⊆
      ⋃ t ∈ T, (↑t : Set (Fin m)).pi (fun _ => s) := by
    intro a ha
    obtain ⟨t, ht, hcard⟩ := Finset.exists_subset_card_eq ha
    refine Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
    · intro j hj
      exact (Finset.mem_filter.mp (ht hj)).2
  have hcard : T.card ≤ 2^m := by
    calc
      T.card ≤ (Finset.univ : Finset (Fin m)).powerset.card := by
        apply Finset.card_le_card
        intro t ht
        exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp ht).1
      _ = 2^m := by simp
  change ν {a | k ≤ (Finset.univ.filter fun j => a j ∈ s).card} ≤ _
  calc
    ν _ ≤ ν (⋃ t ∈ T, (↑t : Set (Fin m)).pi (fun _ => s)) := measure_mono hsub
    _ ≤ ∑ t ∈ T, ν ((↑t : Set (Fin m)).pi (fun _ => s)) :=
      measure_biUnion_finset_le T (fun t => (↑t : Set (Fin m)).pi (fun _ => s))
    _ ≤ ∑ _t ∈ T, p^k := by
      apply Finset.sum_le_sum
      intro t ht
      rw [Measure.pi_pi_finset]
      calc
        ∏ _j ∈ t, μ s = (μ s)^t.card := by simp
        _ ≤ p^t.card := pow_le_pow_left' hs _
        _ = p^k := by rw [(Finset.mem_powersetCard.mp ht).2]
    _ = (T.card : ℝ≥0∞) * p^k := by simp
    _ ≤ (2 : ℝ≥0∞)^m * p^k := by
      apply mul_le_mul' _ le_rfl
      exact_mod_cast hcard

lemma countHits_interval_lower {m : ℕ} (x : Fin m → ℝ) {t : ℝ} (ht : 0 < t)
    (k : ℕ) (hx : ∑ j, (x j)^2 ≤ ((m : ℝ) - k) * t^2) :
    k ≤ countHits (Set.Icc (-t) t) x := by
  classical
  let S := Finset.univ.filter fun j => x j ∈ Set.Icc (-t) t
  let T := Finset.univ \ S
  have hcard : S.card + T.card = m := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    dsimp [T]
    omega
  have hsq : (T.card : ℝ) * t^2 ≤ ∑ j, (x j)^2 := by
    calc
      (T.card : ℝ) * t^2 = ∑ _j ∈ T, t^2 := by simp
      _ ≤ ∑ j ∈ T, (x j)^2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hn : x j ∉ Set.Icc (-t) t := by simpa [T, S] using hj
        have ha : t ≤ |x j| := by
          by_contra h
          have hh := abs_lt.mp (lt_of_not_ge h)
          exact hn ⟨hh.1.le, hh.2.le⟩
        nlinarith [sq_abs (x j)]
      _ ≤ ∑ j, (x j)^2 := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  have hm : (S.card : ℝ) + T.card = m := by exact_mod_cast hcard
  have hk : (k : ℝ) ≤ S.card := by nlinarith [sq_pos_of_pos ht]
  have hS : countHits (Set.Icc (-t) t) x = S.card := by
    unfold countHits
    congr 1
    ext j
    simp [S]
  rw [hS]
  exact_mod_cast hk

lemma mixture_projection_count_bound {m n : ℕ} {ε : ℝ}
    (he : ε ∈ Set.Icc (0 : ℝ) (1/2)) (x : EuclideanSpace ℝ (Fin n))
    (hx : ‖x‖ = 1) (a b : ℝ) (k : ℕ) :
    (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => coordinateLaw ε)
      {A | k ≤ countHits (Set.Icc a b) (fun j => matrixOperator A x j)} ≤
        (2 : ℝ≥0∞)^m * (ENNReal.ofReal (b-a))^k := by
  have hs : ∑ i, (x i)^2 = 1 := by
    simpa [hx] using (EuclideanSpace.real_norm_sq_eq x).symm
  have h := iid_count_ge_bound (Measure.pi fun _ : Fin n => coordinateLaw ε)
    {r | ∑ i, x i * r i ∈ Set.Icc a b} m k _
    (mixture_projection_interval_bound he x hs a b)
  have hfun (A : Fin m → Fin n → ℝ) :
      (fun j => matrixOperator A x j) = (fun j => ∑ i, x i * A j i) := by
    funext j
    change (∑ i, A j i * x i) = _
    simp only [mul_comm]
  simp_rw [hfun]
  simpa only [countHits, Set.mem_ofPred_eq] using h

 

lemma mixture_image_small_ball {m n : ℕ} {ε : ℝ}
    (he : ε ∈ Set.Icc (0 : ℝ) (1/2)) (x : EuclideanSpace ℝ (Fin n))
    (hx : ‖x‖ = 1) {R t : ℝ} (hR : 0 ≤ R) (ht : 0 < t)
    (k : ℕ) (hk : R^2 ≤ ((m : ℝ) - k) * t^2) :
    (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => coordinateLaw ε)
      {A | ‖matrixOperator A x‖ ≤ R} ≤
        (2 : ℝ≥0∞)^m * (ENNReal.ofReal (2*t))^k := by
  calc
    _ ≤ (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => coordinateLaw ε)
        {A | k ≤ countHits (Set.Icc (-t) t) (fun j => matrixOperator A x j)} := by
      apply measure_mono
      intro A hA
      apply countHits_interval_lower _ ht
      rw [← EuclideanSpace.real_norm_sq_eq]
      exact ((sq_le_sq₀ (norm_nonneg _) hR).mpr hA).trans hk
    _ ≤ _ := by
      simpa only [sub_neg_eq_add, ← two_mul] using
        mixture_projection_count_bound he x hx (-t) t k

 
def transposeEquiv (m n : ℕ) : (Fin m → Fin n → ℝ) ≃ᵐ (Fin n → Fin m → ℝ) where
  toFun A j i := A i j
  invFun A i j := A j i
  left_inv := by intro A; rfl
  right_inv := by intro A; rfl
  measurable_toFun := by
    change Measurable (fun A : Fin m → Fin n → ℝ => fun j i => A i j)
    fun_prop
  measurable_invFun := by
    change Measurable (fun A : Fin n → Fin m → ℝ => fun i j => A j i)
    fun_prop

lemma measurePreserving_transpose (m n : ℕ) (ε : ℝ) :
    MeasurePreserving (transposeEquiv m n)
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => coordinateLaw ε)
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin m => coordinateLaw ε) := by
  have hu := measurePreserving_uncurry (fun _ : Fin m × Fin n => coordinateLaw ε)
  have hp := measurePreserving_piCongrLeft (fun _ : Fin n × Fin m => coordinateLaw ε)
    (Equiv.prodComm (Fin m) (Fin n))
  have hc := MeasurePreserving.symm (MeasurableEquiv.curry (Fin n) (Fin m) ℝ).symm
    (measurePreserving_uncurry (fun _ : Fin n × Fin m => coordinateLaw ε))
  exact hc.comp (hp.comp hu)

lemma matrixOperator_transpose {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    matrixOperator A.transpose = (matrixOperator A).adjoint := by
  unfold matrixOperator
  rw [← LinearMap.adjoint_toContinuousLinearMap]
  congr 1
  simpa using A.toEuclideanLin_conjTranspose_eq_adjoint

lemma mixture_adjoint_small_ball {m n : ℕ} {ε : ℝ}
    (he : ε ∈ Set.Icc (0 : ℝ) (1/2)) (v : EuclideanSpace ℝ (Fin m))
    (hv : ‖v‖ = 1) {R t : ℝ} (hR : 0 ≤ R) (ht : 0 < t)
    (k : ℕ) (hk : R^2 ≤ ((n : ℝ) - k) * t^2) :
    (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => coordinateLaw ε)
      {A | ‖(matrixOperator A).adjoint v‖ ≤ R} ≤
        (2 : ℝ≥0∞)^n * (ENNReal.ofReal (2*t))^k := by
  have hh := (measurePreserving_transpose m n ε).measure_preimage_emb
    (transposeEquiv m n).measurableEmbedding {A | ‖matrixOperator A v‖ ≤ R}
  have hset : (transposeEquiv m n) ⁻¹' {A | ‖matrixOperator A v‖ ≤ R} =
      {A | ‖(matrixOperator A).adjoint v‖ ≤ R} := by
    ext A
    change (‖matrixOperator (Matrix.transpose A) v‖ ≤ R) ↔ _
    exact Iff.of_eq (congrArg (fun L : EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin n) => ‖L v‖ ≤ R) (matrixOperator_transpose A))
  have hh' := (congrArg (fun s =>
    (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => coordinateLaw ε) s) hset).symm.trans hh
  exact hh'.trans_le (mixture_image_small_ball he v hv hR ht k hk)

 
def rowEmbeddingLinear {m : ℕ} (T : Finset (Fin m)) :
    EuclideanSpace ℝ T →ₗ[ℝ] EuclideanSpace ℝ (Fin m) := by
  classical
  exact {
    toFun := fun v => (EuclideanSpace.equiv (Fin m) ℝ).symm
      (fun i => if hi : i ∈ T then v ⟨i, hi⟩ else 0)
    map_add' := by intro v w; ext i; by_cases hi : i ∈ T <;> simp [hi]
    map_smul' := by intro r v; ext i; by_cases hi : i ∈ T <;> simp [hi] }

def rowEmbedding {m : ℕ} (T : Finset (Fin m)) :
    EuclideanSpace ℝ T →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (rowEmbeddingLinear T).toContinuousLinearMap

lemma rowEmbedding_norm {m : ℕ} (T : Finset (Fin m)) (v : EuclideanSpace ℝ T) :
    ‖rowEmbedding T v‖ = ‖v‖ := by
  classical
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  have hs : (∑ i : Fin m, (rowEmbedding T v i)^2) =
      ∑ i ∈ T, (rowEmbedding T v i)^2 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    simp [rowEmbedding, rowEmbeddingLinear, hi]
  rw [hs, ← Finset.sum_coe_sort T (fun i => (rowEmbedding T v i)^2)]
  apply Finset.sum_congr rfl
  intro i _
  simp [rowEmbedding, rowEmbeddingLinear, i.property]

lemma rowEmbedding_inner {m : ℕ} (T : Finset (Fin m))
    (v : EuclideanSpace ℝ T) (z : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (rowEmbedding T v) z =
      inner ℝ v ((EuclideanSpace.equiv T ℝ).symm (fun i => z i)) := by
  classical
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  have hs : (∑ i : Fin m, z i * rowEmbedding T v i) =
      ∑ i ∈ T, z i * rowEmbedding T v i := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    simp [rowEmbedding, rowEmbeddingLinear, hi]
  rw [hs, ← Finset.sum_coe_sort T (fun i => z i * rowEmbedding T v i)]
  apply Finset.sum_congr rfl
  intro i _
  simp [rowEmbedding, rowEmbeddingLinear, i.property]

lemma net_point_small_image {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (S : Finset E) {δ K c : ℝ}
    (_hδ : 0 ≤ δ) (hK : 0 ≤ K) (hL : ∀ z, ‖L z‖ ≤ K * ‖z‖)
    (hnet : ∀ x : E, ‖x‖ = 1 → ∃ y ∈ S, dist x y ≤ δ)
    (v : E) (hv : ‖v‖ = 1) (hvL : ‖L v‖ < c) :
    ∃ y ∈ S, ‖L y‖ ≤ c + K * δ := by
  obtain ⟨y, hy, hdist⟩ := hnet v hv
  refine ⟨y, hy, ?_⟩
  calc
    ‖L y‖ ≤ ‖L v‖ + ‖L (y-v)‖ := by
      simpa only [map_sub, add_sub_cancel] using norm_add_le (L v) (L (y-v))
    _ ≤ c + K * δ := by
      apply add_le_add hvL.le
      exact (hL (y-v)).trans (mul_le_mul_of_nonneg_left
        (by simpa only [dist_eq_norm, norm_sub_rev] using hdist) hK)

 

lemma uniform_row_lower_failure_bound {m n : ℕ} {ε : ℝ}
    (he : ε ∈ Set.Icc (0 : ℝ) (1/2)) (b k : ℕ) {K c t : ℝ}
    (hK : 0 < K) (hc : 0 < c) (ht : 0 < t)
    (hk : (2*c)^2 ≤ ((n : ℝ) - k) * t^2) :
    (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => coordinateLaw ε)
      {A | ‖matrixOperator A‖ ≤ K ∧
        ∃ T : Finset (Fin m), T.card ≤ b ∧
          ∃ v : EuclideanSpace ℝ T, ‖v‖ = 1 ∧
            ‖(matrixOperator A).adjoint (rowEmbedding T v)‖ < c} ≤
      (2 : ℝ≥0∞)^m * ENNReal.ofReal ((1+2*K/c)^b) *
        ((2 : ℝ≥0∞)^n * (ENNReal.ofReal (2*t))^k) := by
  classical
  let ν := Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => coordinateLaw ε
  let P := (Finset.univ : Finset (Finset (Fin m))).filter fun T => T.card ≤ b
  let p : ℝ≥0∞ := (2 : ℝ≥0∞)^n * (ENNReal.ofReal (2*t))^k
  have hnets (T : Finset (Fin m)) :=
    unit_sphere_net (E := EuclideanSpace ℝ T) (div_pos hc hK)
  choose S hS hnet hcard using hnets
  have hcard' (T : Finset (Fin m)) (hT : T ∈ P) :
      (S T).card ≤ ENNReal.ofReal ((1+2*K/c)^b) := by
    have hh : ((S T).card : ℝ) ≤ (1+2*K/c)^b := by
      have heq : (1+2/(c/K)) = 1+2*K/c := by field_simp
      have hh := hcard T
      rw [heq, finrank_euclideanSpace, Fintype.card_coe] at hh
      apply hh.trans
      exact pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity))
        (Finset.mem_filter.mp hT).2
    exact_mod_cast ENNReal.ofReal_le_ofReal hh
  have hsub : {A : Fin m → Fin n → ℝ | ‖matrixOperator A‖ ≤ K ∧
        ∃ T : Finset (Fin m), T.card ≤ b ∧
          ∃ v : EuclideanSpace ℝ T, ‖v‖ = 1 ∧
            ‖(matrixOperator A).adjoint (rowEmbedding T v)‖ < c} ⊆
      ⋃ T ∈ P, ⋃ v ∈ S T,
        {A | ‖(matrixOperator A).adjoint (rowEmbedding T v)‖ ≤ 2*c} := by
    rintro A ⟨hA, T, hT, v, hv, hAv⟩
    have hL : ∀ z : EuclideanSpace ℝ T,
        ‖((matrixOperator A).adjoint.comp (rowEmbedding T)) z‖ ≤ K * ‖z‖ := by
      intro z
      calc
        _ ≤ ‖(matrixOperator A).adjoint‖ * ‖rowEmbedding T z‖ :=
          (matrixOperator A).adjoint.le_opNorm _
        _ ≤ K * ‖z‖ := by
          rw [ContinuousLinearMap.adjoint.norm_map, rowEmbedding_norm]
          exact mul_le_mul_of_nonneg_right hA (norm_nonneg z)
    obtain ⟨w, hw, hwA⟩ := net_point_small_image
      ((matrixOperator A).adjoint.comp (rowEmbedding T)) (S T)
      (div_nonneg hc.le hK.le) hK.le hL (hnet T) v hv hAv
    have heq : c + K*(c/K) = 2*c := by
      rw [mul_div_cancel₀ _ hK.ne']
      ring
    rw [heq] at hwA
    exact Set.mem_iUnion.mpr ⟨T, Set.mem_iUnion.mpr ⟨by simp [P, hT],
      Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr ⟨hw, hwA⟩⟩⟩⟩
  have hP : (P.card : ℝ≥0∞) ≤ (2 : ℝ≥0∞)^m := by
    have hh : P.card ≤ 2^m := by
      calc
        P.card ≤ (Finset.univ : Finset (Finset (Fin m))).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = 2^m := by simp
    exact_mod_cast hh
  change ν _ ≤ _
  calc
    _ ≤ ν (⋃ T ∈ P, ⋃ v ∈ S T,
        {A | ‖(matrixOperator A).adjoint (rowEmbedding T v)‖ ≤ 2*c}) := measure_mono hsub
    _ ≤ ∑ T ∈ P, ν (⋃ v ∈ S T,
        {A | ‖(matrixOperator A).adjoint (rowEmbedding T v)‖ ≤ 2*c}) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ T ∈ P, ((S T).card : ℝ≥0∞) * p := by
      apply Finset.sum_le_sum
      intro T _
      calc
        _ ≤ ∑ v ∈ S T, ν {A | ‖(matrixOperator A).adjoint (rowEmbedding T v)‖ ≤ 2*c} :=
          measure_biUnion_finset_le _ _
        _ ≤ ∑ _v ∈ S T, p := by
          apply Finset.sum_le_sum
          intro v hv
          exact mixture_adjoint_small_ball he (rowEmbedding T v)
            ((rowEmbedding_norm T v).trans (hS T v hv)) (by positivity) ht k hk
        _ = _ := by simp
    _ ≤ ∑ _T ∈ P, ENNReal.ofReal ((1+2*K/c)^b) * p := by
      apply Finset.sum_le_sum
      intro T hT
      exact mul_le_mul' (hcard' T hT) le_rfl
    _ = (P.card : ℝ≥0∞) * ENNReal.ofReal ((1+2*K/c)^b) * p := by
      simp [mul_assoc]
    _ ≤ _ := mul_le_mul' (mul_le_mul' hP le_rfl) le_rfl

 

lemma interval_count_stability {m : ℕ} (g h : Fin m → ℝ) {u : ℝ} (hu : 0 < u) :
    ((countHits (Set.Icc (-u) u) g : ℝ) - countHits (Set.Icc (-(2*u)) (2*u)) h) * u^2 ≤
      ∑ j, (g j - h j)^2 := by
  classical
  let S := Finset.univ.filter fun j => g j ∈ Set.Icc (-u) u
  let T := Finset.univ.filter fun j => h j ∈ Set.Icc (-(2*u)) (2*u)
  let U := S \ T
  have hS : countHits (Set.Icc (-u) u) g = S.card := by
    unfold countHits; congr 1; ext j; simp [S]
  have hT : countHits (Set.Icc (-(2*u)) (2*u)) h = T.card := by
    unfold countHits; congr 1; ext j; simp [T]
  have hcard : S.card ≤ T.card + U.card := by
    calc
      S.card ≤ (T ∪ U).card := by
        apply Finset.card_le_card
        intro j hj
        by_cases hjT : j ∈ T
        · exact Finset.mem_union_left _ hjT
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hj, hjT⟩)
      _ ≤ T.card + U.card := Finset.card_union_le _ _
  have hsq : (U.card : ℝ) * u^2 ≤ ∑ j, (g j - h j)^2 := by
    calc
      (U.card : ℝ) * u^2 = ∑ _j ∈ U, u^2 := by simp
      _ ≤ ∑ j ∈ U, (g j - h j)^2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hg : |g j| ≤ u := abs_le.mpr ((Finset.mem_filter.mp
          (Finset.mem_sdiff.mp hj).1).2)
        have hh : 2*u < |h j| := by
          apply lt_of_not_ge
          intro hh
          exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, abs_le.mp hh⟩)
        have hab := abs_sub_abs_le_abs_sub (h j) (g j)
        have hdiff : u ≤ |g j-h j| := by rw [abs_sub_comm] at hab; linarith
        nlinarith [sq_abs (g j-h j)]
      _ ≤ ∑ j, (g j-h j)^2 := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  rw [hS, hT]
  have hcard' : (S.card : ℝ) ≤ T.card + U.card := by exact_mod_cast hcard
  exact (mul_le_mul_of_nonneg_right (by linarith : (S.card : ℝ)-T.card ≤ U.card)
    (sq_nonneg u)).trans hsq

 
def nearGapCount {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (u : ℝ) : ℕ :=
  countHits (Set.Icc (-u) u) (fun j => 1 + matrixOperator A x j)

lemma nearGapCount_fixed_bound {m n : ℕ} {ε : ℝ}
    (he : ε ∈ Set.Icc (0 : ℝ) (1/2)) (x : EuclideanSpace ℝ (Fin n))
    (hx : ‖x‖ = 1) (u : ℝ) (k : ℕ) :
    (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => coordinateLaw ε)
      {A | k ≤ nearGapCount A x u} ≤
        (2 : ℝ≥0∞)^m * (ENNReal.ofReal (2*u))^k := by
  have h := mixture_projection_count_bound (m := m) he x hx (-u-1) (u-1) k
  have hcount (A : Fin m → Fin n → ℝ) : nearGapCount A x u =
      countHits (Set.Icc (-u-1) (u-1)) (fun j => matrixOperator A x j) := by
    unfold nearGapCount countHits
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_Icc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  simp_rw [hcount]
  convert h using 1
  congr 3
  ring

lemma nearGapCount_net_transfer {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) {u δ K C : ℝ} (hu : 0 < u)
    (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hA : ‖matrixOperator A‖ ≤ K)
    (hxy : dist x y ≤ δ) (k : ℕ) (hC : K^2 * δ^2 ≤ (C-k) * u^2)
    (hx : C ≤ nearGapCount A x u) : k ≤ nearGapCount A y (2*u) := by
  let L := matrixOperator A
  have hdiff : ‖L (x-y)‖ ≤ K*δ := by
    calc
      _ ≤ ‖L‖*‖x-y‖ := L.le_opNorm _
      _ ≤ K*δ := mul_le_mul hA (by simpa [dist_eq_norm] using hxy)
        (norm_nonneg _) hK
  have hsq : ‖L (x-y)‖^2 ≤ K^2 * δ^2 := by
    calc
      _ ≤ (K*δ)^2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK hδ)).mpr hdiff
      _ = _ := mul_pow _ _ _
  have hc := interval_count_stability (fun j => 1 + L x j) (fun j => 1 + L y j) hu
  have heq : (∑ j, ((1+L x j)-(1+L y j))^2) = ‖L (x-y)‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro j _
    simp only [map_sub, PiLp.sub_apply]
    congr 1
    ring
  rw [heq] at hc
  change ((nearGapCount A x u : ℝ) - nearGapCount A y (2*u)) * u^2 ≤ _ at hc
  have hreal : (k : ℝ) ≤ nearGapCount A y (2*u) := by
    nlinarith [sq_pos_of_pos hu]
  exact_mod_cast hreal

 

lemma uniform_gap_count_failure_bound {m n : ℕ} {ε : ℝ}
    (he : ε ∈ Set.Icc (0 : ℝ) (1/2)) (k : ℕ) {K u δ C : ℝ}
    (hK : 0 ≤ K) (hu : 0 < u) (hδ : 0 < δ)
    (hC : K^2 * δ^2 ≤ (C-k) * u^2) :
    (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => coordinateLaw ε)
      {A | ‖matrixOperator A‖ ≤ K ∧ ∃ x : EuclideanSpace ℝ (Fin n),
        ‖x‖ = 1 ∧ C < nearGapCount A x u} ≤
      ENNReal.ofReal ((1+2/δ)^n) *
        ((2 : ℝ≥0∞)^m * (ENNReal.ofReal (4*u))^k) := by
  classical
  let ν := Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => coordinateLaw ε
  obtain ⟨S, hS, hnet, hcard⟩ := unit_sphere_net (E := EuclideanSpace ℝ (Fin n)) hδ
  have hsub : {A : Fin m → Fin n → ℝ | ‖matrixOperator A‖ ≤ K ∧ ∃ x : EuclideanSpace ℝ (Fin n),
        ‖x‖ = 1 ∧ C < nearGapCount A x u} ⊆
      ⋃ y ∈ S, {A | k ≤ nearGapCount A y (2*u)} := by
    rintro A ⟨hA, x, hx, hCx⟩
    obtain ⟨y, hy, hxy⟩ := hnet x hx
    exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy,
      nearGapCount_net_transfer A x y hu hδ.le hK hA hxy k hC hCx.le⟩⟩
  have hcard' : (S.card : ℝ≥0∞) ≤ ENNReal.ofReal ((1+2/δ)^n) := by
    rw [finrank_euclideanSpace, Fintype.card_fin] at hcard
    exact_mod_cast ENNReal.ofReal_le_ofReal hcard
  change ν _ ≤ _
  calc
    _ ≤ ν (⋃ y ∈ S, {A | k ≤ nearGapCount A y (2*u)}) := measure_mono hsub
    _ ≤ ∑ y ∈ S, ν {A | k ≤ nearGapCount A y (2*u)} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ S, ((2 : ℝ≥0∞)^m * (ENNReal.ofReal (4*u))^k) := by
      apply Finset.sum_le_sum
      intro y hy
      simpa only [show 2*(2*u) = 4*u by ring] using
        nearGapCount_fixed_bound (m := m) he y (hS y hy) (2*u) k
    _ = (S.card : ℝ≥0∞) * ((2 : ℝ≥0∞)^m * (ENNReal.ofReal (4*u))^k) := by simp
    _ ≤ _ := mul_le_mul' hcard' le_rfl

end MicroscopicJamming

end

end OAI
