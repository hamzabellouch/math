import Mathlib
import OAI.Probability.SKGap.Localization.ExpSum

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
namespace SKGap
variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {ι : Type*} [Fintype ι] [Nonempty ι]
omit [Fintype ι] [Nonempty ι] in
theorem interpolation_increment_identity {n : ℕ} (a b : ι → Fin n → ℝ) (i j : ι) (t : ℝ)
    (horth : ∑ k, (a i k - a j k) * (b i k - b j k) = 0) :
    (∑ k, (interpolatedCoeffDeriv a b t i k - interpolatedCoeffDeriv a b t j k) *
      (interpolatedCoeff a b t i k - interpolatedCoeff a b t j k)) =
      sin t * cos t * ((∑ k, (a i k - a j k) ^ 2) - ∑ k, (b i k - b j k) ^ 2) := by
  have he (k : Fin n) :
      (interpolatedCoeffDeriv a b t i k - interpolatedCoeffDeriv a b t j k) *
        (interpolatedCoeff a b t i k - interpolatedCoeff a b t j k) =
      sin t * cos t * (a i k - a j k)^2 - sin t * cos t * (b i k - b j k)^2 +
        (cos t ^ 2 - sin t ^ 2) * ((a i k - a j k) * (b i k - b j k)) := by
    dsimp [interpolatedCoeff, interpolatedCoeffDeriv]
    ring
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [horth]
  ring

theorem interpolation_derivative_nonneg {n : ℕ} {κ : ℝ} (hκ : 0 ≤ κ)
    (m : ι → ℝ) (a b : ι → Fin (n + 1) → ℝ)
    (horth : ∀ i j, ∑ k, (a i k - a j k) * (b i k - b j k) = 0)
    (hinc : ∀ i j, (∑ k, (b i k - b j k)^2) ≤ ∑ k, (a i k - a j k)^2)
    {t : ℝ} (ht : t ∈ Icc 0 (π / 2)) :
    0 ≤ ∫ z, interpolationDerivative κ m a b t z ∂standardGaussianProduct (n + 1) := by
  have hs : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [pi_pos, ht.2])
  have hc : 0 ≤ cos t := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos, ht.1], ht.2⟩
  rw [show (fun z => interpolationDerivative κ m a b t z) =
      (fun z => ∑ i, softWeight κ (affineProcess m (interpolatedCoeff a b t) z) i *
        ∑ k, interpolatedCoeffDeriv a b t i k * z k) from rfl,
    gaussian_linear_weight_IBP]
  apply mul_nonneg (div_nonneg hκ (by norm_num))
  apply integral_nonneg
  intro z
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (mul_nonneg (softWeight_pos _ _ _).le (softWeight_pos _ _ _).le)
  rw [interpolation_increment_identity a b i j t (horth i j)]
  exact mul_nonneg (mul_nonneg hs hc) (sub_nonneg.mpr (hinc i j))

theorem gaussian_smoothMax_comparison {n : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (m : ι → ℝ) (a b : ι → Fin (n + 1) → ℝ)
    (horth : ∀ i j, ∑ k, (a i k - a j k) * (b i k - b j k) = 0)
    (hinc : ∀ i j, (∑ k, (b i k - b j k)^2) ≤ ∑ k, (a i k - a j k)^2) :
    (∫ z, smoothMax κ (affineProcess m b z) ∂standardGaussianProduct (n + 1)) ≤
      ∫ z, smoothMax κ (affineProcess m a z) ∂standardGaussianProduct (n + 1) := by
  let f := fun t => ∫ z, smoothMax κ (affineProcess m (interpolatedCoeff a b t) z)
    ∂standardGaussianProduct (n + 1)
  have hmono : MonotoneOn f (Icc 0 (π / 2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (continuous_iff_continuousAt.mpr (fun t => (interpolation_hasDerivAt hκ m a b t).continuousAt)).continuousOn
      (fun t _ => (interpolation_hasDerivAt hκ m a b t).hasDerivWithinAt)
    intro t ht
    exact interpolation_derivative_nonneg hκ.le m a b horth hinc (interior_subset ht)
  have hle := hmono (show (0:ℝ) ∈ Icc 0 (π/2) from ⟨le_refl _, by positivity⟩)
    (show π/2 ∈ Icc (0:ℝ) (π/2) from ⟨by positivity, le_refl _⟩) (by positivity)
  have h0 : interpolatedCoeff a b 0 = b := by
    funext i k
    simp [interpolatedCoeff]
  have h1 : interpolatedCoeff a b (π/2) = a := by
    funext i k
    simp [interpolatedCoeff]
  simpa only [f, h0, h1] using hle

def finiteMax (x : ι → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty x

theorem le_finiteMax (x : ι → ℝ) (i : ι) : x i ≤ finiteMax x :=
  Finset.le_sup' x (Finset.mem_univ i)

theorem finiteMax_le {x : ι → ℝ} {b : ℝ} (hb : ∀ i, x i ≤ b) : finiteMax x ≤ b :=
  Finset.sup'_le _ _ (fun i _ => hb i)

theorem continuous_finiteMax : Continuous (finiteMax : (ι → ℝ) → ℝ) :=
  Continuous.finset_sup'_apply Finset.univ_nonempty (fun i _ => continuous_apply i)

theorem finiteMax_norm_le (x : ι → ℝ) : ‖finiteMax x‖ ≤ ∑ i, |x i| := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty x
  change ‖Finset.univ.sup' Finset.univ_nonempty x‖ ≤ _
  rw [hi, Real.norm_eq_abs]
  exact Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)

omit [Fintype ι] [Nonempty ι] in
theorem integrable_affineProcess {n : ℕ} (m : ι → ℝ) (a : ι → Fin n → ℝ) (i : ι) :
    Integrable (fun z => affineProcess m a z i) (standardGaussianProduct n) := by
  apply (integrable_const _).add
  exact integrable_finsetSum _ (fun k _ => (integrable_eval (i := k) IsGaussian.integrable_id).const_mul _)

theorem integrable_finiteMax_affine {n : ℕ} (m : ι → ℝ) (a : ι → Fin n → ℝ) :
    Integrable (fun z => finiteMax (affineProcess m a z)) (standardGaussianProduct n) := by
  apply (integrable_finsetSum _ (fun i _ => (integrable_affineProcess m a i).norm)).mono'
    (continuous_finiteMax.comp (continuous_affineProcess m a)).aestronglyMeasurable
  exact ae_of_all _ (fun z => finiteMax_norm_le _)

theorem integrable_smoothMax_affine {n : ℕ} {κ : ℝ} (hκ : 0 < κ) (m : ι → ℝ) (a : ι → Fin n → ℝ) :
    Integrable (fun z => smoothMax κ (affineProcess m a z)) (standardGaussianProduct n) := by
  apply ((integrable_finsetSum _ (fun i _ => (integrable_affineProcess m a i).norm)).add
    (integrable_const (log (Fintype.card ι) / κ))).mono'
    ((continuous_smoothMax κ).comp (continuous_affineProcess m a)).aestronglyMeasurable
  exact ae_of_all _ (fun z => smoothMax_norm_le hκ _)

theorem gaussian_finiteMax_comparison {n : ℕ}
    (m : ι → ℝ) (a b : ι → Fin (n + 1) → ℝ)
    (horth : ∀ i j, ∑ k, (a i k - a j k) * (b i k - b j k) = 0)
    (hinc : ∀ i j, (∑ k, (b i k - b j k)^2) ≤ ∑ k, (a i k - a j k)^2) :
    (∫ z, finiteMax (affineProcess m b z) ∂standardGaussianProduct (n + 1)) ≤
      ∫ z, finiteMax (affineProcess m a z) ∂standardGaussianProduct (n + 1) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hlog : 0 ≤ log (Fintype.card ι) := log_nonneg (by exact_mod_cast Fintype.card_pos)
  let κ := (log (Fintype.card ι) + 1) / ε
  have hκ : 0 < κ := div_pos (by linarith) hε
  have herr : log (Fintype.card ι) / κ ≤ ε := by
    apply (div_le_iff₀ hκ).mpr
    dsimp [κ]
    rw [mul_div_cancel₀ _ hε.ne']
    linarith
  calc
    _ ≤ ∫ z, smoothMax κ (affineProcess m b z) ∂standardGaussianProduct (n + 1) := by
      apply integral_mono (integrable_finiteMax_affine m b) (integrable_smoothMax_affine hκ m b)
      intro z
      exact finiteMax_le (fun i => smoothMax_ge hκ _ i)
    _ ≤ ∫ z, smoothMax κ (affineProcess m a z) ∂standardGaussianProduct (n + 1) :=
      gaussian_smoothMax_comparison hκ m a b horth hinc
    _ ≤ (∫ z, finiteMax (affineProcess m a z) ∂standardGaussianProduct (n + 1)) + ε := by
      calc
        _ ≤ ∫ z, finiteMax (affineProcess m a z) + log (Fintype.card ι) / κ
            ∂standardGaussianProduct (n + 1) := by
          apply integral_mono (integrable_smoothMax_affine hκ m a)
            ((integrable_finiteMax_affine m a).add (integrable_const _))
          intro z
          exact smoothMax_le hκ _ (fun i => le_finiteMax _ i)
        _ = (∫ z, finiteMax (affineProcess m a z) ∂standardGaussianProduct (n + 1)) +
            log (Fintype.card ι) / κ := by
          rw [integral_add (integrable_finiteMax_affine m a) (integrable_const _)]
          simp
        _ ≤ _ := add_le_add (le_refl _) herr

section CompactIndex
variable {I : Type*} [TopologicalSpace I] [CompactSpace I] [Nonempty I]

def supProcess {n : ℕ} (m : I → ℝ) (a : I → Fin n → ℝ) (z : Fin n → ℝ) : ℝ :=
  sSup (Set.range (affineProcess m a z))

omit [CompactSpace I] [Nonempty I] in
theorem continuous_affine_index {n : ℕ} {m : I → ℝ} {a : I → Fin n → ℝ}
    (hm : Continuous m) (ha : Continuous a) (z : Fin n → ℝ) :
    Continuous (affineProcess m a z) := by
  exact hm.add (continuous_finsetSum _ (fun k _ => ((continuous_apply k).comp ha).mul continuous_const))

theorem supProcess_attained {n : ℕ} {m : I → ℝ} {a : I → Fin n → ℝ}
    (hm : Continuous m) (ha : Continuous a) (z : Fin n → ℝ) :
    ∃ i, supProcess m a z = affineProcess m a z i ∧
      ∀ j, affineProcess m a z j ≤ affineProcess m a z i := by
  obtain ⟨i, _, he, hi⟩ := isCompact_univ.exists_sSup_image_eq_and_ge
    Set.univ_nonempty (continuous_affine_index hm ha z).continuousOn
  exact ⟨i, by simpa [supProcess] using he, fun j => hi j (Set.mem_univ _)⟩

theorem affine_le_supProcess {n : ℕ} {m : I → ℝ} {a : I → Fin n → ℝ}
    (hm : Continuous m) (ha : Continuous a) (z : Fin n → ℝ) (i : I) :
    affineProcess m a z i ≤ supProcess m a z := by
  obtain ⟨j, he, hj⟩ := supProcess_attained hm ha z
  rw [he]
  exact hj i

theorem supProcess_le {n : ℕ} {m : I → ℝ} {a : I → Fin n → ℝ}
    (hm : Continuous m) (ha : Continuous a) (z : Fin n → ℝ) {c : ℝ}
    (hc : ∀ i, affineProcess m a z i ≤ c) : supProcess m a z ≤ c := by
  obtain ⟨i, he, _⟩ := supProcess_attained hm ha z
  rw [he]
  exact hc i

omit [Nonempty I] in
theorem continuous_supProcess {n : ℕ} {m : I → ℝ} {a : I → Fin n → ℝ}
    (hm : Continuous m) (ha : Continuous a) : Continuous (supProcess m a) := by
  have hc : Continuous (fun p : (Fin n → ℝ) × I => affineProcess m a p.1 p.2) := by
    exact (hm.comp continuous_snd).add (continuous_finsetSum _ (fun k _ =>
      (((continuous_apply k).comp ha).comp continuous_snd).mul
        ((continuous_apply k).comp continuous_fst)))
  change Continuous (fun z => sSup (Set.range (affineProcess m a z)))
  simpa only [Set.image_univ] using isCompact_univ.continuous_sSup hc

omit [TopologicalSpace I] [CompactSpace I] [Nonempty I] in
 theorem affineProcess_abs_le {n : ℕ} {m : I → ℝ} {a : I → Fin n → ℝ}
    {M A : ℝ} (hm : ∀ i, |m i| ≤ M) (ha : ∀ i k, |a i k| ≤ A)
    (z : Fin n → ℝ) (i : I) :
    |affineProcess m a z i| ≤ M + A * ∑ k, |z k| := by
  calc
    _ ≤ |m i| + |∑ k, a i k * z k| := abs_add_le _ _
    _ ≤ M + ∑ k, |a i k * z k| := add_le_add (hm i) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ M + ∑ k, A * |z k| := by
      gcongr with k
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (ha i k) (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

theorem integrable_supProcess {n : ℕ} {m : I → ℝ} {a : I → Fin n → ℝ}
    (hm : Continuous m) (ha : Continuous a) :
    Integrable (supProcess m a) (standardGaussianProduct n) := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hm.continuousOn
  obtain ⟨A, hA⟩ := isCompact_univ.exists_bound_of_continuousOn ha.continuousOn
  have hMb : ∀ i, |m i| ≤ M := fun i => by simpa only [Real.norm_eq_abs] using hM i (Set.mem_univ _)
  have hAb : ∀ i k, |a i k| ≤ A := by
    intro i k
    have hk : |a i k| ≤ ‖a i‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (a i) k
    exact hk.trans (hA i (Set.mem_univ _))
  apply ((integrable_const M).add ((integrable_finsetSum _ (fun k _ =>
    ((integrable_eval (i := k) IsGaussian.integrable_id).norm))).const_mul A)).mono'
    (continuous_supProcess hm ha).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  obtain ⟨i, he, _⟩ := supProcess_attained hm ha z
  rw [he, Real.norm_eq_abs]
  exact affineProcess_abs_le hMb hAb z i

theorem exists_finite_affine_net {n : ℕ} {m : I → ℝ} {a : I → Fin n → ℝ}
    (hm : Continuous m) (ha : Continuous a) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : Finset I, t.Nonempty ∧ ∀ j, ∃ i ∈ t,
      |m j - m i| ≤ ε ∧ ∀ k, |a j k - a i k| ≤ ε := by
  let U : I → Set I := fun i => m ⁻¹' Metric.ball (m i) ε ∩ a ⁻¹' Metric.ball (a i) ε
  have ho (i : I) : IsOpen (U i) :=
    (Metric.isOpen_ball.preimage hm).inter (Metric.isOpen_ball.preimage ha)
  have hu : Set.univ ⊆ ⋃ i, U i := by
    intro j _
    apply Set.mem_iUnion.mpr
    exact ⟨j, by simp [U, hε]⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U ho hu
  have hcover (j : I) : ∃ i ∈ t, j ∈ U i := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ j))
    obtain ⟨hit, hji⟩ := Set.mem_iUnion.mp hi
    exact ⟨i, hit, hji⟩
  have hne : t.Nonempty := by
    obtain ⟨i, hi, _⟩ := hcover (Classical.choice inferInstance)
    exact ⟨i, hi⟩
  refine ⟨t, hne, fun j => ?_⟩
  obtain ⟨i, hi, hj⟩ := hcover j
  refine ⟨i, hi, ?_, fun k => ?_⟩
  · have hd : dist (m j) (m i) < ε := hj.1
    simpa only [Real.dist_eq] using hd.le
  · have hb : dist (a j) (a i) < ε := hj.2
    have hk := (dist_le_pi_dist (a j) (a i) k).trans_lt hb
    simpa only [Real.dist_eq] using hk.le

omit [TopologicalSpace I] [CompactSpace I] [Nonempty I] in
 theorem affineProcess_difference_abs_le {n : ℕ} (m : I → ℝ) (a : I → Fin n → ℝ)
    {ε : ℝ} {i j : I} (hm : |m i - m j| ≤ ε)
    (ha : ∀ k, |a i k - a j k| ≤ ε) (z : Fin n → ℝ) :
    |affineProcess m a z i - affineProcess m a z j| ≤ ε * (1 + ∑ k, |z k|) := by
  have he : affineProcess m a z i - affineProcess m a z j =
      (m i - m j) + ∑ k, (a i k - a j k) * z k := by
    simp only [affineProcess, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [he]
  calc
    _ ≤ |m i - m j| + |∑ k, (a i k - a j k) * z k| := abs_add_le _ _
    _ ≤ ε + ∑ k, |(a i k - a j k) * z k| :=
      add_le_add hm (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ε + ∑ k, ε * |z k| := by
      gcongr with k
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (ha k) (abs_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem gaussian_supProcess_comparison {n : ℕ}
    {m : I → ℝ} {a b : I → Fin (n + 1) → ℝ}
    (hm : Continuous m) (ha : Continuous a) (hb : Continuous b)
    (horth : ∀ i j, ∑ k, (a i k - a j k) * (b i k - b j k) = 0)
    (hinc : ∀ i j, (∑ k, (b i k - b j k)^2) ≤ ∑ k, (a i k - a j k)^2) :
    (∫ z, supProcess m b z ∂standardGaussianProduct (n + 1)) ≤
      ∫ z, supProcess m a z ∂standardGaussianProduct (n + 1) := by
  let μ := standardGaussianProduct (n + 1)
  let Z : (Fin (n + 1) → ℝ) → ℝ := fun z => 1 + ∑ k, |z k|
  have hZI : Integrable Z μ := (integrable_const 1).add
    (integrable_finsetSum _ (fun k _ => by
      have hi : Integrable (fun z : Fin (n + 1) → ℝ => z k) μ :=
        integrable_eval (i := k) IsGaussian.integrable_id
      simpa only [Real.norm_eq_abs] using hi.norm))
  have hZ : 0 ≤ ∫ z, Z z ∂μ := integral_nonneg (fun z => by dsimp [Z]; positivity)
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := ε / ((∫ z, Z z ∂μ) + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hδε : δ * (∫ z, Z z ∂μ) ≤ ε := by
    dsimp [δ]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by linarith : 0 < (∫ z, Z z ∂μ) + 1)).mpr
    nlinarith
  obtain ⟨t, ht, hnet⟩ := exists_finite_affine_net hm hb hδ
  have : Nonempty t := ht.to_subtype
  let mf : t → ℝ := fun i => m i
  let af : t → Fin (n + 1) → ℝ := fun i => a i
  let bf : t → Fin (n + 1) → ℝ := fun i => b i
  have hfinite := gaussian_finiteMax_comparison mf af bf
    (fun i j => horth i j) (fun i j => hinc i j)
  calc
    _ ≤ ∫ z, finiteMax (affineProcess mf bf z) + δ * Z z ∂μ := by
      apply integral_mono (integrable_supProcess hm hb)
        ((integrable_finiteMax_affine mf bf).add (hZI.const_mul δ))
      intro z
      apply supProcess_le hm hb
      intro j
      obtain ⟨i, hi, hmj, hbj⟩ := hnet j
      have hd := (le_abs_self _).trans (affineProcess_difference_abs_le m b hmj hbj z)
      have hmax := le_finiteMax (affineProcess mf bf z) (⟨i, hi⟩ : t)
      change affineProcess m b z i ≤ _ at hmax
      change affineProcess m b z j ≤ finiteMax (affineProcess mf bf z) + δ * (1 + ∑ k, |z k|)
      linarith
    _ = (∫ z, finiteMax (affineProcess mf bf z) ∂μ) + δ * ∫ z, Z z ∂μ := by
      rw [integral_add (integrable_finiteMax_affine mf bf) (hZI.const_mul δ), integral_const_mul]
    _ ≤ (∫ z, finiteMax (affineProcess mf af z) ∂μ) + ε := add_le_add hfinite hδε
    _ ≤ (∫ z, supProcess m a z ∂μ) + ε := by
      refine add_le_add ?_ le_rfl
      apply integral_mono (integrable_finiteMax_affine mf af) (integrable_supProcess hm ha)
      intro z
      apply finiteMax_le
      intro i
      exact affine_le_supProcess hm ha z i

end CompactIndex
end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
