import Mathlib
import OAI.Probability.SKGap.Matrix.MatrixEntryCLM
import OAI.Probability.SKGap.Gaussian.GaussianProductIntegral
import OAI.Probability.SKGap.Matrix.OpNormDiagonal
import OAI.Probability.SKGap.Gaussian.GaussianSign

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma operator_le_frobenius (M : Matrix ι ι ℝ) : opNorm M ≤ ‖M‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have hh := Matrix.frobenius_norm_mul M (Matrix.replicateCol Unit (fun i => x i))
  rw [← Matrix.replicateCol_mulVec,Matrix.frobenius_norm_replicateCol,
    Matrix.frobenius_norm_replicateCol] at hh
  exact hh

def matrixBilinear (M : Matrix ι ι ℝ) (u v : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, ∑ k, u i*M i k*v k

lemma matrixBilinear_inner (M : Matrix ι ι ℝ) (u v : EuclideanSpace ℝ ι) :
    matrixBilinear M u v = inner ℝ u (M.toEuclideanLin.toContinuousLinearMap v) := by
  change (∑ i, ∑ k, u i*M i k*v k) = ∑ i, (∑ k, M i k*v k)*u i
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma matrixBilinear_abs_le (M : Matrix ι ι ℝ) (u v : EuclideanSpace ℝ ι) :
    |matrixBilinear M u v| ≤ opNorm M*‖u‖*‖v‖ := by
  rw [matrixBilinear_inner]
  calc
    _ ≤ ‖u‖*‖M.toEuclideanLin.toContinuousLinearMap v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖u‖*(opNorm M*‖v‖) := mul_le_mul_of_nonneg_left
      (M.toEuclideanLin.toContinuousLinearMap.le_opNorm v) (norm_nonneg _)
    _ = _ := by ring

lemma matrixBilinear_frobenius (M : Matrix ι ι ℝ) (u v : EuclideanSpace ℝ ι) :
    |matrixBilinear M u v| ≤ ‖M‖*‖u‖*‖v‖ :=
  (matrixBilinear_abs_le M u v).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (operator_le_frobenius M) (norm_nonneg _)) (norm_nonneg _))

omit [DecidableEq ι] in
lemma matrixBilinear_sub (M N : Matrix ι ι ℝ) (u v : EuclideanSpace ℝ ι) :
    matrixBilinear (M-N) u v = matrixBilinear M u v-matrixBilinear N u v := by
  simp only [matrixBilinear,Matrix.sub_apply,mul_sub,sub_mul,Finset.sum_sub_distrib]

omit [DecidableEq ι] in
lemma matrixBilinear_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : Ω → Matrix ι ι ℝ) (hF : ∀ i k, Integrable (fun x => F x i k) μ)
    (u v : EuclideanSpace ℝ ι) :
    (∫ x, matrixBilinear (F x) u v ∂μ) =
      matrixBilinear (fun i k => ∫ x, F x i k ∂μ) u v := by
  unfold matrixBilinear
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun k _ => ((hF i k).const_mul (u i)).mul_const (v k)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun k _ => ((hF i k).const_mul (u i)).mul_const (v k))]
  simp only [integral_mul_const,integral_const_mul]

lemma matrixBilinear_diagonal_error {e : ι → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (he : ∀ i, |e i| ≤ ε) (u v : EuclideanSpace ℝ ι) :
    |matrixBilinear (diagonal e) u v| ≤ ε*‖u‖*‖v‖ :=
  (matrixBilinear_abs_le _ _ _).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (opNorm_diagonal_le hε he) (norm_nonneg _)) (norm_nonneg _))

lemma goe_bilinear_lipschitz (r : ℝ) (F : Matrix ι ι ℝ → Matrix ι ι ℝ)
    {L : ℝ} (hL : 0 ≤ L) (hF : ∀ M N, ‖F M-F N‖ ≤ L*‖M-N‖)
    (u v : EuclideanSpace ℝ ι) :
    LipschitzWith ⟨L*‖u‖*‖v‖*sqrt (2*r),by positivity⟩
      (fun g : EuclideanSpace ℝ (MatrixCoordinates ι) => matrixBilinear (F (goeMatrix r g)) u v) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm,Real.norm_eq_abs]
  rw [← matrixBilinear_sub]
  calc
    _ ≤ ‖F (goeMatrix r x)-F (goeMatrix r y)‖*‖u‖*‖v‖ := matrixBilinear_frobenius _ _ _
    _ ≤ (L*‖goeMatrix r x-goeMatrix r y‖)*‖u‖*‖v‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hF _ _) (norm_nonneg _)) (norm_nonneg _)
    _ ≤ (L*(sqrt (2*r)*‖x-y‖))*‖u‖*‖v‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ hL
      exact (goeMatrix_L2_lipschitz r).norm_sub_le x y
    _ = _ := by change _ = (L*‖u‖*‖v‖*sqrt (2*r))*‖x-y‖; ring

end SKGap

namespace SKGap
open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal
lemma gaussianProduct_tail_lipschitz {κ : Type*} [Fintype κ]
    {f : (κ → ℝ) → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L (fun x : EuclideanSpace ℝ κ => f x.ofLp))
    (hL : 0 < L) {u : ℝ} (hu : 0 ≤ u) :
    (Measure.pi (fun _ : κ => gaussianReal 0 1)).real
      {x | u ≤ |f x - ∫ y, f y ∂Measure.pi (fun _ : κ => gaussianReal 0 1)|} ≤
      2*exp (-2*u^2/(π^2*(L:ℝ)^2)) := by
  let e : (κ → ℝ) ≃ᵐ EuclideanSpace ℝ κ := MeasurableEquiv.toLp 2 _
  have hp : MeasurePreserving e (Measure.pi (fun _ : κ => gaussianReal 0 1))
      (stdGaussian (EuclideanSpace ℝ κ)) := ⟨e.measurable,map_pi_eq_stdGaussian⟩
  have hi := hp.integral_comp' (fun x : EuclideanSpace ℝ κ => f x.ofLp)
  change (∫ x, f x ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) = _ at hi
  have h := stdGaussian_tail_lipschitz hf hL hu
  rw [← hi] at h
  have hs : MeasurableSet {x : EuclideanSpace ℝ κ |
      u ≤ |f x.ofLp-∫ y, f y ∂Measure.pi (fun _ : κ => gaussianReal 0 1)|} :=
    measurableSet_le measurable_const ((hf.continuous.measurable.sub_const _).abs)
  have he := congrArg ENNReal.toReal (hp.measure_preimage hs.nullMeasurableSet)
  change (Measure.pi (fun _ : κ => gaussianReal 0 1)).real
      {x | u ≤ |f x-∫ y, f y ∂Measure.pi (fun _ : κ => gaussianReal 0 1)|} = _ at he
  rw [he]
  exact h
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma goe_entries_integrable (r : ℝ) (F : Matrix ι ι ℝ → Matrix ι ι ℝ)
    {L : ℝ} (hL : 0 ≤ L) (hF : ∀ M N, ‖F M-F N‖ ≤ L*‖M-N‖) (i k : ι) :
    Integrable (fun g => F (goeMatrix r g) i k)
      (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)) := by
  have hf : LipschitzWith ⟨L,hL⟩ F := by
    apply LipschitzWith.of_dist_le_mul
    intro M N
    change ‖F M-F N‖ ≤ L*‖M-N‖
    exact hF M N
  exact gaussianProduct_integrable_lipschitz ((matrixEntry_lipschitz i k).comp
    (hf.comp (goeMatrix_L2_lipschitz r)))

lemma goe_bilinear_bias (r : ℝ) (F : Matrix ι ι ℝ → Matrix ι ι ℝ)
    (hF : ∀ (s : ι → ℝ), (∀ i, s i^2=1) → ∀ M,
      F (signConjugate s M)=signConjugate s (F M))
    (hI : ∀ i k, Integrable (fun g => F (goeMatrix r g) i k)
      (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)))
    (d : ι → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hd : ∀ i, |(∫ g, F (goeMatrix r g) i i
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))-d i| ≤ ε)
    (u v : EuclideanSpace ℝ ι) :
    |(∫ g, matrixBilinear (F (goeMatrix r g)) u v
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))-
      matrixBilinear (diagonal d) u v| ≤ ε*‖u‖*‖v‖ := by
  let e : ι → ℝ := fun i => ∫ g, F (goeMatrix r g) i i
    ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
  have he : (fun i k => ∫ g, F (goeMatrix r g) i k
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)) = diagonal e := by
    ext i k
    by_cases hik : i=k
    · subst k; simp only [diagonal_apply_eq]; rfl
    · rw [diagonal_apply_ne _ hik]
      exact goe_equivariant_offdiag r F hF i k hik
  rw [matrixBilinear_integral _ _ hI,he,← matrixBilinear_sub,diagonal_sub]
  exact matrixBilinear_diagonal_error hε hd u v

lemma gaussianProduct_tail_from_bias {κ : Type*} [Fintype κ]
    {f : (κ → ℝ) → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L (fun x : EuclideanSpace ℝ κ => f x.ofLp))
    (hL : 0 < L) {a b t : ℝ} (hb : |(∫ x, f x
      ∂Measure.pi (fun _ : κ => gaussianReal 0 1))-a| ≤ b) (ht : 0 ≤ t) :
    (Measure.pi (fun _ : κ => gaussianReal 0 1)).real {x | b+t ≤ |f x-a|} ≤
      2*exp (-2*t^2/(π^2*(L:ℝ)^2)) := by
  let μ := Measure.pi (fun _ : κ => gaussianReal 0 1)
  apply (measureReal_mono (show {x | b+t ≤ |f x-a|} ⊆
      {x | t ≤ |f x-∫ y, f y ∂μ|} from ?_)).trans (gaussianProduct_tail_lipschitz hf hL ht)
  intro x hx
  have hh : |f x-a| ≤ |f x-∫ y, f y ∂μ|+|(∫ y, f y ∂μ)-a| := abs_sub_le _ _ _
  change b+t ≤ |f x-a| at hx
  change t ≤ |f x-∫ y, f y ∂μ|
  linarith

lemma goe_bilinear_uniform_lipschitz (r : ℝ) (F : Matrix ι ι ℝ → Matrix ι ι ℝ)
    {L U : ℝ} (hL : 0 ≤ L) (hU : 0 ≤ U) (hF : ∀ M N, ‖F M-F N‖ ≤ L*‖M-N‖)
    (u v : EuclideanSpace ℝ ι) (hu : ‖u‖ ≤ U) (hv : ‖v‖ ≤ U) :
    LipschitzWith ⟨(L+1)*(U+1)^2*sqrt (2*r),by positivity⟩
      (fun g : EuclideanSpace ℝ (MatrixCoordinates ι) => matrixBilinear (F (goeMatrix r g)) u v) := by
  apply (goe_bilinear_lipschitz r F hL hF u v).weaken
  change L*‖u‖*‖v‖*sqrt (2*r) ≤ (L+1)*(U+1)^2*sqrt (2*r)
  apply mul_le_mul_of_nonneg_right _ (sqrt_nonneg _)
  calc
    _ ≤ (L+1)*(U+1)*(U+1) := by gcongr <;> linarith
    _ = _ := by ring

lemma goe_bilinear_concentration {j L U ε t : ℝ} (hj : 0 < j) (hL : 0 ≤ L)
    (hU : 0 ≤ U) (hε : 0 ≤ ε) (ht : 0 ≤ t) [Nonempty ι]
    (F : Matrix ι ι ℝ → Matrix ι ι ℝ)
    (hF : ∀ (s : ι → ℝ), (∀ i, s i^2=1) → ∀ M,
      F (signConjugate s M)=signConjugate s (F M))
    (hLip : ∀ M N, ‖F M-F N‖ ≤ L*‖M-N‖)
    (d : ι → ℝ)
    (hd : ∀ i, |(∫ g, F (goeMatrix (j/(Fintype.card ι:ℝ)) g) i i
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))-d i| ≤ ε)
    (u v : EuclideanSpace ℝ ι) (hu : ‖u‖ ≤ U) (hv : ‖v‖ ≤ U) :
    (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
      {g | ε*U^2+t ≤ |matrixBilinear (F (goeMatrix (j/(Fintype.card ι:ℝ)) g)-diagonal d) u v|} ≤
      2*exp (-(Fintype.card ι:ℝ)*t^2/(π^2*((L+1)*(U+1)^2)^2*j)) := by
  let n : ℝ := Fintype.card ι
  let r := j/n
  let C := (L+1)*(U+1)^2
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hr : 0 < r := div_pos hj hn
  have hC : 0 < C := by dsimp [C]; positivity
  have hCF : LipschitzWith ⟨C*sqrt (2*r),by positivity⟩
      (fun g : EuclideanSpace ℝ (MatrixCoordinates ι) => matrixBilinear (F (goeMatrix r g)) u v) :=
    goe_bilinear_uniform_lipschitz r F hL hU hLip u v hu hv
  have hmean := goe_bilinear_bias r F hF (goe_entries_integrable r F hL hLip) d hε hd u v
  have hmean' : |(∫ g, matrixBilinear (F (goeMatrix r g)) u v
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))-
      matrixBilinear (diagonal d) u v| ≤ ε*U^2 := hmean.trans (by nlinarith [mul_le_mul hu hv (norm_nonneg _) hU])
  have hpos : (0:ℝ≥0) < ⟨C*sqrt (2*r),by positivity⟩ := by
    change (0:ℝ) < C*sqrt (2*r)
    positivity
  have hp := gaussianProduct_tail_from_bias hCF hpos hmean' ht
  simp only [matrixBilinear_sub]
  apply hp.trans_eq
  congr 2
  change -2*t^2/(π^2*(C*sqrt (2*r))^2) = -n*t^2/(π^2*C^2*j)
  rw [mul_pow,sq_sqrt (by positivity : 0 ≤ 2*r)]
  dsimp only [r]
  field_simp
end SKGap
end
end

end OAI
