import OAI.Geometry.NodalSets.Waves.AffineGaussianSmallBall
import OAI.Geometry.NodalSets.Waves.GaussianFactorBound

namespace OAI

namespace Yau.Probability
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal
noncomputable section
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma euclidean_ofLp_norm_le (v : E) : ‖WithLp.ofLp v‖ ≤ ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
  intro i
  exact PiLp.norm_apply_le v i

lemma euclidean_toLp_norm_le (v : ι → ℝ) :
    ‖WithLp.toLp 2 v‖ ≤ ((Fintype.card ι : ℝ)+1)*‖v‖ := by
  have hs : ‖WithLp.toLp 2 v‖^2 ≤ (Fintype.card ι : ℝ)*‖v‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      ∑ i, (v i)^2 ≤ ∑ _ : ι, ‖v‖^2 := by
        apply Finset.sum_le_sum
        intro i _
        have h := norm_le_pi_norm v i
        rw [Real.norm_eq_abs] at h
        nlinarith [sq_abs (v i),abs_nonneg (v i),norm_nonneg v]
      _ = _ := by simp
  have hc : (0:ℝ) ≤ Fintype.card ι := by positivity
  have hn := norm_nonneg (WithLp.toLp 2 v)
  apply (sq_le_sq₀ hn (by positivity)).mp
  nlinarith [sq_nonneg ((Fintype.card ι : ℝ)*‖v‖),
    mul_nonneg hc (sq_nonneg ‖v‖)]

lemma euclidean_affine_small_ball (L : E ≃L[ℝ] E) (mean : E)
    (radius B : ℝ) (hr : 0 ≤ radius) (hB : 0 ≤ B)
    (hL : ‖L.symm.toContinuousLinearMap‖ ≤ B) :
    ((stdGaussian E).map (fun z ↦ mean+L z)) {y | ‖y‖ ≤ radius} ≤
      ENNReal.ofReal ((2*(B*((Fintype.card ι : ℝ)+1)*radius)/
        Real.sqrt (2*Real.pi))^(Fintype.card ι)) := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)
  let K : (ι → ℝ) ≃L[ℝ] (ι → ℝ) := e.symm.trans (L.trans e)
  have hK : ‖K.symm.toContinuousLinearMap‖ ≤ B*((Fintype.card ι : ℝ)+1) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    change ‖e (L.symm (e.symm v))‖ ≤ _
    calc
      _ ≤ ‖L.symm (e.symm v)‖ := euclidean_ofLp_norm_le _
      _ ≤ ‖L.symm.toContinuousLinearMap‖*‖e.symm v‖ := L.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ B*(((Fintype.card ι : ℝ)+1)*‖v‖) :=
        mul_le_mul hL (euclidean_toLp_norm_le v) (norm_nonneg _) hB
      _ = _ := by ring
  have hb := affine_gaussian_small_ball K (e mean) radius
    (B*((Fintype.card ι : ℝ)+1)) hr (by positivity) hK
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_apply (by fun_prop) (isClosed_le continuous_norm continuous_const).measurableSet]
  rw [Measure.map_apply (by fun_prop) (isClosed_le continuous_norm continuous_const).measurableSet] at hb
  apply le_trans (measure_mono ?_) hb
  intro v hv
  change ‖e mean+K v‖ ≤ radius
  have he : e mean+K v = e (mean+L (WithLp.toLp 2 v)) := by
    simp [K,e,map_add]
  rw [he]
  exact (euclidean_ofLp_norm_le _).trans hv

variable [DecidableEq ι]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

lemma gaussian_map_small_ball (T : F →L[ℝ] E) (mean : E)
    (a radius : ℝ) (ha : 0 < a) (hr : 0 ≤ radius)
    (h : ∀ v : E, a*‖v‖^2 ≤ ‖T.adjoint v‖^2) :
    ((stdGaussian F).map (fun z ↦ mean+T z)) {y | ‖y‖ ≤ radius} ≤
      ENNReal.ofReal ((2*((Real.sqrt a)⁻¹*((Fintype.card ι : ℝ)+1)*radius)/
        Real.sqrt (2*Real.pi))^(Fintype.card ι)) := by
  obtain ⟨L,hLaw,hL⟩ := exists_gaussian_factor_equiv T a ha h
  have he : (stdGaussian F).map (fun z ↦ mean+T z) =
      (stdGaussian E).map (fun z ↦ mean+L z) := by
    rw [show (fun z ↦ mean+T z) = (fun z ↦ mean+z) ∘ T from rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), hLaw,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [he]
  exact euclidean_affine_small_ball L mean radius (Real.sqrt a)⁻¹ hr (by positivity) hL

end
end Yau.Probability

end OAI
