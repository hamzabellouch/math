import OAI.Probability.InvariantIsing.Fields.FieldGaussianIntegrability
import OAI.Probability.InvariantIsing.Fields.FieldTiltDerivative

namespace OAI

/-! Differentiating the actual scalar Gaussian noise amplitude. Linear
growth supplies the local exponential envelope. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

def fieldGaussianAmplitude (ζ : ℝ) (F : ℝ → ℝ) (z r : ℝ) : ℝ :=
  if ζ = 0 then ∫ u, F (z + r * u) ∂gaussianReal 0 1
  else logMean ζ (gaussianReal 0 1) (fun u => F (z + r * u))

lemma fieldGaussianAmplitude_eq_operator (ζ : ℝ) (F : ℝ → ℝ) (z : ℝ)
    {r : ℝ} (hr : 0 ≤ r) :
    fieldGaussianAmplitude ζ F z r = gaussianOperator ζ (r ^ 2) F z := by
  simp only [fieldGaussianAmplitude, gaussianOperator, Real.sqrt_sq hr]
  split_ifs
  · rfl
  · unfold logMean
    ring

private lemma amplitude_abs_bound (r s : ℝ) (hs : s ∈ Ioo (r - 1) (r + 1)) :
    |s| ≤ |r| + 1 := by
  have hsr : |s - r| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
  calc
    |s| = |s - r + r| := by congr 1; ring
    _ ≤ |s - r| + |r| := abs_add_le _ _
    _ ≤ _ := by linarith

lemma hasDerivAt_fieldGaussianAmplitude (ζ z r : ℝ) {F D : ℝ → ℝ}
    (hF : Measurable F) (hFg : HasLinearGrowth F) (hD : Measurable D)
    {K : ℝ} (hK : 0 ≤ K) (hDb : ∀ u, |D u| ≤ K)
    (hd : ∀ u, HasDerivAt F (D u) u) :
    HasDerivAt (fieldGaussianAmplitude ζ F z)
      (∫ u, D (z + r * u) * u
        ∂(gaussianReal 0 1).tilted (fun u => ζ * F (z + r * u))) r := by
  have hFm (s : ℝ) : Measurable (fun u => F (z + s * u)) :=
    hF.comp (measurable_const.add (measurable_id.const_mul s))
  have hDm (s : ℝ) : Measurable (fun u => D (z + s * u) * u) :=
    (hD.comp (measurable_const.add (measurable_id.const_mul s))).mul measurable_id
  have hd' (s u : ℝ) : HasDerivAt (fun q => F (z + q * u)) (D (z + s * u) * u) s := by
    have ha : HasDerivAt (fun q => z + q * u) u s := by
      convert ((hasDerivAt_id s).mul_const u).const_add z using 1 <;>
        first | rfl | simp only [one_mul]
    exact (hd (z + s * u)).comp s ha
  by_cases hζ : ζ = 0
  · subst ζ
    have hi := field_gaussian_linear_integrable 1 0 (hFm r)
      ((hFg.add_left z).scale_argument r)
    have hdom : Integrable (fun u : ℝ => K * |u|) (gaussianReal 0 1) :=
      (((memLp_id_gaussianReal 1).integrable le_rfl).abs).const_mul K
    obtain ⟨_, hI⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Ioo_mem_nhds (by linarith : r - 1 < r) (by linarith : r < r + 1))
      (Eventually.of_forall fun s => (hFm s).aestronglyMeasurable) hi
      (hDm r).aestronglyMeasurable
      (ae_of_all _ fun u s _ => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hDb _) (abs_nonneg u))
      hdom (ae_of_all _ fun u s _ => hd' s u)
    have he : fieldGaussianAmplitude 0 F z =
        fun s => ∫ u, F (z + s * u) ∂gaussianReal 0 1 := by
      funext s
      simp only [fieldGaussianAmplitude, ite_true]
    rw [he]
    simpa only [zero_mul, tilted_const] using hI
  · obtain ⟨C, L, hC, hL, hFb⟩ := hFg
    let A := Real.exp (|ζ| * (C + L * |z|)) * (|ζ| * K)
    let B := |ζ| * L * (|r| + 1)
    have henv : Integrable (fun u : ℝ => A * Real.exp ((B + 1) * ‖u‖)) (gaussianReal 0 1) :=
      ((gaussianReal_exponentialNormMoments 0 1) (B + 1)).const_mul A
    have hFbound (s u : ℝ) (hs : s ∈ Ioo (r - 1) (r + 1)) :
        |F (z + s * u)| ≤ C + L * (|z| + (|r| + 1) * |u|) := by
      have hu : ‖z + s * u‖ ≤ |z| + (|r| + 1) * |u| := by
        rw [Real.norm_eq_abs]
        exact (abs_add_le _ _).trans (by
          rw [abs_mul]
          exact add_le_add_right (mul_le_mul_of_nonneg_right (amplitude_abs_bound r s hs) (abs_nonneg u)) _)
      exact (hFb _).trans (add_le_add_right (mul_le_mul_of_nonneg_left hu hL) C)
    have hbound : ∀ᵐ u ∂gaussianReal 0 1, ∀ s ∈ Ioo (r - 1) (r + 1),
        ‖Real.exp (ζ * F (z + s * u)) * (ζ * (D (z + s * u) * u))‖ ≤
          A * Real.exp ((B + 1) * ‖u‖) := by
      apply ae_of_all
      intro u s hs
      have hexp : ζ * F (z + s * u) ≤ |ζ| * (C + L * (|z| + (|r| + 1) * |u|)) :=
        (le_abs_self _).trans (by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hFbound s u hs) (abs_nonneg ζ))
      have hu : |u| ≤ Real.exp |u| := by linarith [Real.add_one_le_exp |u|]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul, abs_mul]
      calc
        _ ≤ Real.exp (|ζ| * (C + L * (|z| + (|r| + 1) * |u|))) *
            (|ζ| * (K * Real.exp |u|)) :=
          mul_le_mul (Real.exp_le_exp.mpr hexp)
            (mul_le_mul_of_nonneg_left (mul_le_mul (hDb _) hu (abs_nonneg u) hK) (abs_nonneg ζ))
            (mul_nonneg (abs_nonneg ζ) (mul_nonneg (abs_nonneg _) (abs_nonneg _))) (Real.exp_pos _).le
        _ = A * Real.exp ((B + 1) * ‖u‖) := by
          dsimp only [A, B]
          rw [Real.norm_eq_abs,
            show |ζ| * (C + L * (|z| + (|r| + 1) * |u|)) =
              |ζ| * (C + L * |z|) + (|ζ| * L * (|r| + 1)) * |u| by ring,
            Real.exp_add,
            show (|ζ| * L * (|r| + 1) + 1) * |u| =
              (|ζ| * L * (|r| + 1)) * |u| + |u| by ring,
            Real.exp_add]
          ring
    have hi := integrable_exp_of_linearGrowth (gaussianReal 0 1)
      (gaussianReal_exponentialNormMoments 0 1) (hFm r)
      ((show HasLinearGrowth F from ⟨C, L, hC, hL, hFb⟩).add_left z |>.scale_argument r) ζ
    have h := hasDerivAt_logMean_of_integrable_envelope (gaussianReal 0 1)
      (fun s u => F (z + s * u)) (fun s u => D (z + s * u) * u) hFm hζ
      (Ioo_mem_nhds (by linarith : r - 1 < r) (by linarith : r < r + 1))
      (hDm r) hi (fun s _ u => hd' s u) _ henv hbound
    have he : fieldGaussianAmplitude ζ F z =
        fun s => logMean ζ (gaussianReal 0 1) (fun u => F (z + s * u)) := by
      funext s
      simp only [fieldGaussianAmplitude, hζ, ite_false]
    rw [he]
    exact h

end InvariantIsing

end

end OAI
