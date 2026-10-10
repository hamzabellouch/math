import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TailJets

namespace OAI

noncomputable section
namespace VelocityDetection.TailSpace.Jets
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators

def averageL {n a : ℕ} {k : Coord n → ℝ} (hk : Integrable k) (s : ℝ) :
    compatibleJets n a →L[ℝ] compatibleJets n a :=
  LinearMap.mkContinuous
    { toFun := average k s
      map_add' := by
        intro J K
        simp only [average, show ∀ Y, translate (s • Y) (J + K) =
          translate (s • Y) J + translate (s • Y) K from fun Y => (translateLI (s • Y)).map_add J K,
          smul_add]
        exact integral_add (integrable_average hk s J) (integrable_average hk s K)
      map_smul' := by
        intro c J
        simp only [average, show ∀ Y, translate (s • Y) (c • J) =
          c • translate (s • Y) J from fun Y => (translateLI (s • Y)).map_smul c J,
          smul_comm (k _) c]
        exact integral_smul c _ }
    (∫ Y, ‖k Y‖) (norm_average_le hk s)

@[simp] theorem averageL_apply {n a : ℕ} {k : Coord n → ℝ} (hk : Integrable k)
    (s : ℝ) (J : compatibleJets n a) : averageL hk s J = average k s J := rfl

def convolve {n a : ℕ} {k : Coord n → ℝ} (hk : Integrable k) :
    compatibleJets n a →L[ℝ] compatibleJets n a := averageL hk (-1)

theorem value_convolve {n a : ℕ} {k : Coord n → ℝ} (hk : Integrable k)
    (J : compatibleJets n a) (X : Coord n) :
    value (convolve hk J) X = ∫ Y, k Y * value J (X - Y) := by
  simpa [convolve, neg_one_smul, sub_eq_add_neg] using value_average hk (-1) J X

theorem norm_convolve_le {n a : ℕ} {k : Coord n → ℝ} (hk : Integrable k)
    (J : compatibleJets n a) : ‖convolve hk J‖ ≤ (∫ Y, ‖k Y‖) * ‖J‖ :=
  norm_average_le hk (-1) J

theorem continuous_average {n a : ℕ} {k : Coord n → ℝ} (hk : Integrable k)
    (J : compatibleJets n a) : Continuous (fun s : ℝ => average k s J) := by
  apply continuous_of_dominated (bound := fun Y => ‖k Y‖ * ‖J‖)
  · intro s
    exact (integrable_average hk s J).aestronglyMeasurable
  · intro s
    filter_upwards [] with Y
    simp only [norm_smul, norm_translate, le_refl]
  · exact hk.norm.mul_const ‖J‖
  · filter_upwards [] with Y
    have hs : Continuous (fun s : ℝ => s • Y) := continuous_id.smul continuous_const
    have ht : Continuous (fun s : ℝ => translate (s • Y) J) :=
      (continuous_translate J).comp hs
    exact ht.const_smul (k Y)

@[simp] theorem average_zero_scale {n a : ℕ} (k : Coord n → ℝ)
    (J : compatibleJets n a) : average k 0 J = (∫ Y, k Y) • J := by
  simp only [average, zero_smul, translate_zero, integral_smul_const]

theorem average_tendsto_identity {n a : ℕ} {k : Coord n → ℝ} (hk : Integrable k)
    (hm : ∫ Y, k Y = 1) (J : compatibleJets n a) :
    Tendsto (fun s : ℝ => average k s J) (𝓝 0) (𝓝 J) := by
  have hh := (continuous_average hk J).tendsto 0
  simpa only [average_zero_scale, hm, one_smul] using hh

theorem norm_average_le_of_probability_kernel {n a : ℕ} {k : Coord n → ℝ}
    (hk : Integrable k) (hn : ∀ Y, 0 ≤ k Y) (hm : ∫ Y, k Y = 1)
    (s : ℝ) (J : compatibleJets n a) : ‖average k s J‖ ≤ ‖J‖ := by
  have he : (∫ Y, ‖k Y‖) = 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg (hn _)] using hm
  simpa only [he, one_mul] using norm_average_le hk s J

end VelocityDetection.TailSpace.Jets
end

end OAI
