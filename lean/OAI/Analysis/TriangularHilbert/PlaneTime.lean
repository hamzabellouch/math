import OAI.Analysis.TriangularHilbert.PlaneIntegral

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma planeEnergy_hasDerivAt_time (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) (α : Three → ℝ) (hα : ∀ w, 0 < α w)
    {s : ℝ} (hs : 0 < s) (v : Three) :
    HasDerivAt (fun t => planeIntegral (fun p => heatEnergy A h u p (fun w => α w*t) v) d)
      (∑ w, α w * planeIntegral (fun p => heatVariance A h u p (fun a => α a*s) v w) d) s := by
  obtain ⟨a,b,ha,hab,hla,hlb⟩ := finite_variance_bounds α hα
  have hb : 0 < b := ha.trans_le hab
  have has : 0 < a*(s/2) := mul_pos ha (by linarith)
  have habs : a*(s/2) ≤ b*(2*s) := by gcongr; linarith
  obtain ⟨B,hB,hBn,hbound⟩ := exists_heat_uniform_majorant A hh has habs (abs_nonneg d) u
  let C := ∑ w, α w
  have hC : 0 ≤ C := Finset.sum_nonneg (fun w _ => (hα w).le)
  have hσ : ∀ w, 0 < α w*s := fun w => mul_pos (hα w) hs
  have hint := (heatPlane_integrable A hh u d hσ).energy 2 v
  have hvar := (heatPlane_integrable A hh u d hσ).variance 2 v
  have hmeas : AEStronglyMeasurable (fun z : ℝ × ℝ => ∑ w, α w * heatVariance A h u (chart 2 d z) (fun a => α a*s) v w) := by
    exact (Finset.aestronglyMeasurable_fun_sum Finset.univ (fun w _ =>
        (hvar w).aestronglyMeasurable.const_mul (α w)))
  have hboundσ (t : ℝ) (ht : t ∈ Set.Ioo (s/2) (2*s)) :
      (∀ w, a*(s/2) ≤ α w*t) ∧ (∀ w, α w*t ≤ b*(2*s)) := by
    have ht0 : 0 < t := (by linarith : 0 < s/2).trans ht.1
    constructor
    · intro w; exact mul_le_mul (hla w) ht.1.le (by linarith) (hα w).le
    · intro w; exact mul_le_mul (hlb w) ht.2.le ht0.le hb.le
  have hn : Set.Ioo (s/2) (2*s) ∈ 𝓝 s := Ioo_mem_nhds (by linarith) (by linarith)
  have hfmeas : ∀ᶠ t in 𝓝 s, AEStronglyMeasurable (fun z : ℝ × ℝ => heatEnergy A h u (chart 2 d z) (fun w => α w*t) v) := by
    filter_upwards [hn] with t ht
    have ht0 : 0 < t := (by linarith : 0 < s/2).trans ht.1
    exact ((continuous_heatEnergy A hh u (fun w => mul_pos (hα w) ht0) v).measurable.comp
      (measurable_chart 2 d)).aestronglyMeasurable
  have hder := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t z => heatEnergy A h u (chart 2 d z) (fun w => α w*t) v)
    (F' := fun t z => ∑ w, α w * heatVariance A h u (chart 2 d z) (fun a => α a*t) v w)
    (bound := fun z => C*B z) hn hfmeas hint hmeas
    (Eventually.of_forall (fun z t ht => by
      calc
        _ ≤ ∑ w, ‖α w * heatVariance A h u (chart 2 d z) (fun a => α a*t) v w‖ := norm_sum_le _ _
        _ ≤ ∑ w, α w * B z := by
          apply Finset.sum_le_sum
          intro w _
          rw [norm_mul, Real.norm_eq_abs, abs_of_pos (hα w)]
          exact mul_le_mul_of_nonneg_left
            ((hbound 2 d z (le_refl _) _ (hboundσ t ht).1 (hboundσ t ht).2).variance v w) (hα w).le
        _ = C*B z := (Finset.sum_mul _ _ _).symm))
    (hB.const_mul C)
    (Eventually.of_forall (fun z t ht => heatEnergy_hasDerivAt_time A hh u (chart 2 d z) α hα
      ((by linarith : 0 < s/2).trans ht.1) v))).2
  have he : (∫ z : ℝ × ℝ, ∑ w, α w * heatVariance A h u (chart 2 d z) (fun a => α a*s) v w) =
      ∑ w, α w * planeIntegral (fun p => heatVariance A h u p (fun a => α a*s) v w) d := by
    rw [integral_finsetSum _ (fun w _ => (hvar w).const_mul (α w))]
    simp only [integral_const_mul, planeIntegral]
  rw [he] at hder
  exact hder

lemma two_planeVariance (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    2 * planeIntegral (fun p => heatVariance A h u p σ v w) d =
      planeIntegral (fun p => heatPure A h u p σ v w) d -
      planeIntegral (fun p => heatCost A h u p σ v w) d := by
  rw [planeIntegral, ← integral_const_mul]
  have he : (fun z : ℝ × ℝ => 2 * heatVariance A h u (chart 2 d z) σ v w) =
      (fun z => heatPure A h u (chart 2 d z) σ v w - heatCost A h u (chart 2 d z) σ v w) := by
    funext z
    simp only [heatVariance,heatPure,heatCost]
    ring
  rw [he, integral_sub ((heatPlane_integrable A hh u d hσ).pure 2 v w)
    ((heatPlane_integrable A hh u d hσ).cost 2 v w)]
  rfl

lemma planeCost_nonneg (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (d : ℝ) (σ : Three → ℝ) (v w : Three) :
    0 ≤ planeIntegral (fun p => heatCost A h u p σ v w) d :=
  integral_nonneg (fun z => heatCost_nonneg A h u (chart 2 d z) σ v w)

lemma two_planeMixed_le (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) {σ : Three → ℝ} (hσ : ∀ a, 0 < σ a)
    {v w z : Three} (hw : w ≠ v) (hz : z ≠ v) (hwz : w ≠ z) :
    2 * planeIntegral (fun p => heatMixed A h u p σ v w z) d ≤
      planeIntegral (fun p => heatCost A h u p σ v w) d +
      planeIntegral (fun p => heatCost A h u p σ v z) d := by
  have hi := heatPlane_integrable A hh u d hσ
  simp only [planeIntegral]
  rw [← integral_const_mul, ← integral_add (hi.cost 2 v w) (hi.cost 2 v z)]
  exact integral_mono ((hi.mixed 2 v w z hw hz hwz).const_mul 2)
    ((hi.cost 2 v w).add (hi.cost 2 v z)) (fun p => two_heatMixed_le A hh u (chart 2 d p) hσ hw hz)

lemma planeCost_neighbors (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) {σ : Three → ℝ} (hσ : ∀ a, 0 < σ a) (w : Three) :
    (∑ v, if v = w then 0 else planeIntegral (fun p => heatCost A h u p σ v w) d) ≤
      Real.sqrt 2 * planeIntegral (fun p => heatCost A h u p σ w w) d := by
  have hi := heatPlane_integrable A hh u d hσ
  have hv v : Integrable (fun z : ℝ × ℝ => if v = w then (0:ℝ) else heatCost A h u (chart 2 d z) σ v w) := by
    split_ifs
    · exact integrable_zero _ _ _
    · exact hi.cost 2 v w
  have he : (∑ v, if v = w then 0 else planeIntegral (fun p => heatCost A h u p σ v w) d) =
      ∫ z : ℝ × ℝ, ∑ v, if v = w then 0 else heatCost A h u (chart 2 d z) σ v w := by
    rw [integral_finsetSum _ (fun v _ => hv v)]
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> simp [planeIntegral]
  rw [he, planeIntegral, ← integral_const_mul]
  exact integral_mono (integrable_finsetSum _ (fun v _ => hv v))
    ((hi.cost 2 w w).const_mul _) (fun z => heatCost_neighbors A hh u (chart 2 d z) hσ w)

end
end TriangularHilbert.Heat
end

end OAI
