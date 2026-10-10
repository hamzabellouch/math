import Mathlib
import OAI.Analysis.HardSphere.Geometry.FreePathExpectation
import OAI.Analysis.HardSphere.PathBounds.FreeVisitTravel
import OAI.Analysis.HardSphere.Cutoffs.MeshMoment

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

def meshEvent {L : Length} (m : ℕ) (E : Set (ConfigurationPath 1 L)) :=
  {ω : ConfigurationPath 1 L | ∃ j : Fin m, meshSegment j ω ∈ E}
lemma meshEvent_measurable {L : Length} (m : ℕ) {E : Set (ConfigurationPath 1 L)} (hE : MeasurableSet E) :
    MeasurableSet (meshEvent m E) := by
  simp only [meshEvent,ofPred_exists]
  exact MeasurableSet.iUnion (fun j ↦ hE.preimage (meshSegment_continuous L j).measurable)

lemma meshEvent_free_bound {L : Length} (m : ℕ) (hm : 0 < m) {E : Set (ConfigurationPath 1 L)}
    (hE : MeasurableSet E) {τ : ℝ} (hτ : 0<τ) (p : ℝ≥0∞)
    (hp : ∀ X : Configuration 1 L, coordinateWiener 1 {w | freeTrajectory 1 L τ w X ∈ E} ≤ p)
    (X : Configuration 1 L) :
    coordinateWiener 1 {w | freeTrajectory 1 L ((m:ℝ)*τ) w X ∈ meshEvent m E} ≤ (m:ℝ≥0∞)*p := by
  let F : ConfigurationPath 1 L → ℝ≥0∞ := E.indicator (fun _ ↦ 1)
  have hF : Measurable F := measurable_const.indicator hE
  have hB (Y : Configuration 1 L) : ∫⁻ w,F (freeTrajectory 1 L τ w Y) ∂coordinateWiener 1 ≤ p := by
    have hEv : MeasurableSet {w | freeTrajectory 1 L τ w Y ∈ E} :=
      hE.preimage ((freeTrajectory_continuous 1 L τ).comp (continuous_id.prodMk continuous_const)).measurable
    change ∫⁻ w,({w | freeTrajectory 1 L τ w Y ∈ E}.indicator (fun _ ↦ 1)) w ∂coordinateWiener 1 ≤ p
    simpa only [lintegral_indicator_const hEv,one_mul] using hp Y
  have hEv : MeasurableSet {w | freeTrajectory 1 L ((m:ℝ)*τ) w X ∈ meshEvent m E} :=
    (meshEvent_measurable m hE).preimage ((freeTrajectory_continuous 1 L ((m:ℝ)*τ)).comp (continuous_id.prodMk continuous_const)).measurable
  calc
    _ = ∫⁻w,({w | freeTrajectory 1 L ((m:ℝ)*τ) w X ∈ meshEvent m E}.indicator (fun _ ↦ (1:ℝ≥0∞))) w ∂coordinateWiener 1 :=
      by rw [lintegral_indicator_const hEv,one_mul]
    _ ≤ ∫⁻w,meshSum m F (freeTrajectory 1 L ((m:ℝ)*τ) w X) ∂coordinateWiener 1 := by
      apply lintegral_mono
      intro w
      by_cases hw : freeTrajectory 1 L ((m:ℝ)*τ) w X ∈ meshEvent m E
      · rw [Set.indicator_of_mem (show w ∈ {w | freeTrajectory 1 L ((m:ℝ)*τ) w X ∈ meshEvent m E} from hw)]
        obtain ⟨j,hj⟩ := hw
        have hle := Finset.single_le_sum (f := fun j : Fin m ↦ F (meshSegment j (freeTrajectory 1 L ((m:ℝ)*τ) w X)))
          (fun _ _ ↦ bot_le) (Finset.mem_univ j)
        simpa only [F,meshSum,Set.indicator_of_mem hj] using hle
      · rw [Set.indicator_of_notMem (show w ∉ {w | freeTrajectory 1 L ((m:ℝ)*τ) w X ∈ meshEvent m E} from hw)]
        exact bot_le
    _ ≤ (m:ℝ≥0∞)*p := meshSum_free_bound F hF hτ p hB m hm X

end HardSphere.PathCutoff

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace HardSphere.PathCutoff

lemma exp_cap_le {x B : ℝ} (hB : 0 < B) (hx : 0 ≤ x) :
    Real.exp (min x B/B)  ≤  1+(Real.exp 1-1)*x/B := by
  have h0 : 0 ≤ min x B/B := div_nonneg (le_min hx hB.le) hB.le
  have h1 : min x B/B ≤ 1 := (div_le_one hB).mpr (min_le_right _ _)
  have h := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (1:ℝ))
    (sub_nonneg.mpr h1) h0 (by ring : 1-min x B/B+min x B/B=1)
  simp only [smul_eq_mul,mul_zero,mul_one,zero_add,Real.exp_zero] at h
  calc
    Real.exp (min x B/B) ≤ 1+(Real.exp 1-1)*(min x B)/B := by
      convert h using 1
      ring
    _  ≤  1+(Real.exp 1-1)*x/B := by
      gcongr
      · exact sub_nonneg.mpr (by simp)
      · exact min_le_left _ _

lemma exp_cap_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω→ℝ} (hX : Integrable X μ) (hX0 : ∀ᵐω ∂μ,0 ≤ X ω) {B : ℝ} (hB : 0 < B) :
    ∫⁻ω, ENNReal.ofReal (Real.exp (min (X ω) B/B)) ∂μ  ≤
      ENNReal.ofReal (Real.exp ((Real.exp 1-1)*(∫ω,X ω ∂μ)/B)) := by
  have hi : Integrable (fun ω ↦ 1+(Real.exp 1-1)*X ω/B) μ :=
    (integrable_const 1).add ((hX.const_mul _).div_const _)
  calc
    _  ≤  ∫⁻ω,ENNReal.ofReal (1+(Real.exp 1-1)*X ω/B) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hX0] with ω hω
      exact ENNReal.ofReal_le_ofReal (exp_cap_le hB hω)
    _ = ENNReal.ofReal (1+(Real.exp 1-1)*(∫ω,X ω ∂μ)/B) := by
      rw [←ofReal_integral_eq_lintegral_ofReal hi]
      · congr 1
        rw [integral_add (integrable_const _) ((hX.const_mul _).div_const _),integral_const,
          integral_div,integral_const_mul,probReal_univ,one_smul]
      · filter_upwards [hX0] with ω hω
        have he : 0 ≤ Real.exp 1-1 := sub_nonneg.mpr (by simp)
        positivity
    _  ≤  _ := ENNReal.ofReal_le_ofReal (by linarith [Real.add_one_le_exp ((Real.exp 1-1)*(∫ω,X ω ∂μ)/B)])

end HardSphere.PathCutoff

end
end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits BathSlice
attribute [local irreducible] torusDistance freeTrajectory

def noiseSize (w : CoordinatePaths 1) : ℝ := ∑ j : Fin 3, ‖w (0,j)‖
lemma noiseSize_nonneg (w : CoordinatePaths 1) : 0 ≤ noiseSize w :=
  Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
lemma noiseSize_continuous : Continuous noiseSize := by unfold noiseSize; fun_prop
lemma noiseSize_coord (w : CoordinatePaths 1) (j : Fin 3) : ‖w (0,j)‖ ≤ noiseSize w :=
  by
    change ‖w (0,j)‖ ≤ ∑ i : Fin 3, ‖w (0,i)‖
    exact Finset.single_le_sum (fun i _ ↦ norm_nonneg (w (0,i))) (Finset.mem_univ j)

lemma free_diameter_le (L : Length) (t : ℝ) (w : CoordinatePaths 1) (y : Torus L) {R : ℝ}
    (hR : 0 ≤ R) (hw : ∀ j, ‖w (0,j)‖ ≤ R) :
    intervalDiameter 0 1 (freeTrajectory 1 L t w (oneConfiguration y)) ≤ 6*Real.sqrt (2*t)*R := by
  have hd (s : Time) : torusDistance L (freeTrajectory 1 L t w (oneConfiguration y) s 0) y ≤
      3*(Real.sqrt (2*t)*R) := by
    apply torusDistance_le_three_of_coord L _ _ (by positivity)
    intro j
    apply (freeTrajectory_coord_dist_le L t w (oneConfiguration y) 0 s j).trans
    exact mul_le_mul_of_nonneg_left (hw j) (Real.sqrt_nonneg _)
  apply intervalDiameter_le _ _ _ (by positivity)
  intro s q
  have htri := torusDistance_triangle' L
    (freeTrajectory 1 L t w (oneConfiguration y) (intervalTime 0 1 s) 0) y
    (freeTrajectory 1 L t w (oneConfiguration y) (intervalTime 0 1 q) 0)
  rw [torusDistance_comm L y] at htri
  linarith [hd (intervalTime 0 1 s), hd (intervalTime 0 1 q)]

lemma free_diameter_noise (L : Length) {t r : ℝ} (hr : 0<r) (ht : t ≤ r^2)
    (w : CoordinatePaths 1) (y : Torus L) :
    intervalDiameter 0 1 (freeTrajectory 1 L t w (oneConfiguration y))/r ≤ 12*noiseSize w := by
  have hs : Real.sqrt (2*t) ≤ 2*r := Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith [sq_nonneg r]⟩
  have h := free_diameter_le L t w y (noiseSize_nonneg w) (noiseSize_coord w)
  apply (div_le_iff₀ hr).mpr
  have hh := mul_le_mul_of_nonneg_right hs (show 0 ≤ 6*noiseSize w from mul_nonneg (by norm_num) (noiseSize_nonneg w))
  nlinarith

lemma noiseSize_memLp (p : ℝ≥0∞) (hp : p≠⊤) : MemLp noiseSize p (coordinateWiener 1) := by
  unfold noiseSize
  apply memLp_finsetSum
  intro j _
  exact ((IsGaussian.memLp_id wiener p hp).norm).comp_measurePreserving
    (measurePreserving_eval (fun _ : Direction 1 ↦ wiener) (0,j))

lemma integrable_cubicNoise : Integrable (fun w : CoordinatePaths 1 ↦ (1+12*noiseSize w)^3) (coordinateWiener 1) := by
  have h0 : MemLp (fun _ : CoordinatePaths 1 ↦ (1:ℝ)) (3:ℝ≥0∞) (coordinateWiener 1) := memLp_const 1
  have h1 := (noiseSize_memLp 3 (by norm_num)).const_mul 12
  have h : MemLp (fun w : CoordinatePaths 1 ↦ 1+12*noiseSize w) (3:ℝ≥0∞) (coordinateWiener 1) := h0.add h1
  have hi := h.integrable_norm_pow (by norm_num : (3:ℕ)≠0)
  have hpos (w : CoordinatePaths 1) : 0 ≤ 1+12*noiseSize w := by have := noiseSize_nonneg w; positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hpos _)] using hi

end HardSphere.PathCutoff

end
end

end

end OAI
