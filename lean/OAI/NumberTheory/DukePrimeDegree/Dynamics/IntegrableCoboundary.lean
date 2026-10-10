import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalSigmaOrder

namespace OAI

/-! # Integrable coboundaries have zero mean

Only the difference is assumed integrable. Truncating the transfer
function by one-Lipschitz clamps and applying dominated convergence
avoids any integrability assumption on the logarithmic normalization.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace DukePrimeDegree

def realClamp (M x : ℝ) : ℝ := max (-M) (min M x)

lemma realClamp_lipschitz (M : ℝ) : LipschitzWith 1 (realClamp M) :=
  (LipschitzWith.id.const_min M).const_max (-M)

lemma realClamp_eq {M x : ℝ} (hx : |x| ≤ M) : realClamp M x=x := by
  have h := abs_le.mp hx
  simp only [realClamp,min_eq_right h.2,max_eq_right h.1]

lemma realClamp_abs_le {M : ℝ} (hM : 0 ≤ M) (x : ℝ) : |realClamp M x| ≤ M := by
  apply abs_le.mpr
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

lemma realClamp_difference_le (M x y : ℝ) :
    |realClamp M x-realClamp M y| ≤ |x-y| := by
  have H := (realClamp_lipschitz M).dist_le_mul x y
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using H

theorem integral_coboundary_eq_zero {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) {f : Y → ℝ} (hf : StronglyMeasurable f)
    (hdf : Integrable (fun y => f y-f (T y)) μ) :
    (∫ y, f y-f (T y) ∂μ)=0 := by
  let F : ℕ → Y → ℝ := fun n y => realClamp n (f y)
  have hFm n : StronglyMeasurable (F n) :=
    (realClamp_lipschitz n).continuous.comp_stronglyMeasurable hf
  have hFi n : Integrable (F n) μ := by
    apply (integrable_const (n:ℝ)).mono' (hFm n).aestronglyMeasurable
    exact ae_of_all _ fun y => by
      simpa only [Real.norm_eq_abs] using realClamp_abs_le (Nat.cast_nonneg n) (f y)
  have hFTi n : Integrable (fun y => F n (T y)) μ := hT.integrable_comp_of_integrable (hFi n)
  have hInt n : (∫ y, F n (T y) ∂μ) = ∫ y, F n y ∂μ := by
    rw [←integral_map hT.measurable.aemeasurable (hFm n).aestronglyMeasurable,hT.map_eq]
  have hzero n : (∫ y, F n y-F n (T y) ∂μ)=0 := by
    rw [integral_sub (hFi n) (hFTi n),hInt n,sub_self]
  have hlim : ∀ᵐ y ∂μ, Tendsto (fun n => F n y-F n (T y)) atTop (𝓝 (f y-f (T y))) := by
    apply ae_of_all
    intro y
    obtain ⟨N,hN⟩ := exists_nat_gt (max |f y| |f (T y)|)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N:ℝ) ≤ n := Nat.cast_le.mpr hn
    have hy : |f y| ≤ (n:ℝ) := (le_max_left _ _).trans (le_of_lt hN) |>.trans hn'
    have hTy : |f (T y)| ≤ (n:ℝ) := (le_max_right _ _).trans (le_of_lt hN) |>.trans hn'
    simp only [F,realClamp_eq hy,realClamp_eq hTy]
  have hbound n : ∀ᵐ y ∂μ, ‖F n y-F n (T y)‖ ≤ ‖f y-f (T y)‖ :=
    ae_of_all _ fun y => by
      simpa only [Real.norm_eq_abs] using realClamp_difference_le n (f y) (f (T y))
  have H := tendsto_integral_of_dominated_convergence
    (fun y => ‖f y-f (T y)‖) (fun n => ((hFi n).sub (hFTi n)).aestronglyMeasurable)
    hdf.norm hbound hlim
  have H0 : Tendsto (fun n => ∫ y, F n y-F n (T y) ∂μ) atTop (𝓝 (0:ℝ)) := by
    simpa only [hzero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique H H0

end DukePrimeDegree

end

end OAI
