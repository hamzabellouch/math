import OAI.Probability.SLE.Loewner.SmoothRawInverse

namespace OAI

/-! The exact raw inverse has a finite radial tip limit on a short
smooth-driver interval. No geometric witness is assumed. -/
noncomputable section
open Set Filter Metric Complex
open scoped Topology NNReal

namespace SLEExactGauge

lemma exists_right_limit_of_complex_lipschitz (f : ℝ → ℂ) (K : ℝ≥0)
    (hf : ∀ x > 0, ∀ y > 0, dist (f x) (f y) ≤ K*|x-y|) :
    ∃ z : ℂ, Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 z) := by
  have hre : LipschitzOnWith K (fun x => (f x).re) (Ioi (0 : ℝ)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    calc
      dist (f x).re (f y).re = |(f x-f y).re| := by simp [Real.dist_eq]
      _ ≤ ‖f x-f y‖ := Complex.abs_re_le_norm _
      _ ≤ K*|x-y| := by simpa only [dist_eq_norm] using hf x hx y hy
      _ = K*dist x y := by simp [Real.dist_eq]
  have him : LipschitzOnWith K (fun x => (f x).im) (Ioi (0 : ℝ)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    calc
      dist (f x).im (f y).im = |(f x-f y).im| := by simp [Real.dist_eq]
      _ ≤ ‖f x-f y‖ := Complex.abs_im_le_norm _
      _ ≤ K*|x-y| := by simpa only [dist_eq_norm] using hf x hx y hy
      _ = K*dist x y := by simp [Real.dist_eq]
  obtain ⟨r,hr,her⟩ := hre.extend_real
  obtain ⟨i,hi,hei⟩ := him.extend_real
  let g (x : ℝ) : ℂ := (r x : ℂ)+(i x : ℂ)*I
  have hg : Continuous g :=
    (Complex.continuous_ofReal.comp hr.continuous).add
      ((Complex.continuous_ofReal.comp hi.continuous).mul continuous_const)
  refine ⟨g 0,?_⟩
  have hh : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g 0)) :=
    (hg.tendsto 0).mono_left nhdsWithin_le_nhds
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  apply Complex.ext <;> simp [g,← her hx,← hei hx]

namespace Target

theorem inverseFlow_tip_limit_of_short_smooth_driver
    (b : Driver) (T : ℝ≥0) (b' : ℝ → ℝ)
    (hd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt (fun s => b s.toNNReal)
      (b' t) (Icc 0 (T : ℝ)) t)
    {L : ℝ} (hL : 0 ≤ L) (hb : ∀ t ∈ Icc 0 (T : ℝ), |b' t| ≤ L)
    (hsmall : L^2*(T : ℝ) ≤ 1) :
    ∃ z : ℂ, Tendsto (fun y : ℝ => inverseFlow 1 b T ((b T : ℂ)+(y : ℂ)*I))
      (𝓝[>] 0) (𝓝 z) :=
  exists_right_limit_of_complex_lipschitz _ 1 (fun _ hy _ hv => by
    simpa only [NNReal.coe_one,one_mul] using
      inverseFlow_vertical_contraction b T b' hd hL hb hsmall hy hv)

end Target
end SLEExactGauge

end

end OAI
