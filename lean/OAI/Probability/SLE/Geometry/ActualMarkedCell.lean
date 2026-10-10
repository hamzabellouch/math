import OAI.Probability.SLE.Mass.CellMassComparison

namespace OAI

/-! The actual centered argument and modulus supply the marked disk
coordinates in the physical cell comparison. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Multipoint

lemma IsCapacityTwoWitness.live_marked_polar
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (t : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ t) :
    let q := G t z-(U t:ℂ)
    0 < ‖q‖₊ ∧ q.arg ∈ Ioo (0:ℝ) Real.pi ∧
      G t z=(U t:ℂ)+(‖q‖₊:ℂ)*Complex.exp (q.arg*Complex.I) := by
  let q := G t z-(U t:ℂ)
  have hq : 0 < q.im := by
    simpa only [q,Complex.sub_im,Complex.ofReal_im,sub_zero] using hw.imag_positive t z hz
  have hn : q ≠ 0 := by intro h; simp only [h,Complex.zero_im,lt_self_iff_false] at hq
  refine ⟨by exact_mod_cast norm_pos_iff.mpr hn,?_,?_⟩
  · refine ⟨lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hq.le) ?_,
      Complex.arg_lt_pi_iff.mpr (Or.inr hq.ne')⟩
    intro h
    exact hq.ne' (Complex.arg_eq_zero_iff.mp h.symm).2
  · change G t z=(U t:ℂ)+(‖q‖:ℂ)*Complex.exp (q.arg*Complex.I)
    rw [Complex.norm_mul_exp_arg_mul_I]
    dsimp only [q]
    ring

lemma IsCapacityTwoWitness.cell_mass_comparison_at_marked_point
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hgrowth : PublishedDiskUnivalentGrowth)
    (κ : ℝ) (hκ : 0 < κ) (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ t)
    (r : ℝ) (hr : 0 < r) (hR : fullRadius G t z=(2048*Real.pi)*r)
    (μ : Measure upperHalfPlane) [IsFiniteMeasureOnCompacts μ] :
    ∃ (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (a : ℝ≥0) (ha : 0 < a),
      θ=(G t z-(U t:ℂ)).arg ∧ a=‖G t z-(U t:ℂ)‖₊ ∧
      let ν := weightedImageMass (fun w : upperHalfPlane => F t ((w:ℂ)+(U t:ℂ)))
        (fun w : upperHalfPlane => ENNReal.ofReal
          (‖deriv (F t) ((w:ℂ)+(U t:ℂ))‖^dimension κ)) (dilationMass κ a ha μ)
      let L := ENNReal.ofReal (compactWeightedMass (Target.diskMassWeight κ θ hθ)
        (Target.diskSourceHalfPlane θ) μ)
      ENNReal.ofReal (((128*Real.pi)*r)^dimension κ)*L ≤
          ν (closedBall z ((4096*Real.pi)*r)) ∧
        ∀ A : Set ℂ, A ⊆ closedBall z (2*r) →
          ν A ≤ ENNReal.ofReal (((32768*Real.pi)*r)^dimension κ)*L := by
  obtain ⟨ha,hθ,he⟩ := hw.live_marked_polar t z hz
  exact ⟨_,hθ,_,ha,rfl,rfl,hw.cell_mass_comparison hgrowth κ hκ _ hθ t z hz r hr hR _ ha he μ⟩

end SLEExactGauge

end

end OAI
