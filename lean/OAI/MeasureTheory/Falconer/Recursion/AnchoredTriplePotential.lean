import OAI.MeasureTheory.Falconer.Angular.GnomonicTripleKernel
import OAI.MeasureTheory.Falconer.Radial.RadialAnglePotential

namespace OAI

/-! # The actual Gaussian bad-triple weight is integrable on every retained anchor -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

noncomputable def gaussianChartTripleWeight (h : ℕ) (r : ℝ) (p q z : Space n) : ℝ≥0∞ :=
  (ENNReal.ofReal (r^(-(h:ℝ))))^3 *
    gaussianRows (n+1) h {A | ∀ i,
      |inner ℝ (gnomonicChart p : Space (n+1)) (A i)| ≤ r ∧
      |inner ℝ (gnomonicChart q : Space (n+1)) (A i)| ≤ r ∧
      |inner ℝ (gnomonicChart z : Space (n+1)) (A i)| ≤ r}

theorem anchored_bad_triple_potential (μ : Measure (Space n))
    (G : Set (Space n × Space n)) (E : Set (Space n)) (hE : MeasurableSet E)
    (p q : Space n) (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1)
    {b W K ℓ : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hpq : b ≤ ‖q-p‖)
    (hK : 0 ≤ K) (hℓ : (h:ℝ) < ℓ) (g k : ℕ)
    (hW : 8*W/b^2 ≤ 1/(2:ℝ)^g)
    (hretained : ∀ z ∈ E, (p,z) ∈ G ∧ ‖z‖ ≤ 1 ∧ b ≤ ‖z-p‖ ∧
      Real.sqrt (tripleGram (gnomonicChart p : Space (n+1))
        (gnomonicChart q : Space (n+1)) (gnomonicChart z : Space (n+1))) < W)
    (hdiag : ∀ z, (p,z) ∈ G → z ≠ p)
    (hcap : ∀ j : ℕ, j ≤ g+k → ∀ u : Space n, ‖u‖ = 1 →
      μ {z | (p,z) ∈ G ∧ dist (NormedSpace.normalize (z-p)) u < 3*(1/(2:ℝ)^j)} ≤
        ENNReal.ofReal (K*(3*(1/(2:ℝ)^j))^ℓ)) :
    (∫⁻ z in E, gaussianChartTripleWeight h (1/(2:ℝ)^(g+k)) p q z ∂μ) ≤
      ENNReal.ofReal ((gaussianTripleBandConstant/(b/4)^2)^h) *
      ENNReal.ofReal ((2:ℝ)^(h:ℝ)*((2*K*(3:ℝ)^ℓ)*(((2:ℝ)^g)^((h:ℝ)-ℓ))*
        (1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-ℓ))))) := by
  let r : ℝ := 1/(2:ℝ)^(g+k)
  let F : Space n → ℝ≥0∞ := fun z => ENNReal.ofReal ((1/max (displacementAngle p q z) r)^(h:ℝ))
  let C : ℝ≥0∞ := ENNReal.ofReal ((gaussianTripleBandConstant/(b/4)^2)^h)
  have hr : 0 < r := by dsimp [r]; positivity
  have hqne : q ≠ p := by
    intro he
    rw [he,sub_self,norm_zero] at hpq
    linarith
  have hbound (z : Space n) (hz : z ∈ E) : gaussianChartTripleWeight h r p q z ≤ C*F z := by
    obtain ⟨_,hz1,hpz,_⟩ := hretained z hz
    apply (gnomonic_triple_kernel p q z hp hq hz1 hb hb1 hr hpq hpz).trans_eq
    dsimp [C,F]
    have hCpos : 0 ≤ (gaussianTripleBandConstant/(b/4)^2)^h :=
      pow_nonneg (div_nonneg gaussianTripleBandConstant_pos.le (sq_nonneg _)) h
    rw [← ENNReal.ofReal_mul hCpos,Real.rpow_natCast]
    congr 1
    rw [← mul_pow]
    congr 1
    ring
  have hsub : E ⊆ {z | displacementAngle p q z < 1/(2:ℝ)^g} ∩ {z | (p,z) ∈ G} := by
    intro z hz
    obtain ⟨hG,hz1,hpz,hw⟩ := hretained z hz
    exact ⟨(displacementAngle_lt_of_tripleGram hp hq hz1 hb hpq hpz hw).trans_le hW,hG⟩
  have hm : μ.restrict E ≤ (μ.restrict {z | (p,z) ∈ G}).restrict
      {z | displacementAngle p q z < 1/(2:ℝ)^g} := by
    rw [Measure.restrict_restrict (measurableSet_lt (displacementAngle_measurable p q) measurable_const)]
    exact Measure.restrict_mono hsub le_rfl
  calc
    _ ≤ ∫⁻ z in E, C*F z ∂μ := lintegral_mono_ae (by
      filter_upwards [ae_restrict_mem hE] with z hz
      exact hbound z hz)
    _ = C * ∫⁻ z in E, F z ∂μ := lintegral_const_mul' C _ ENNReal.ofReal_ne_top
    _ ≤ C * ∫⁻ z in {z | displacementAngle p q z < 1/(2:ℝ)^g}, F z
        ∂μ.restrict {z | (p,z) ∈ G} := mul_le_mul' le_rfl (lintegral_mono' hm le_rfl)
    _ ≤ _ := mul_le_mul' le_rfl
      (radial_angle_potential μ G p q hqne hdiag hK (Nat.cast_nonneg _) hℓ g k hcap)

end Falconer

end OAI
