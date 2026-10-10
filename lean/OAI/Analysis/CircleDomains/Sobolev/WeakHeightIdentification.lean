import OAI.Analysis.CircleDomains.Uniformization.HeightTestLimit
import OAI.Analysis.CircleDomains.Rigidity.ConductivityWeakFields

namespace OAI

/-! Identification of weak error-gradient limits with the derivatives
of the actual continuous height limit. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def heightLimitGradient (G₀ G₁ : Lp ℝ 2 (volume : Measure EuclideanPlane))
    (p : EuclideanPlane) : EuclideanPlane :=
  WithLp.toLp 2 (fun i => if i = 0 then G₀ p else G₁ p+1)

 theorem weak_height_identification
    (f : ℕ → EuclideanPlane → ℂ) (D : ∀ n, PlaneLocalWeakComplex (f n))
    (hf : ∀ n, Continuous (f n)) {v : EuclideanPlane → ℝ}
    (hp : ∀ p, Tendsto (fun n => (f n p).im) atTop (𝓝 (v p)))
    (hb : ∀ K : Set EuclideanPlane, IsCompact K →
      ∃ C : ℝ, ∀ n p, p ∈ K → ‖(f n p).im‖ ≤ C)
    (hI : ∀ n, Integrable (fun p => (D n).imagGradient p 0^2+((D n).imagGradient p 1-1)^2))
    (G₀ G₁ : Lp ℝ 2 (volume : Measure EuclideanPlane))
    (h₀ : ∀ w : Lp ℝ 2 (volume : Measure EuclideanPlane),
      Tendsto (fun n => ∫ p, (D n).imagGradient p 0*w p) atTop (𝓝 (∫ p, G₀ p*w p)))
    (h₁ : ∀ w : Lp ℝ 2 (volume : Measure EuclideanPlane),
      Tendsto (fun n => ∫ p, ((D n).imagGradient p 1-1)*w p) atTop (𝓝 (∫ p, G₁ p*w p))) :
    DeGiorgi.HasWeakGrad (heightLimitGradient G₀ G₁) v univ := by
  have hpair {u : ℕ → EuclideanPlane → ℝ} {G : EuclideanPlane → ℝ}
      (h : ∀ w : Lp ℝ 2 (volume : Measure EuclideanPlane),
        Tendsto (fun n => ∫ p, u n p*w p) atTop (𝓝 (∫ p, G p*w p)))
      {ψ : EuclideanPlane → ℝ} (hψ : MemLp ψ 2 volume) :
      Tendsto (fun n => ∫ p, u n p*ψ p) atTop (𝓝 (∫ p, G p*ψ p)) := by
    have he (a : EuclideanPlane → ℝ) :
        (∫ p, a p*hψ.toLp ψ p) = ∫ p, a p*ψ p := by
      apply integral_congr_ae
      filter_upwards [hψ.coeFn_toLp] with p hp
      rw [hp]
    simpa only [he] using h (hψ.toLp ψ)
  intro i ψ hψ hs _
  simp only [Measure.restrict_univ]
  let test : EuclideanPlane → ℝ := fun p => fderiv ℝ ψ p (EuclideanSpace.single i 1)
  have ht : Continuous test := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hst : HasCompactSupport test := hs.fderiv_apply (𝕜 := ℝ) _
  have hl := height_test_integral_tendsto (fun n p => (f n p).im)
    (fun n => Complex.continuous_im.comp (hf n)) hp hb ht hst
  have hψL : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hs
  have hright : Tendsto (fun n => ∫ p, (D n).imagGradient p i*ψ p) atTop
      (𝓝 (∫ p, heightLimitGradient G₀ G₁ p i*ψ p)) := by
    fin_cases i
    · simpa [heightLimitGradient] using hpair h₀ hψL
    · have hh := (hpair h₁ hψL).add_const (∫ p, ψ p)
      have hψI : Integrable ψ volume := hψ.continuous.integrable_of_hasCompactSupport hs
      have he (n : ℕ) : (∫ p, ((D n).imagGradient p 1-1)*ψ p)+(∫ p, ψ p) =
          ∫ p, (D n).imagGradient p 1*ψ p := by
        have hadd := integral_add (((D n).error_memLp (hI n)).2.integrable_mul hψL) hψI
        simp only [Pi.mul_apply] at hadd
        rw [← hadd]
        congr 1
        funext p
        ring
      have hG : (∫ p, G₁ p*ψ p)+(∫ p, ψ p) = ∫ p, (G₁ p+1)*ψ p := by
        have hadd := integral_add ((Lp.memLp G₁).integrable_mul hψL) hψI
        simp only [Pi.mul_apply] at hadd
        rw [← hadd]
        congr 1
        funext p
        ring
      simpa [he, hG, heightLimitGradient] using hh
  have hweak (n : ℕ) : (∫ p, (f n p).im*test p) =
      -(∫ p, (D n).imagGradient p i*ψ p) := by
    simpa only [Measure.restrict_univ] using (D n).imag_weak i ψ hψ hs (subset_univ _)
  have hh : Tendsto (fun n => -(∫ p, (D n).imagGradient p i*ψ p)) atTop
      (𝓝 (∫ p, v p*test p)) := hl.congr' (Eventually.of_forall hweak)
  exact tendsto_nhds_unique hh hright.neg

 def heightLimitWitness (G₀ G₁ : Lp ℝ 2 (volume : Measure EuclideanPlane))
    {v : EuclideanPlane → ℝ} (hv : Continuous v)
    (hw : DeGiorgi.HasWeakGrad (heightLimitGradient G₀ G₁) v univ) (R : ℝ) :
    DeGiorgi.MemW1pWitness 2 v (ball 0 R) where
  memLp := continuous_memLp_ball hv R
  weakGrad := heightLimitGradient G₀ G₁
  weakGrad_component_memLp := by
    intro i
    let : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanPlane) R)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    fin_cases i
    · exact (Lp.memLp G₀).restrict _
    · exact ((Lp.memLp G₁).restrict _).add (memLp_const 1)
  isWeakGrad := fun i => weakPartial_restrict_from_univ (hw i) _

end CircleDomainRigidity

end

end OAI
