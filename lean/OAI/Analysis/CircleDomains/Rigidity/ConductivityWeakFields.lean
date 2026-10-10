import OAI.Analysis.CircleDomains.Rigidity.ConductivityGlobalEnergy
import OAI.Analysis.CircleDomains.Sobolev.WeakPairEnergy

namespace OAI

/-! Global L2 weak limits of the two error-gradient components of the
actual conductivity heights. The paired energy budget is retained. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem PlaneLocalWeakComplex.imag_aestronglyMeasurable
    {f : EuclideanPlane → ℂ} (D : PlaneLocalWeakComplex f) (i : Fin 2) :
    AEStronglyMeasurable (fun p => D.imagGradient p i) volume :=
  (aecover_ball (μ := volume) (x := (0 : EuclideanPlane)) tendsto_id).aestronglyMeasurable
    (fun R => (D.imag_memLp R i).aestronglyMeasurable)

 theorem PlaneLocalWeakComplex.error_memLp
    {f : EuclideanPlane → ℂ} (D : PlaneLocalWeakComplex f)
    (hI : Integrable (fun p => D.imagGradient p 0^2+(D.imagGradient p 1-1)^2)) :
    MemLp (fun p => D.imagGradient p 0) 2 volume ∧
      MemLp (fun p => D.imagGradient p 1-1) 2 volume := by
  have hm0 := D.imag_aestronglyMeasurable 0
  have hm1 : AEStronglyMeasurable (fun p => D.imagGradient p 1-1) volume :=
    (D.imag_aestronglyMeasurable 1).sub aestronglyMeasurable_const
  constructor
  · apply (memLp_two_iff_integrable_sq hm0).mpr
    exact hI.mono' (hm0.pow 2) (Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact le_add_of_nonneg_right (sq_nonneg _)))
  · apply (memLp_two_iff_integrable_sq hm1).mpr
    exact hI.mono' (hm1.pow 2) (Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact le_add_of_nonneg_left (sq_nonneg _)))

 theorem conductivity_weak_error_fields
    (f : ℕ → EuclideanPlane → ℂ) (D : ∀ n, PlaneLocalWeakComplex (f n))
    {B : ℝ}
    (hI : ∀ n, Integrable (fun p => (D n).imagGradient p 0^2+((D n).imagGradient p 1-1)^2))
    (hB : ∀ n, (∫ p, (D n).imagGradient p 0^2+((D n).imagGradient p 1-1)^2) ≤ B) :
    ∃ (G₀ G₁ : Lp ℝ 2 (volume : Measure EuclideanPlane)) (s : ℕ → ℕ),
      StrictMono s ∧
      (∀ w : Lp ℝ 2 (volume : Measure EuclideanPlane),
        Tendsto (fun n => ∫ p, (D (s n)).imagGradient p 0*w p) atTop
          (𝓝 (∫ p, G₀ p*w p))) ∧
      (∀ w : Lp ℝ 2 (volume : Measure EuclideanPlane),
        Tendsto (fun n => ∫ p, ((D (s n)).imagGradient p 1-1)*w p) atTop
          (𝓝 (∫ p, G₁ p*w p))) ∧
      (∫ p, G₀ p^2+G₁ p^2) ≤ B := by
  let u₀ : ℕ → EuclideanPlane → ℝ := fun n p => (D n).imagGradient p 0
  let u₁ : ℕ → EuclideanPlane → ℝ := fun n p => (D n).imagGradient p 1-1
  have hm₀ (n : ℕ) : MemLp (u₀ n) 2 volume := ((D n).error_memLp (hI n)).1
  have hm₁ (n : ℕ) : MemLp (u₁ n) 2 volume := ((D n).error_memLp (hI n)).2
  have hnorm (n : ℕ) : ‖(hm₀ n).toLp (u₀ n)‖ ≤ B+1 ∧
      ‖(hm₁ n).toLp (u₁ n)‖ ≤ B+1 := by
    have hn0 : ‖(hm₀ n).toLp (u₀ n)‖^2 = ∫ p, u₀ n p^2 := by
      rw [Lp.norm_toLp, integral_sq_eq_eLpNorm_toReal_sq (hm₀ n)]
    have hn1 : ‖(hm₁ n).toLp (u₁ n)‖^2 = ∫ p, u₁ n p^2 := by
      rw [Lp.norm_toLp, integral_sq_eq_eLpNorm_toReal_sq (hm₁ n)]
    have hb := hB n
    change (∫ p, u₀ n p^2+u₁ n p^2) ≤ B at hb
    rw [integral_add (hm₀ n).integrable_sq (hm₁ n).integrable_sq, ← hn0, ← hn1] at hb
    constructor <;> nlinarith [sq_nonneg (‖(hm₀ n).toLp (u₀ n)‖-1),
      sq_nonneg (‖(hm₁ n).toLp (u₁ n)‖-1), sq_nonneg ‖(hm₀ n).toLp (u₀ n)‖,
      sq_nonneg ‖(hm₁ n).toLp (u₁ n)‖]
  obtain ⟨G₀, _, s₀, hs₀, h₀⟩ := exists_L2_weak_subsequence volume u₀ hm₀ (B+1)
    (fun n => (hnorm n).1)
  obtain ⟨G₁, _, s₁, hs₁, h₁⟩ := exists_L2_weak_subsequence volume (u₁ ∘ s₀)
    (fun n => hm₁ (s₀ n)) (B+1) (fun n => (hnorm (s₀ n)).2)
  let s := s₀ ∘ s₁
  have hlim₀ (w : Lp ℝ 2 (volume : Measure EuclideanPlane)) :
      Tendsto (fun n => ∫ p, u₀ (s n) p*w p) atTop (𝓝 (∫ p, G₀ p*w p)) :=
    (h₀ w).comp hs₁.tendsto_atTop
  refine ⟨G₀, G₁, s, hs₀.comp hs₁, hlim₀, h₁, ?_⟩
  exact paired_L2_energy_le (fun n => hm₀ (s n)) (fun n => hm₁ (s n)) G₀ G₁
    (ε := fun _ => 0) tendsto_const_nhds
    (Eventually.of_forall (fun n => by simpa only [add_zero] using hB (s n)))
    (hlim₀ G₀) (h₁ G₁)

end CircleDomainRigidity

end

end OAI
