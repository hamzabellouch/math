import OAI.Analysis.CircleDomains.Sobolev.WeakHeightIdentification
import OAI.Analysis.CircleDomains.Sobolev.RestrictedWeakPairing

namespace OAI

/-! Vanishing complementary energies force the actual limiting height
gradient to vanish there, including on positive-area dust. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem weak_height_gradient_zero
    (f : ℕ → EuclideanPlane → ℂ) (D : ∀ n, PlaneLocalWeakComplex (f n))
    (hI : ∀ n, Integrable (fun p => (D n).imagGradient p 0^2+((D n).imagGradient p 1-1)^2))
    (G₀ G₁ : Lp ℝ 2 (volume : Measure EuclideanPlane))
    (h₀ : ∀ w : Lp ℝ 2 (volume : Measure EuclideanPlane),
      Tendsto (fun n => ∫ p, (D n).imagGradient p 0*w p) atTop (𝓝 (∫ p, G₀ p*w p)))
    (h₁ : ∀ w : Lp ℝ 2 (volume : Measure EuclideanPlane),
      Tendsto (fun n => ∫ p, ((D n).imagGradient p 1-1)*w p) atTop (𝓝 (∫ p, G₁ p*w p)))
    {F : Set EuclideanPlane} (hF : MeasurableSet F) (hFfin : volume F < ∞)
    (he : Tendsto (fun n => ∫ p in F,
      (D n).imagGradient p 0^2+(D n).imagGradient p 1^2) atTop (𝓝 0)) :
    ∀ᵐ p ∂volume.restrict F, heightLimitGradient G₀ G₁ p = 0 := by
  let μ := volume.restrict F
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hFfin.ne
  have hG₀ : MemLp G₀ 2 μ := (Lp.memLp G₀).restrict F
  have hG₁ : MemLp (fun p => G₁ p+1) 2 μ := ((Lp.memLp G₁).restrict F).add (memLp_const 1)
  let V₀ := hG₀.toLp G₀
  let V₁ := hG₁.toLp (fun p => G₁ p+1)
  have hm₀ (n : ℕ) : MemLp (fun p => (D n).imagGradient p 0) 2 μ :=
    (((D n).error_memLp (hI n)).1).restrict F
  have hm₁ (n : ℕ) : MemLp (fun p => (D n).imagGradient p 1) 2 μ := by
    have hh := ((((D n).error_memLp (hI n)).2).restrict F).add (memLp_const (1 : ℝ))
    convert hh using 1
    funext p
    simp only [Pi.add_apply]
    ring
  have hp₀ (w : Lp ℝ 2 μ) :
      Tendsto (fun n => ∫ p, (D n).imagGradient p 0*w p ∂μ) atTop
        (𝓝 (∫ p, V₀ p*w p ∂μ)) := by
    have hh := restricted_shifted_weak_pairing hF
      (fun n => ((D n).error_memLp (hI n)).1) G₀ h₀ 0 w
    simp only [add_zero] at hh
    convert hh using 1
    congr 1
    apply integral_congr_ae
    filter_upwards [hG₀.coeFn_toLp] with p hp
    rw [hp]
  have hp₁ (w : Lp ℝ 2 μ) :
      Tendsto (fun n => ∫ p, (D n).imagGradient p 1*w p ∂μ) atTop
        (𝓝 (∫ p, V₁ p*w p ∂μ)) := by
    have hh := restricted_shifted_weak_pairing hF
      (fun n => ((D n).error_memLp (hI n)).2) G₁ h₁ 1 w
    simp only [sub_add_cancel] at hh
    convert hh using 1
    congr 1
    apply integral_congr_ae
    filter_upwards [hG₁.coeFn_toLp] with p hp
    rw [hp]
  have hb : (∫ p, V₀ p^2+V₁ p^2 ∂μ) ≤ 0 :=
    paired_L2_energy_le hm₀ hm₁ V₀ V₁ (B := 0) he (Eventually.of_forall (fun n => by
      change (∫ p in F, (D n).imagGradient p 0^2+(D n).imagGradient p 1^2) ≤
        0+(∫ p in F, (D n).imagGradient p 0^2+(D n).imagGradient p 1^2)
      exact le_add_of_nonneg_left (le_refl 0)))
      (hp₀ V₀) (hp₁ V₁)
  have hi : Integrable (fun p => V₀ p^2+V₁ p^2) μ :=
    (Lp.memLp V₀).integrable_sq.add (Lp.memLp V₁).integrable_sq
  have hzero : (∫ p, V₀ p^2+V₁ p^2 ∂μ) = 0 :=
    le_antisymm hb (integral_nonneg (fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun p => add_nonneg (sq_nonneg (V₀ p)) (sq_nonneg (V₁ p))) hi).mp hzero
  filter_upwards [hae, hG₀.coeFn_toLp, hG₁.coeFn_toLp] with p hp h0 h1
  change V₀ p^2+V₁ p^2 = 0 at hp
  change V₀ p = G₀ p at h0
  change V₁ p = G₁ p+1 at h1
  rw [h0, h1] at hp
  have hp' : G₀ p^2+(G₁ p+1)^2 = 0 := hp
  have hz0 : G₀ p = 0 := by nlinarith [sq_nonneg (G₁ p+1)]
  have hz1 : G₁ p+1 = 0 := by nlinarith [sq_nonneg (G₀ p)]
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  funext i
  fin_cases i <;> simp [heightLimitGradient, hz0, hz1]

end CircleDomainRigidity

end

end OAI
