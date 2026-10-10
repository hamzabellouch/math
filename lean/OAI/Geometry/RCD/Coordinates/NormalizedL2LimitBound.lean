import OAI.Geometry.RCD.Coordinates.NormalizedUniformL2

namespace OAI

/-! # Retaining the exact normalized L2 bound in a value limit -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem square_add_le_weighted {t : ℝ} (ht : 0<t) (a b : ℝ) :
    (a+b)^2≤(1+t)*a^2+(1+t⁻¹)*b^2 := by
  have he : (1+t)*a^2+(1+t⁻¹)*b^2-(a+b)^2=t⁻¹*(t*a-b)^2 := by
    field_simp [ht.ne']
    ring
  have hp := mul_nonneg (inv_nonneg.mpr ht.le) (sq_nonneg (t*a-b))
  linarith

variable {X : Type*} [MeasurableSpace X]

theorem normalized_L2_limit_le_one (μ : ℕ → Measure X)
    (hmass : ∀ k, 0<(μ k).real univ) (u f : ℕ → X → ℝ)
    (hu : ∀ k, MemLp (u k) 2 (μ k)) (hf : ∀ k, MemLp (f k) 2 (μ k))
    (hub : ∀ k, ((μ k).real univ)⁻¹*(∫ x, (u k x)^2 ∂μ k)≤1)
    (herror : Tendsto (fun k => ((μ k).real univ)⁻¹*
      (∫ x, (f k x-u k x)^2 ∂μ k)) atTop (𝓝 0))
    {V : ℝ} (hvalue : Tendsto (fun k => ((μ k).real univ)⁻¹*
      (∫ x, (f k x)^2 ∂μ k)) atTop (𝓝 V)) : V≤1 := by
  apply le_of_forall_pos_le_add
  intro t ht
  have hi (k : ℕ) : ((μ k).real univ)⁻¹*(∫ x, (f k x)^2 ∂μ k)≤
      1+t+(1+t⁻¹)*(((μ k).real univ)⁻¹*(∫ x, (f k x-u k x)^2 ∂μ k)) := by
    have he := (hf k).sub (hu k)
    have hI := integral_mono_ae (hf k).integrable_sq
      (((hu k).integrable_sq.const_mul (1+t)).add (he.integrable_sq.const_mul (1+t⁻¹)))
      (Eventually.of_forall fun x => by
        simpa only [Pi.add_apply,Pi.sub_apply,add_sub_cancel] using
          square_add_le_weighted ht (u k x) (f k x-u k x))
    simp only [Pi.add_apply] at hI
    rw [integral_add ((hu k).integrable_sq.const_mul (1+t)) (he.integrable_sq.const_mul (1+t⁻¹)),
      integral_const_mul,integral_const_mul] at hI
    calc
      _ ≤ ((μ k).real univ)⁻¹*((1+t)*(∫ x, (u k x)^2 ∂μ k)+
          (1+t⁻¹)*(∫ x, (f k x-u k x)^2 ∂μ k)) :=
        mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr (hmass k).le)
      _ = (1+t)*(((μ k).real univ)⁻¹*(∫ x, (u k x)^2 ∂μ k))+
          (1+t⁻¹)*(((μ k).real univ)⁻¹*(∫ x, (f k x-u k x)^2 ∂μ k)) := by ring
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left (hub k) (show 0≤1+t by linarith)]
  have hright : Tendsto (fun k => 1+t+(1+t⁻¹)*(((μ k).real univ)⁻¹*
      (∫ x, (f k x-u k x)^2 ∂μ k))) atTop (𝓝 (1+t)) := by
    simpa only [mul_zero,add_zero] using (herror.const_mul (1+t⁻¹)).const_add (1+t)
  exact le_of_tendsto_of_tendsto hvalue hright (Eventually.of_forall hi)

end RegularPointCoordinates

end

end OAI
