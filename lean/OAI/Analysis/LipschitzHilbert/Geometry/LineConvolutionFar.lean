import OAI.Analysis.LipschitzHilbert.Fourier.LineKernelScaling

namespace OAI

/-! First kernel moments control the contribution of bounded data outside
an enlarged interval. This is the far part of the smooth Carleson measure. -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem lineConvolution_bound_of_gap (K : ℝ → ℂ)
    (hK : Integrable (fun t => |t| *‖K t‖)) (f : ℝ → ℂ)
    (B d x : ℝ) (hB : 0≤B) (hd : 0<d) (hfb : ∀ y, ‖f y‖≤B)
    (hgap : ∀ t, |t|<d → f (x-t)=0) :
    ‖lineConvolution K f x‖≤(B/d)*(∫ t, |t| *‖K t‖) := by
  have h := norm_integral_le_of_norm_le (hK.const_mul (B/d))
    (Filter.Eventually.of_forall (fun t => show ‖K t*f (x-t)‖≤(B/d)*(|t| *‖K t‖) from by
      by_cases ht : |t|<d
      · rw [hgap t ht,mul_zero,norm_zero]
        positivity
      · have htd : d≤|t| := le_of_not_gt ht
        have hb : B≤(B/d)*|t| := by
          calc
            B = (B/d)*d := (div_mul_cancel₀ B hd.ne').symm
            _ ≤ _ := mul_le_mul_of_nonneg_left htd (div_nonneg hB hd.le)
        rw [norm_mul]
        calc
          _ ≤ ‖K t‖*((B/d)*|t|) := mul_le_mul_of_nonneg_left ((hfb _).trans hb) (norm_nonneg _)
          _ = _ := by ring))
  simpa only [lineConvolution,integral_const_mul] using h

theorem lineProjection_far_bound (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W)
    (f : ℝ → ℂ) (B d x : ℝ) (hB : 0≤B) (hd : 0<d)
    (hfb : ∀ y, ‖f y‖≤B) (hgap : ∀ t, |t|<d → f (x-t)=0) :
    ‖lineConvolution (lineProjectionKernel q W hW.ne') f x‖≤
      (B*W/d)*(∫ t, |t| *‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖) := by
  have h := lineConvolution_bound_of_gap (lineProjectionKernel q W hW.ne')
    (schwartz_first_absolute_moment_integrable _) f B d x hB hd hfb hgap
  rw [lineProjectionKernel_moment1 q W hW] at h
  convert h using 1; ring

theorem lineProjection_far_energy (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W)
    (f : ℝ → ℂ) (B d : ℝ) (hB : 0≤B) (hd : 0<d) (hfb : ∀ y, ‖f y‖≤B)
    (J : Set ℝ) (hJ : volume J<⊤)
    (hgap : ∀ x∈J, ∀ t, |t|<d → f (x-t)=0) :
    (∫ x in J, ‖lineConvolution (lineProjectionKernel q W hW.ne') f x‖^2)≤
      ((B*W/d)*(∫ t, |t| *‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖))^2*volume.real J := by
  have h := norm_setIntegral_le_of_norm_le_const (μ:=volume) (s:=J)
    (f:=fun x => ‖lineConvolution (lineProjectionKernel q W hW.ne') f x‖^2)
    (C:=((B*W/d)*(∫ t, |t| *‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖))^2) hJ (fun x hx => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (lineProjection_far_bound q W hW f B d x hB hd hfb (hgap x hx)) 2)
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => sq_nonneg _)] at h
  exact h

theorem outside_enlarged_interval_gap (f : ℝ → ℂ) (a b d x t : ℝ)
    (hx : x∈Icc a b) (ht : |t|<d) :
    (Icc (a-d) (b+d))ᶜ.indicator f (x-t)=0 := by
  apply indicator_of_notMem
  intro hnot
  apply hnot
  have hab := abs_lt.mp ht
  exact ⟨by linarith [hx.1,hab.2],by linarith [hx.2,hab.1]⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
