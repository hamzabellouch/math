import OAI.NumberTheory.Ostmann.Dirichlet.SmoothedExplicitIntegrand

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Dirichlet
open Complex Set Filter MeasureTheory
open scoped Topology SchwartzMap

def smoothTailMajorant (t : ℝ) : ℝ := (1+|t|)^(-(2:ℝ))

theorem smoothTailMajorant_nonneg (t : ℝ) : 0 ≤ smoothTailMajorant t :=
  Real.rpow_nonneg (by positivity) _

theorem smoothTailMajorant_integrable : Integrable smoothTailMajorant := by
  change Integrable (fun t : ℝ => (1+|t|)^(-(2:ℝ)))
  simpa only [smoothTailMajorant, Real.norm_eq_abs] using
    (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num))

def smoothTailIntegral : ℝ := ∫ t : ℝ, smoothTailMajorant t

theorem smoothTailIntegral_nonneg : 0 ≤ smoothTailIntegral :=
  integral_nonneg smoothTailMajorant_nonneg

theorem smooth_mellin_tail_pointwise (ρ : 𝓢(ℝ, ℂ)) (A : ℕ)
    {σ T C t : ℝ} (hT : 0 < T) (habs : T ≤ |t|)
    (hb : (1+|t|)^(A+2)*‖mellin (ρ:ℝ→ℂ) ((σ:ℂ)+t*Complex.I)‖ ≤ C) :
    ‖mellin (ρ:ℝ→ℂ) ((σ:ℂ)+t*Complex.I)‖ ≤ C/T^A*smoothTailMajorant t := by
  have hbase : 0 < 1+|t| := by positivity
  have hpow : T^A ≤ (1+|t|)^A := pow_le_pow_left₀ hT.le (by linarith) _
  have hp : ‖mellin (ρ:ℝ→ℂ) ((σ:ℂ)+t*Complex.I)‖*(T^A*(1+|t|)^2) ≤ C := by
    calc
      _ ≤ ‖mellin (ρ:ℝ→ℂ) ((σ:ℂ)+t*Complex.I)‖*((1+|t|)^A*(1+|t|)^2) := by gcongr
      _ = (1+|t|)^(A+2)*‖mellin (ρ:ℝ→ℂ) ((σ:ℂ)+t*Complex.I)‖ := by rw [pow_add]; ring
      _ ≤ C := hb
  have he : C/T^A*smoothTailMajorant t = C/(T^A*(1+|t|)^2) := by
    change C/T^A*((1+|t|)^(-(2:ℝ))) = _
    rw [Real.rpow_neg hbase.le, Real.rpow_two]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he]
  exact (le_div_iff₀ (by positivity)).mpr hp

theorem smooth_right_tail_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (ρ : 𝓢(ℝ, ℂ)) (A : ℕ)
    {X σ T B C : ℝ} (hX : 0 < X) (hT : 0 < T) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hlog : ∀ t : ℝ, ‖logDeriv χ.LFunction ((σ:ℂ)+t*Complex.I)‖ ≤ B)
    (hker : ∀ t : ℝ, (1+|t|)^(A+2)*‖mellin (ρ:ℝ→ℂ) ((σ:ℂ)+t*Complex.I)‖ ≤ C)
    (S : Set ℝ) (hS : MeasurableSet S) (hheight : ∀ t ∈ S, T ≤ |t|) :
    ‖∫ t in S, characterSmoothIntegrand ρ χ X ((σ:ℂ)+t*Complex.I)‖ ≤
      B*C*X^σ/T^A*smoothTailIntegral := by
  let D := B*C*X^σ/T^A
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hpoint (t : ℝ) (ht : t ∈ S) :
      ‖characterSmoothIntegrand ρ χ X ((σ:ℂ)+t*Complex.I)‖ ≤ D*smoothTailMajorant t := by
    have hm := smooth_mellin_tail_pointwise ρ A hT (hheight t ht) (hker t)
    rw [norm_characterSmoothIntegrand ρ χ hX]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    calc
      _ ≤ B*(C/T^A*smoothTailMajorant t)*X^σ := by gcongr; exact hlog t
      _ = _ := by dsimp [D]; ring
  have hnorm := norm_integral_le_of_norm_le
    ((smoothTailMajorant_integrable.const_mul D).integrableOn (s := S))
    (by filter_upwards [ae_restrict_mem hS] with t ht using hpoint t ht)
  calc
    _ ≤ ∫ t in S, D*smoothTailMajorant t := hnorm
    _ = D*(∫ t in S, smoothTailMajorant t) := integral_const_mul _ _
    _ ≤ D*smoothTailIntegral := mul_le_mul_of_nonneg_left
      (setIntegral_le_integral smoothTailMajorant_integrable
        (Eventually.of_forall smoothTailMajorant_nonneg)) hD
    _ = _ := rfl

end Ostmann.Dirichlet

end

end OAI
