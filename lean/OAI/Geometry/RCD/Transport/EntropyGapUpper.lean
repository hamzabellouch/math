import OAI.Geometry.RCD.Transport.ShiftedEntropyBounds

namespace OAI

/-! # Affine entropy cancellation under mass and linear-pairing conservation -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem entropy_gap_upper (f u w v : Lp ℝ 2 μ) {ε : ℝ} (hε : 0<ε) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, f x∈Icc 0 (A:ℝ)) (hu : ∀ᵐ x ∂μ, u x∈Icc 0 (A:ℝ))
    (hv0 : 0≤v) (hwi : Integrable w μ) (hvi : Integrable v μ)
    (hmass : (∫ x, v x ∂μ) = ∫ x, w x ∂μ)
    (hpair : inner ℝ v f = inner ℝ w u) :
    (∫ x, v x*shiftedEntropy ε (f x) ∂μ)-(∫ x, w x*shiftedEntropy ε (u x) ∂μ) ≤
      ∫ x, w x*(ε+u x)*(Real.log (ε+A)-Real.log (ε+u x)) ∂μ := by
  let L := Real.log (ε+A)-Real.log ε
  have hiu := shiftedEntropy_weighted_integrable μ hε A u w hu
  have hif := shiftedEntropy_weighted_integrable μ hε A f v hf
  have hwu := (Lp.memLp w).integrable_mul (Lp.memLp u)
  have hvf := (Lp.memLp v).integrable_mul (Lp.memLp f)
  change Integrable (fun x => w x*u x) μ at hwu
  change Integrable (fun x => v x*f x) μ at hvf
  have hupper : (∫ x, v x*shiftedEntropy ε (f x) ∂μ) ≤
      ε*L*(∫ x, v x ∂μ)+(L-1)*(∫ x, v x*f x ∂μ) := by
    have hm := integral_mono_ae hif ((hvi.const_mul (ε*L)).add (hvf.const_mul (L-1))) (by
      filter_upwards [hf,(Lp.coeFn_nonneg _).mpr hv0] with x hx hy
      have hh := mul_le_mul_of_nonneg_left (shiftedEntropy_le_affine hε hx) hy
      dsimp only [L] at *
      simp only [Pi.add_apply]
      nlinarith only [hh])
    have he := integral_add (hvi.const_mul (ε*L)) (hvf.const_mul (L-1))
    simp only [Pi.add_apply] at he hm
    simpa only [he,integral_const_mul] using hm
  have hp : (∫ x, v x*f x ∂μ) = ∫ x, w x*u x ∂μ := by
    simpa only [L2.inner_def,Real.inner_apply] using hpair
  have hr : (∫ x, w x*(ε+u x)*(Real.log (ε+A)-Real.log (ε+u x)) ∂μ) =
      ε*L*(∫ x, w x ∂μ)+(L-1)*(∫ x, w x*u x ∂μ)-
      (∫ x, w x*shiftedEntropy ε (u x) ∂μ) := by
    calc
      _ = ∫ x, ε*L*w x+(L-1)*(w x*u x)-w x*shiftedEntropy ε (u x) ∂μ := by
        apply integral_congr_ae
        exact .of_forall fun x => by dsimp only [L,shiftedEntropy]; ring
      _ = _ := by
        have es := integral_sub ((hwi.const_mul (ε*L)).add (hwu.const_mul (L-1))) hiu
        have ea := integral_add (hwi.const_mul (ε*L)) (hwu.const_mul (L-1))
        simp only [Pi.add_apply] at es ea
        rw [es,ea,integral_const_mul,integral_const_mul]
  rw [hmass,hp] at hupper
  rw [hr]
  linarith only [hupper]

end RegularPointCoordinates

end

end OAI
