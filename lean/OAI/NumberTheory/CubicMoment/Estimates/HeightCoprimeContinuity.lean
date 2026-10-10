import OAI.NumberTheory.CubicMoment.Estimates.MellinEnvelopeBound
import OAI.NumberTheory.CubicMoment.Estimates.HeightAveraging

namespace OAI

/-! Domination and continuity for the genuine divisor-restricted mass
as its independent arithmetic height varies. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma coprimeMellinMass_continuous_coefficients (S H U : Finset Eisenstein)
    (v w : ℝ → Eisenstein → ℂ) (hv : ∀ a, Continuous (fun t => v t a))
    (hw : ∀ a, Continuous (fun t => w t a)) (y : Eisenstein → ℝ) (s : ℝ) :
    Continuous (fun t => coprimeMellinMass S H U (v t) (w t) y s) := by
  unfold coprimeMellinMass
  apply continuous_finsetSum
  intro d hd
  apply Continuous.div_const
  apply Continuous.add
  · apply continuous_finsetSum
    intro h hh
    apply Continuous.pow
    apply Continuous.norm
    apply continuous_finsetSum
    intro a ha
    exact ((hv a).mul continuous_const).mul continuous_const
  · apply continuous_finsetSum
    intro h hh
    apply Continuous.pow
    apply Continuous.norm
    apply continuous_finsetSum
    intro a ha
    exact ((hw a).mul continuous_const).mul continuous_const

lemma normCoprimeRadialForm_continuous_coefficients (S H : Finset Eisenstein)
    (v w : ℝ → Eisenstein → ℂ) (hv : ∀ a, Continuous (fun t => v t a))
    (hw : ∀ a, Continuous (fun t => w t a)) (phase : Eisenstein → ℂ)
    (x y : Eisenstein → ℝ) (W : ℝ → ℂ) (ρ : ℝ) :
    Continuous (fun t => normCoprimeRadialForm S H (v t) (w t) phase x y W ρ) := by
  unfold normCoprimeRadialForm
  apply continuous_finsetSum
  intro h hh
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro a ha
  apply continuous_finsetSum
  intro b hb
  split_ifs
  · exact (((hv a).mul continuous_const).mul ((hw b).mul continuous_const).star).mul continuous_const
  · exact continuous_const

def twistedCoprimeMellinMass (S H U : Finset Eisenstein)
    (β : Eisenstein → ℂ) (y : Eisenstein → ℝ) (u s : ℝ) : ℝ :=
  coprimeMellinMass S H U (fun a => star (β a*mellinPhase u (norm a)))
    (fun a => star (β a*mellinPhase u (norm a))) y s

lemma twistedCoprimeMellinMass_continuous_height (S H U : Finset Eisenstein)
    (β : Eisenstein → ℂ) (y : Eisenstein → ℝ) (s : ℝ) :
    Continuous (fun u => twistedCoprimeMellinMass S H U β y u s) := by
  apply coprimeMellinMass_continuous_coefficients
  all_goals intro a; unfold mellinPhase; fun_prop

lemma twistedCoprimeMellinMass_le (S H U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) (β : Eisenstein → ℂ) (y : Eisenstein → ℝ) (u s : ℝ) :
    twistedCoprimeMellinMass S H U β y u s ≤ coprimeMellinEnvelope S H U β β := by
  have h := coprimeMellinMass_le_envelope S H U hS
    (fun a => star (β a*mellinPhase u (norm a)))
    (fun a => star (β a*mellinPhase u (norm a))) y s
  simpa only [twistedCoprimeMellinMass,coprimeMellinEnvelope,norm_star,norm_mul,mellinPhase_norm,mul_one] using h

lemma continuous_integral_twistedCoprimeMellinMass (S H U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) (β : Eisenstein → ℂ) (y : Eisenstein → ℝ)
    {f : ℝ → ℝ} (hf : Continuous f) (hfi : Integrable f) :
    Continuous (fun u => ∫ s : ℝ, f s*twistedCoprimeMellinMass S H U β y u s) := by
  apply continuous_of_dominated (bound := fun s => ‖f s‖*coprimeMellinEnvelope S H U β β)
  · intro u
    exact (hf.mul (coprimeMellinMass_continuous S H U _ _ y)).aestronglyMeasurable
  · intro u
    filter_upwards with s
    have hn : 0 ≤ twistedCoprimeMellinMass S H U β y u s :=
      coprimeMellinMass_nonneg S H U _ _ y s
    rw [norm_mul,Real.norm_eq_abs (twistedCoprimeMellinMass S H U β y u s),abs_of_nonneg hn]
    exact mul_le_mul_of_nonneg_left (twistedCoprimeMellinMass_le S H U hS β y u s)
      (_root_.norm_nonneg _)
  · exact hfi.norm.mul_const _
  · filter_upwards with s
    exact continuous_const.mul (twistedCoprimeMellinMass_continuous_height S H U β y s)

end CubicFirstMoment

end

end OAI
