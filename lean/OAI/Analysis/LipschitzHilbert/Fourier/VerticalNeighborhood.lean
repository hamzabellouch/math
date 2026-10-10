import OAI.Analysis.LipschitzHilbert.Estimates.IntervalPoincare

namespace OAI

/-! Dimension-independent vertical neighborhood control from the actual
function and its vertical derivative. The moment application only needs
this fixed interval Sobolev estimate. -/

noncomputable section
open MeasureTheory Set

namespace LipschitzHilbert

theorem interval_pointwise_square {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {a b : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc a b))) {x : ℝ} (hx : x ∈ Icc a b) :
    ‖f x‖^2 ≤ (2/(b-a)) * (∫ t in Icc a b, ‖f t‖^2) +
      2*(b-a)*(∫ t in Icc a b, ‖deriv f t‖^2) := by
  have hm : 0 < b-a := sub_pos.mpr hab
  have hcont : ContinuousOn f (Icc a b) :=
    fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hi : IntegrableOn (fun t => ‖f t‖^2) (Icc a b) volume :=
    (hcont.norm.pow 2).integrableOn_Icc
  let D := (b-a) * ∫ t in Icc a b, ‖deriv f t‖^2
  have hpoint (t : ℝ) (ht : t ∈ Icc a b) : ‖f x‖^2 ≤ 2*‖f t‖^2+2*D := by
    have hp := interval_pair_energy f hab.le hf hd hx ht
    have hn : ‖f x‖ ≤ ‖f t‖ + ‖f x-f t‖ := by
      simpa only [add_sub_cancel] using norm_add_le (f t) (f x-f t)
    have hs := pow_le_pow_left₀ (norm_nonneg (f x)) hn 2
    dsimp [D]
    nlinarith [sq_nonneg (‖f t‖-‖f x-f t‖)]
  have hint := integral_mono_ae
    (integrable_const (‖f x‖^2) : Integrable (fun _ : ℝ => ‖f x‖^2) (volume.restrict (Icc a b)))
    ((hi.const_mul 2).add (integrable_const (2*D)))
    ((ae_restrict_mem measurableSet_Icc).mono (fun t ht => hpoint t ht))
  have hmass : (volume.restrict (Icc a b)).real univ = b-a := by
    rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal hm.le]
  dsimp only [Pi.add_apply] at hint
  rw [integral_add (hi.const_mul 2) (integrable_const (2*D)), integral_const_mul,
    integral_const, integral_const, hmass] at hint
  simp only [smul_eq_mul] at hint
  have heq : (2/(b-a)) * (∫ t in Icc a b, ‖f t‖^2) * (b-a) =
      2 * ∫ t in Icc a b, ‖f t‖^2 := by field_simp [hm.ne']
  dsimp [D] at hint
  nlinarith

theorem vertical_neighborhood_square {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (y W v : ℝ) (hW : 0 < W) (hv : |v| ≤ W)
    (hf : ∀ t ∈ Icc (y-W) (y+W), DifferentiableAt ℝ f t)
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc (y-W) (y+W)))) :
    ‖f (y+v)‖^2 ≤ W⁻¹ * (∫ t in Icc (y-W) (y+W), ‖f t‖^2) +
      4*W*(∫ t in Icc (y-W) (y+W), ‖deriv f t‖^2) := by
  have hx : y+v ∈ Icc (y-W) (y+W) := by
    rcases abs_le.mp hv with ⟨hlo,hhi⟩
    constructor <;> linarith
  have h := interval_pointwise_square f (by linarith : y-W < y+W) hf hd hx
  convert h using 1
  have he : 2/(y+W-(y-W)) = W⁻¹ := by field_simp [hW.ne']; ring
  rw [he]
  ring

end LipschitzHilbert

end

end OAI
