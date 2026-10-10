import OAI.MathematicalPhysics.Boltzmann.Jets.TorusAnnularIntegrability

namespace OAI

/-! # A common square-integrable envelope for all capped velocity moments -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.AnnularEnvelope

theorem squareEnvelope_measurable (s₀ η : ℝ) : Measurable (squareEnvelope s₀ η) :=
  Measurable.tsum (fun j => (term_measurable s₀ η j).pow_const 2)

def commonMoment (s₀ η A B : ℝ) (u : ℝ × Transverse) : ℝ :=
  A+B*Real.sqrt (squareEnvelope s₀ η u)

theorem commonMoment_measurable (s₀ η A B : ℝ) : Measurable (commonMoment s₀ η A B) :=
  measurable_const.add (((squareEnvelope_measurable s₀ η).sqrt).const_mul B)

theorem commonMoment_nonneg {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (s₀ η : ℝ) (u : ℝ × Transverse) : 0 ≤ commonMoment s₀ η A B u :=
  add_nonneg hA (mul_nonneg hB (Real.sqrt_nonneg _))

theorem finiteEnvelope_nonneg {s₀ t : ℝ} (hs₀ : 0 < s₀) (ht : 0 ≤ t)
    (η : ℝ) (s : Finset ℕ) (y : Transverse) : 0 ≤ finiteEnvelope s₀ η s t y := by
  apply Finset.sum_nonneg
  intro j _
  apply indicator_nonneg
  intro _ _
  exact div_nonneg zero_le_one (add_nonneg ht (DatumBounds.scale_pos hs₀ _).le)

theorem finiteEnvelope_le_sqrt {s₀ η t : ℝ} (hs₀ : 0 < s₀) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (s : Finset ℕ) (y : Transverse) :
    finiteEnvelope s₀ η s t y ≤ Real.sqrt (squareEnvelope s₀ η (t,y)) := by
  apply (sq_le_sq₀ (finiteEnvelope_nonneg hs₀ ht η s y) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (squareEnvelope_nonneg s₀ η (t,y))]
  exact finiteEnvelope_square_le hs₀.le hη s (t,y)

theorem affine_le_commonMoment {s₀ η t B : ℝ} (hs₀ : 0 < s₀) (hη : 0 ≤ η)
    (ht : 0 ≤ t) (hB : 0 ≤ B) (A : ℝ) (s : Finset ℕ) (y : Transverse) :
    A+B*finiteEnvelope s₀ η s t y ≤ commonMoment s₀ η A B (t,y) :=
  add_le_add le_rfl (mul_le_mul_of_nonneg_left (finiteEnvelope_le_sqrt hs₀ hη ht s y) hB)

theorem commonMoment_square_le (s₀ η A B : ℝ) (u : ℝ × Transverse) :
    (commonMoment s₀ η A B u)^2 ≤ 2*A^2+2*B^2*squareEnvelope s₀ η u := by
  have hs := Real.sq_sqrt (squareEnvelope_nonneg s₀ η u)
  have hp := sq_nonneg (A-B*Real.sqrt (squareEnvelope s₀ η u))
  unfold commonMoment
  nlinarith

theorem torus_common_square_integrable {s₀ η T : ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hT : 0 ≤ T) (A B : ℝ) :
    Integrable (fun u : ℝ × Position => (commonMoment s₀ η A B (torusChart u))^2)
      (timePositionVolume T) := by
  have hG := torus_lift_integrable (momentMajorant_integrable hs₀ hη hηmax hT A B 2)
  apply hG.mono' (((commonMoment_measurable s₀ η A B).comp torusChart_measurable).pow_const 2).aestronglyMeasurable
  filter_upwards [] with u
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have he := commonMoment_square_le s₀ η A B (torusChart u)
  simpa only [Function.comp_apply,momentMajorant,indicator_of_mem (torusChart_mem_cell u),mul_one] using he

end BoltzmannNonuniqueness.AnnularEnvelope

end

end OAI
