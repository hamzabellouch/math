import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneBarrier
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarInput

namespace OAI

/-! Bounded comparison on the whole plane, proved with an explicit
quadratic barrier. No periodicity, decay, integrability or compact support
of the scalar is assumed in this argument. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set Filter
open scoped Topology ContDiff

theorem scalar_maximum_principle_bounded {w d : ℝ → Plane → ℝ}
    {a : ℝ → Plane → Plane} {T ν A B : ℝ}
    (_hT : 0 ≤ T) (hν : 0 ≤ ν) (hA : 0 ≤ A)
    (ha : ∀ t ∈ Icc 0 T, ∀ x, ‖a t x‖ ≤ A)
    (hb : ∀ t ∈ Icc 0 T, ∀ x, w t x ≤ B)
    (hc : ContinuousOn (Function.uncurry w) (Icc 0 T ×ˢ univ))
    (hs : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (w t))
    (hd : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivWithinAt (fun s => w s x) (d t x) (Icc 0 T) t)
    (he : ∀ t ∈ Ioc 0 T, ∀ x, d t x ≤ scalarGenerator ν (a t) (w t) x)
    (h₀ : ∀ x, w 0 x ≤ 0) : ∀ t ∈ Icc 0 T, ∀ x, w t x ≤ 0 := by
  intro t ht x
  by_contra! hpos
  let C := 4 * ν + 2 * A ^ 2 + 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let θ : ℝ → ℝ := fun s => Real.exp (C * s)
  have hθ (s : ℝ) : 0 < θ s := Real.exp_pos _
  have hθ₁ : ∀ s ∈ Icc 0 T, 1 ≤ θ s := by
    intro s hs
    exact Real.one_le_exp_iff.mpr (mul_nonneg hC hs.1)
  have hφ : 0 < planeBarrierSquare x := lt_of_lt_of_le (by norm_num)
    (planeBarrierSquare_one_le x)
  let ε := w t x / (2 * θ t * planeBarrierSquare x)
  have hε : 0 < ε := div_pos hpos (by positivity)
  let v : ℝ → Plane → ℝ :=
    fun s y => w s y - ε * θ s * planeBarrierSquare y
  have hvc : ContinuousOn (Function.uncurry v) (Icc 0 T ×ˢ univ) :=
    hc.sub (((continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_fst))).mul
      (planeBarrierSquare_smooth.continuous.comp continuous_snd)).continuousOn)
  obtain ⟨K, hK, houtside⟩ := quadratic_barrier_positive_compact hε hb θ hθ₁
  have hvtx : 0 < v t x := by
    have hm : ε * (2 * θ t * planeBarrierSquare x) = w t x := by
      dsimp [ε]
      exact div_mul_cancel₀ _ (by positivity)
    dsimp only [v]
    nlinarith
  obtain ⟨s, hsK, y, hvsy, hmax⟩ := positive_cylinder_max hvc hK houtside ht hvtx
  have hspos : 0 < s := by
    by_contra hn
    have hz : s = 0 := le_antisymm (le_of_not_gt hn) hsK.1
    subst s
    have h := h₀ y
    have hprod : 0 < ε * θ 0 * planeBarrierSquare y :=
      mul_pos (mul_pos hε (hθ 0)) (lt_of_lt_of_le (by norm_num)
        (planeBarrierSquare_one_le y))
    dsimp only [v] at hvsy
    linarith
  have hst : s ∈ Ioc (0 : ℝ) T := ⟨hspos, hsK.2⟩
  have htime : 0 ≤ d s y - ε * C * θ s * planeBarrierSquare y := by
    apply timeDerivative_nonneg_at_max hspos
      (fun r hr => hmax r ⟨hr.1, hr.2.trans hsK.2⟩ y)
    have hlin : HasDerivAt (fun r => ε * θ r * planeBarrierSquare y)
        (ε * C * θ s * planeBarrierSquare y) s := by
      simpa only [θ, id_eq, mul_one, one_mul, mul_assoc, mul_comm, mul_left_comm] using
        ((((hasDerivAt_id s).const_mul C).exp.const_mul ε).mul_const (planeBarrierSquare y))
    exact ((hd s hst y).sub hlin.hasDerivWithinAt).mono
      (Icc_subset_Icc le_rfl hsK.2)
  have hspace : IsLocalMax (v s) y :=
    Filter.Eventually.of_forall (fun z => hmax s hsK z)
  have hφs : ContDiff ℝ ∞ (fun z => (ε * θ s) * planeBarrierSquare z) :=
    contDiff_const.mul planeBarrierSquare_smooth
  have hvs : ContDiff ℝ ∞ (v s) :=
    (hs s hsK).sub hφs
  have hgen := scalarGenerator_nonpos hvs hspace hν (a s)
  change scalarGenerator ν (a s)
    (fun z => w s z - (ε * θ s) * planeBarrierSquare z) y ≤ 0 at hgen
  rw [scalarGenerator_sub (hs s hsK) hφs,
    scalarGenerator_const_mul planeBarrierSquare_smooth] at hgen
  have hbound := planeBarrierSquare_generator_bound hν hA (a s) (ha s hsK) y
  have hεθ : 0 < ε * θ s := mul_pos hε (hθ s)
  have hmargin := mul_le_mul_of_nonneg_left hbound hεθ.le
  have hstrict : 0 < ε * θ s * planeBarrierSquare y :=
    mul_pos hεθ (lt_of_lt_of_le (by norm_num) (planeBarrierSquare_one_le y))
  have hineq := he s hst y
  dsimp only [C] at htime
  nlinarith

end ForcedComputation.VelocityDetector

end

end OAI
