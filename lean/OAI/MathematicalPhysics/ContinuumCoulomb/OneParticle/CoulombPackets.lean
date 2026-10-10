import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedCoulomb
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombGram

namespace OAI

/-! The global Coulomb pairing for the bounded integrable packets used in
the mode construction. Existing Gaussian-kernel positivity applies directly
once the elementary bounded-density estimate supplies joint integrability. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

structure CoulombPacket where
  value : Position → ℝ
  continuous : Continuous value
  integrable : Integrable value
  bound : ℝ
  bound_nonnegative : 0 ≤ bound
  bound_spec : ∀ x, ‖value x‖ ≤ bound

namespace CoulombPacket

instance : CoeFun CoulombPacket (fun _ => Position → ℝ) := ⟨CoulombPacket.value⟩

def add (f g : CoulombPacket) : CoulombPacket where
  value x := f x + g x
  continuous := f.continuous.add g.continuous
  integrable := f.integrable.add g.integrable
  bound := f.bound + g.bound
  bound_nonnegative := add_nonneg f.bound_nonnegative g.bound_nonnegative
  bound_spec x := (norm_add_le _ _).trans (add_le_add (f.bound_spec x) (g.bound_spec x))

def smul (t : ℝ) (f : CoulombPacket) : CoulombPacket where
  value x := t * f x
  continuous := continuous_const.mul f.continuous
  integrable := f.integrable.const_mul t
  bound := ‖t‖ * f.bound
  bound_nonnegative := mul_nonneg (norm_nonneg t) f.bound_nonnegative
  bound_spec x := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (f.bound_spec x) (norm_nonneg t)

theorem joint_integrable (f g : CoulombPacket) :
    Integrable (fun p : Position × Position =>
      f p.1 * g p.2 * Coulomb.coulombKernel (p.1 - p.2)) := by
  have hg (x : Position) := NeutralAtom.bounded_density_convolution
    NeutralAtom.measurable_coulombKernel NeutralAtom.coulombKernel_nonneg
    (NeutralAtom.coulombKernel_integrableOn_ball 1) (fun _ => NeutralAtom.coulombKernel_le_one)
    g.integrable.norm (fun _ => norm_nonneg _) g.bound_spec x
  let C := g.bound * NeutralAtom.kernelBallMass 1 + ∫ y, ‖g y‖
  have hm : Measurable (fun p : Position × Position =>
      f p.1 * g p.2 * Coulomb.coulombKernel (p.1 - p.2)) :=
    ((f.continuous.measurable.comp measurable_fst).mul
      (g.continuous.measurable.comp measurable_snd)).mul
      (Coulomb.coulombKernel_measurable.comp (measurable_fst.sub measurable_snd))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun x => by
      have hi := (hg x).1.const_mul ‖f x‖
      apply hi.mono' ((hm.comp ((measurable_const : Measurable (fun _ : Position => x)).prodMk
        measurable_id)).aestronglyMeasurable)
      exact Filter.Eventually.of_forall (fun y => by
        dsimp only [Function.comp_def, Prod.fst, Prod.snd, id_eq]
        rw [norm_mul, norm_mul, Real.norm_of_nonneg (Coulomb.coulombKernel_nonneg _)]
        change ‖f x‖ * ‖g y‖ * ‖x - y‖⁻¹ ≤ ‖f x‖ * (‖x - y‖⁻¹ * ‖g y‖)
        ring_nf
        exact le_rfl))
  · apply (f.integrable.norm.const_mul C).mono'
      hm.aestronglyMeasurable.norm.integral_prod_right'
    exact Filter.Eventually.of_forall (fun x => by
      have he : (∫ y, ‖f x * g y * Coulomb.coulombKernel (x - y)‖) =
          ‖f x‖ * ∫ y, NeutralAtom.coulombKernel (x - y) * ‖g y‖ := by
        have hp (y : Position) : ‖f x * g y * Coulomb.coulombKernel (x - y)‖ =
            ‖f x‖ * (NeutralAtom.coulombKernel (x - y) * ‖g y‖) := by
          rw [norm_mul, norm_mul, Real.norm_of_nonneg (Coulomb.coulombKernel_nonneg _)]
          change ‖f x‖ * ‖g y‖ * ‖x - y‖⁻¹ = ‖f x‖ * (‖x - y‖⁻¹ * ‖g y‖)
          ring
        simp_rw [hp, integral_const_mul]
      rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)), he]
      calc
        _ ≤ ‖f x‖ * C := mul_le_mul_of_nonneg_left (hg x).2 (norm_nonneg (f x))
        _ = _ := mul_comm _ _)

def pair (f g : CoulombPacket) : ℝ :=
  ∫ p : Position × Position, f p.1 * g p.2 * Coulomb.coulombKernel (p.1 - p.2)

theorem pair_nonnegative (f : CoulombPacket) : 0 ≤ pair f f :=
  Coulomb.coulomb_form_nonneg_of_pair f.integrable f.continuous.measurable (joint_integrable f f)

theorem pair_symmetric (f g : CoulombPacket) : pair f g = pair g f := by
  unfold pair
  rw [Measure.volume_eq_prod, integral_prod _ (joint_integrable f g),
    integral_prod _ (joint_integrable g f), integral_integral_swap (joint_integrable f g)]
  apply integral_congr_ae
  filter_upwards [] with y
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Coulomb.coulombKernel, norm_sub_rev x y]
  ring

theorem pair_add_left (f g h : CoulombPacket) : pair (add f g) h = pair f h + pair g h := by
  unfold pair
  change (∫ p : Position × Position, (f p.1 + g p.1) * h p.2 * Coulomb.coulombKernel (p.1 - p.2)) = _
  simp_rw [add_mul]
  exact integral_add (joint_integrable f h) (joint_integrable g h)

theorem pair_smul_left (t : ℝ) (f g : CoulombPacket) : pair (smul t f) g = t * pair f g := by
  unfold pair
  change (∫ p : Position × Position, (t * f p.1) * g p.2 * Coulomb.coulombKernel (p.1 - p.2)) = _
  simp_rw [mul_assoc]
  exact integral_const_mul t _

theorem pair_add_right (f g h : CoulombPacket) : pair f (add g h) = pair f g + pair f h := by
  rw [pair_symmetric, pair_add_left, pair_symmetric g f, pair_symmetric h f]

theorem pair_smul_right (t : ℝ) (f g : CoulombPacket) : pair f (smul t g) = t * pair f g := by
  rw [pair_symmetric, pair_smul_left, pair_symmetric g f]

theorem pair_cauchy (f g : CoulombPacket) : pair f g ^ 2 ≤ pair f f * pair g g := by
  have h (t : ℝ) : 0 ≤ pair g g * (t * t) + (2 * pair f g) * t + pair f f := by
    have hn := pair_nonnegative (add f (smul t g))
    rw [pair_add_left, pair_add_right, pair_add_right, pair_smul_left,
      pair_smul_right, pair_smul_right, pair_symmetric g f, pair_smul_left] at hn
    nlinarith only [hn]
  have hd := discrim_le_zero h
  dsimp only [discrim] at hd
  nlinarith only [hd]

end CoulombPacket
end ContinuumCoulomb

end

end OAI
