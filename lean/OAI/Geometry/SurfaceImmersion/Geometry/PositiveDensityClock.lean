import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicPrimitive
import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicCalculus

namespace OAI

/-! The angular clock associated to a positive periodic density of mass one. -/
noncomputable section
open Filter Set
open scoped ContDiff Topology

namespace ClosedSurfaceR4.PositiveDensity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]
  {ρ : B × ℝ → ℝ} {U : Set B}

def clock (ρ : B × ℝ → ℝ) (b : B) (t : ℝ) : ℝ := ∫ s in 0..t, ρ (b, s)

lemma clock_smoothOn [FiniteDimensional ℝ B] (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun z : B × ℝ => clock ρ z.1 z.2) (U ×ˢ univ) := by
  apply (hU.prod isOpen_univ).contDiffOn_iff.mpr
  intro z hz
  obtain ⟨G, hG, he⟩ := SmoothParameterIntegral.exists_smooth_extension_near hU hρ hz.1
  apply (PeriodicPrimitive.contDiff_rawPrimitive_joint hG).contDiffAt.congr_of_eventuallyEq
  have he' := (continuous_fst.continuousAt : Tendsto Prod.fst (𝓝 z) (𝓝 z.1)).eventually he
  filter_upwards [he'] with w hw
  change (∫ s in 0..w.2, ρ (w.1, s)) = ∫ s in 0..w.2, G (w.1, s)
  congr 1
  funext s
  exact (hw s).symm

lemma hasDerivAt_clock (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    {b : B} (hb : b ∈ U) (t : ℝ) : HasDerivAt (clock ρ b) (ρ (b, t)) t :=
  ((LocalPeriodicCalculus.smooth_slice hU hρ hb).continuous.integral_hasStrictDerivAt 0 t).hasDerivAt

lemma clock_strictMono (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t)) {b : B} (hb : b ∈ U) :
    StrictMono (clock ρ b) := by
  apply strictMono_of_deriv_pos
  intro t
  rw [(hasDerivAt_clock hU hρ hb t).deriv]
  exact hpos b hb t

lemma clock_continuous (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    {b : B} (hb : b ∈ U) : Continuous (clock ρ b) :=
  (show Differentiable ℝ (clock ρ b) from
    fun t => (hasDerivAt_clock hU hρ hb t).differentiableAt).continuous

lemma clock_period (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1)
    {b : B} (hb : b ∈ U) (t : ℝ) : clock ρ b (t + 1) = clock ρ b t + 1 := by
  rw [clock, (hper b hb).intervalIntegral_add_eq_add 0 t
    (fun x y => (LocalPeriodicCalculus.smooth_slice hU hρ hb).continuous.intervalIntegrable x y)]
  simp only [zero_add, hmass b hb, clock]

omit [NormedAddCommGroup B] [NormedSpace ℝ B] in
@[simp] lemma clock_zero (ρ : B × ℝ → ℝ) (b : B) : clock ρ b 0 = 0 := by simp [clock]

lemma clock_surjective (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1)
    {b : B} (hb : b ∈ U) : Function.Surjective (clock ρ b) := by
  exact (clock_continuous hU hρ hb).surjective
    ((hper b hb).tendsto_atTop_intervalIntegral_of_pos (by rw [hmass b hb]; norm_num) zero_lt_one)
    ((hper b hb).tendsto_atBot_intervalIntegral_of_pos (by rw [hmass b hb]; norm_num) zero_lt_one)

end ClosedSurfaceR4.PositiveDensity

end

end OAI
