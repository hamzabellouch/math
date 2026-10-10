import OAI.MathematicalPhysics.Boltzmann.Branching.L2PairingBound
import OAI.MathematicalPhysics.Boltzmann.Branching.ReferenceCollisionGeometry
import OAI.MathematicalPhysics.Boltzmann.Branching.RestrictedCone
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityAverageDifference
import OAI.MathematicalPhysics.Boltzmann.Jets.OriginMeshStep

namespace OAI

section

/-! # A positive first-collision angular cap for bounded incoming velocities -/

noncomputable section

open MeasureTheory Set NormedSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem outgoing_bounded_endpoint_cap {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (v e b : V) (he : ‖e‖ ≤ 2) (hv : ‖v‖ ≤ R) (n : Sphere)
    (hn : dist (child v e n.1) b ≤ δ/2) :
    sphereCapMass (δ/(R+2)) ≤ (outgoing (v,e)).real (Metric.ball b δ) := by
  have hRp : 0 < R+2 := by linarith
  have hsub : Metric.ball n (δ/(R+2)) ⊆
      (fun m : Sphere => child v e m.1) ⁻¹' Metric.ball b δ := by
    intro m hm
    have hd : dist (m : V) (n : V) < δ/(R+2) := hm
    have hr : ‖v-e‖ ≤ R+2 := (norm_sub_le v e).trans (add_le_add hv he)
    have ht := dist_triangle (child v e m.1) (child v e n.1) b
    rw [child_angular_distance] at ht
    have hp := mul_le_mul_of_nonneg_right hr (dist_nonneg : 0 ≤ dist (m : V) (n : V))
    have hh := (lt_div_iff₀ hRp).mp hd
    change dist (child v e m.1) b < δ
    nlinarith
  have hh := (sphere_cap_lower (div_pos hδ hRp) n).trans (measureReal_mono hsub)
  rw [Measure.real,outgoing_apply,Measure.map_apply (by unfold child; fun_prop) measurableSet_ball]
  exact hh

theorem outgoing_near_partner_positive {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (v e b : V) (he : ‖e‖ ≤ 2) (hv : ‖v‖ ≤ R) (hne : v ≠ e)
    (heb : dist e b ≤ δ/2) :
    0 < (outgoing (v,e)).real (Metric.ball b δ) := by
  let n : Sphere := ⟨-normalize (v-e),mem_sphere_zero_iff_norm.mpr
    (by rw [norm_neg,norm_normalize (sub_ne_zero.mpr hne)])⟩
  have hn : child v e n.1 = e := (child_normalized_endpoints v e).2
  exact (sphereCapMass_pos (div_pos hδ (by linarith))).trans_le
    (outgoing_bounded_endpoint_cap hR hδ v e b he hv n (by rw [hn]; exact heb))

theorem exists_separated_beam (v : V) :
    1 ≤ ‖v-beamAxis‖ ∨ 1 ≤ ‖v-(-beamAxis)‖ := by
  have h := two_beam_distance_lower v beamAxis axis_norms.2.2
  rw [sub_neg_eq_add]
  by_cases hp : 1 ≤ ‖v-beamAxis‖
  · exact Or.inl hp
  · exact Or.inr (by linarith)

theorem nearby_partner_distance {v e b : V} {α : ℝ}
    (hvb : 1 ≤ ‖v-b‖) (heb : ‖e-b‖ ≤ α) : 1-α ≤ ‖v-e‖ := by
  have ht := norm_sub_le (v-e) (b-e)
  rw [sub_sub_sub_cancel_right,norm_sub_rev b e] at ht
  linarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Bounded sources give bounded L2 velocity averages -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published

theorem dampedLineResolvent_norm_le {f : FourierSpace → ℂ} {B : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ B) (w x : FourierSpace) : ‖dampedLineResolvent f w x‖ ≤ B := by
  have h := norm_integral_le_of_norm_le ((integrableOn_exp_neg_Ioi 0).mul_const B)
    (ae_of_all _ (fun s : ℝ => show ‖Real.exp (-s) • f (x-s • w)‖ ≤ Real.exp (-s)*B by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hf _) (Real.exp_pos _).le))
  simpa only [dampedLineResolvent,integral_mul_const,integral_exp_neg_Ioi_zero,one_mul] using h

theorem velocityLineResolvent_support {r : Velocity × FourierSpace → ℂ} {R : ℝ}
    (hs : ∀ p, R < ‖p.1‖ → r p = 0) (v : Velocity) (x : FourierSpace) (hv : R < ‖v‖) :
    velocityLineResolvent r (v,x) = 0 := by
  apply integral_eq_zero_of_ae
  exact ae_of_all _ (fun s => by simp only [hs (v,_) hv,smul_zero,Pi.zero_apply])

theorem velocityLineAverage_norm_le {r : Velocity × FourierSpace → ℂ} {R B : ℝ}
    (hb : ∀ p, ‖r p‖ ≤ B) (hs : ∀ p, R < ‖p.1‖ → r p = 0) (x : FourierSpace) :
    ‖velocityLineAverage r x‖ ≤ volume.real (Metric.closedBall (0 : Velocity) R)*B := by
  have he : velocityLineAverage r x =
      ∫ v in Metric.closedBall (0 : Velocity) R, velocityLineResolvent r (v,x) := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    exact velocityLineResolvent_support hs v x
      (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hv)
  rw [he]
  have hfinite : volume (Metric.closedBall (0 : Velocity) R) < ⊤ :=
    (isCompact_closedBall _ _).measure_lt_top
  have h := norm_setIntegral_le_of_norm_le_const
    (f := fun v => velocityLineResolvent r (v,x)) hfinite
    (fun v _ => dampedLineResolvent_norm_le (fun y => hb (v,y)) (characteristicDirection v) x)
  simpa only [mul_comm] using h

theorem integrable_bounded_memLp_two {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℂ} (hf : Integrable f μ) {B : ℝ} (hb : ∀ x, ‖f x‖ ≤ B) : MemLp f 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  apply (hf.norm.const_mul B).mono' (hf.aestronglyMeasurable.norm.pow 2)
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),pow_two]
    exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _))

theorem velocityLineAverage_memLp_two {r : Velocity × FourierSpace → ℂ}
    (hr : Integrable r) {R B : ℝ}
    (hb : ∀ p, ‖r p‖ ≤ B) (hs : ∀ p, R < ‖p.1‖ → r p = 0) :
    MemLp (velocityLineAverage r) 2 volume :=
  integrable_bounded_memLp_two (velocityLineAverage_integrable hr)
    (velocityLineAverage_norm_le hb hs)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Actual spatial and velocity masks for the finite mesh representation -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet
open BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum

def boundedMeshWeight (s₀ η δ M a T : ℝ) (r : ℕ → ℝ) (N n : ℕ)
    {J : Finset ℤ} (S : Set Velocity) (j : MeshLabel J) : Published.KineticPhase → ℝ≥0∞ :=
  (meshLabelRegion s₀ η δ M r N n j ∩ {z | z.1.1 ∈ Icc a T ∧ z.2 ∈ S}).indicator (fun _ => 1)

theorem boundedMeshWeight_measurable (s₀ η δ M a T : ℝ) (r : ℕ → ℝ) (N n : ℕ)
    {J : Finset ℤ} {S : Set Velocity} (hS : MeasurableSet S) (j : MeshLabel J) :
    Measurable (boundedMeshWeight s₀ η δ M a T r N n S j) := by
  apply measurable_const.indicator
  exact (meshLabelRegion_measurable s₀ η δ M r N n j).inter
    ((measurableSet_Icc.preimage (by fun_prop)).inter (hS.preimage measurable_snd))

theorem boundedMeshWeight_le_one (s₀ η δ M a T : ℝ) (r : ℕ → ℝ) (N n : ℕ)
    {J : Finset ℤ} (S : Set Velocity) (j : MeshLabel J) (z : Published.KineticPhase) :
    boundedMeshWeight s₀ η δ M a T r N n S j z ≤ 1 := by
  classical
  by_cases h : z ∈ meshLabelRegion s₀ η δ M r N n j ∩ {z | z.1.1 ∈ Icc a T ∧ z.2 ∈ S}
  · simp only [boundedMeshWeight,indicator_of_mem h,le_refl]
  · simp only [boundedMeshWeight,indicator_of_notMem h]
    exact zero_le

theorem boundedMeshWeight_support {s₀ η δ M a T V b : ℝ} {r : ℕ → ℝ} {N n : ℕ}
    {J : Finset ℤ} {S : Set Velocity}
    (hS : ∀ v, v ∈ S → ‖v‖ ≤ V ∧ b ≤ ‖VelocityWeight.transverse v‖)
    (j : MeshLabel J) (z : Published.KineticPhase)
    (hz : boundedMeshWeight s₀ η δ M a T r N n S j z ≠ 0) :
    z.1.1 ∈ Icc a T ∧ ‖z.2‖ ≤ V ∧ b ≤ ‖VelocityWeight.transverse z.2‖ := by
  have hm : z ∈ meshLabelRegion s₀ η δ M r N n j ∩ {z | z.1.1 ∈ Icc a T ∧ z.2 ∈ S} := by
    by_contra h
    exact hz (indicator_of_notMem h _)
  exact ⟨hm.2.1,hS z.2 hm.2.2⟩

theorem boundedMeshWeight_mul {s₀ η δ M a T : ℝ} {r : ℕ → ℝ} {N n : ℕ}
    {J : Finset ℤ} (S : Set Velocity) (j : MeshLabel J)
    (f : Published.KineticPhase → ℝ≥0∞) {z : Published.KineticPhase}
    (hz : z.1.1 ∈ Icc a T) :
    boundedMeshWeight s₀ η δ M a T r N n S j z*f z =
      (meshLabelRegion s₀ η δ M r N n j).indicator ({y | y.2 ∈ S}.indicator f) z := by
  classical
  by_cases hR : z ∈ meshLabelRegion s₀ η δ M r N n j
  · by_cases hS : z.2 ∈ S
    · have hm : z ∈ meshLabelRegion s₀ η δ M r N n j ∩
        {z | z.1.1 ∈ Icc a T ∧ z.2 ∈ S} := ⟨hR,hz,hS⟩
      simp only [boundedMeshWeight,indicator_of_mem hm,one_mul,indicator_of_mem hR,
        indicator_of_mem (show z ∈ {y : Published.KineticPhase | y.2 ∈ S} from hS)]
    · simp [boundedMeshWeight,hR,hS]
  · simp [boundedMeshWeight,hR]

end BoltzmannNonuniqueness.JetCopyDatum

namespace BoltzmannNonuniqueness.PositiveIteration

theorem step_restrict_eq_indicator (a : ℝ) (K : ProbabilityTheory.Kernel Published.KineticPhase Velocity)
    {S : Set Velocity} (hS : MeasurableSet S) (f : Published.KineticPhase → ℝ≥0∞) :
    step a (K.restrict hS) f = step a K ({y | y.2 ∈ S}.indicator f) := by
  funext z
  apply lintegral_congr
  intro s
  change (∫⁻ v in S, f ((flight z s).1,v) ∂K (flight z s)) = _
  rw [← lintegral_indicator hS]
  rfl

end BoltzmannNonuniqueness.PositiveIteration

end

end

section

/-! # Uniform L2 energy bounds for bounded-source velocity averages -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.Published

theorem bounded_integrable_square_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℂ} (hi : Integrable f μ) {B : ℝ} (hb : ∀ x, ‖f x‖ ≤ B) :
    (∫ x, ‖f x‖^2 ∂μ) ≤ B * ∫ x, ‖f x‖ ∂μ := by
  have hm := integrable_bounded_memLp_two hi hb
  calc
    _ ≤ ∫ x, B*‖f x‖ ∂μ := by
      apply integral_mono ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm)
        (hi.norm.const_mul B)
      intro x
      dsimp only
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

theorem bounded_average_energy {r : Velocity × FourierSpace → ℂ}
    (hr : Integrable r) {R B C : ℝ} (hB : 0 ≤ B)
    (hb : ∀ p, ‖r p‖ ≤ B) (hs : ∀ p, R < ‖p.1‖ → r p = 0)
    (hC : (∫ p, ‖r p‖) ≤ C) :
    (∫ x, ‖velocityLineAverage r x‖^2) ≤
      volume.real (Metric.closedBall (0 : Velocity) R)*B*C := by
  have hav := velocityLineAverage_norm_le hb hs
  calc
    _ ≤ (volume.real (Metric.closedBall (0 : Velocity) R)*B)*∫ x, ‖velocityLineAverage r x‖ :=
      bounded_integrable_square_le (velocityLineAverage_integrable hr) hav
    _ ≤ _ := mul_le_mul_of_nonneg_left ((velocityLineAverage_L1_le hr).trans hC)
      (mul_nonneg (measureReal_nonneg) hB)

theorem bounded_average_L2_norm {r : Velocity × FourierSpace → ℂ}
    (hr : Integrable r) {R B C : ℝ} (hB : 0 ≤ B)
    (hb : ∀ p, ‖r p‖ ≤ B) (hs : ∀ p, R < ‖p.1‖ → r p = 0)
    (hC : (∫ p, ‖r p‖) ≤ C) :
    ‖(velocityLineAverage_memLp_two hr hb hs).toLp (velocityLineAverage r)‖ ≤
      volume.real (Metric.closedBall (0 : Velocity) R)*B*C+1 := by
  have he := bounded_average_energy hr hB hb hs hC
  let a := (velocityLineAverage_memLp_two hr hb hs).toLp (velocityLineAverage r)
  have ha : ‖a‖^2 = ∫ x, ‖velocityLineAverage r x‖^2 := by
    rw [L2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [(velocityLineAverage_memLp_two hr hb hs).coeFn_toLp] with x hx
    rw [hx]
  change ‖a‖ ≤ _
  rw [← ha] at he
  nlinarith [sq_nonneg (‖a‖-1)]

end BoltzmannNonuniqueness.Published

end

end

section

/-! # The restricted selected step has the exact bounded mesh weights -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet
open BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem originScale_restricted_step_eq {s₀ η K α γ d₀ q δ M a T : ℝ}
    {r : ℕ → ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (n : ℕ) (hr : 0 < r n) (hδ : 0 < δ) (N : ℕ)
    {S : Set Velocity} (hS : MeasurableSet S)
    {f : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f)
    {z : Published.KineticPhase} (hz : z.1.1 ∈ Icc a T) :
    step a ((originScaleKernel (r n) s₀ η K α γ d₀ q δ M N 0).restrict hS) f z =
      ∑ j : MeshLabel (windowMesh η δ M),
        step a (dilatedFreeKernel (r n) η K α γ (meshScale s₀ η r n j)
          (d₀*meshScale s₀ η r n j^10) q j.2)
          (fun y => boundedMeshWeight s₀ η δ M a T r N n S j y*f y) z := by
  rw [step_restrict_eq_indicator]
  rw [originScale_step_eq_mesh_sum (K := K) (α := α) (γ := γ) (d₀ := d₀) (q := q)
    (M := M) (f := {y : Published.KineticPhase | y.2 ∈ S}.indicator f) hs₀ hsmax hη hηmax n hr hδ N a
    (hf.indicator (hS.preimage measurable_snd)) z]
  apply Finset.sum_congr rfl
  intro j _
  apply le_antisymm
  · apply step_slab_mono _ _ hz
    intro y hy
    exact (boundedMeshWeight_mul S j f hy).ge
  · apply step_slab_mono _ _ hz
    intro y hy
    exact (boundedMeshWeight_mul S j f hy).le

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
