import OAI.GroupTheory.Kervaire.WeightedCycles

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate

namespace KervaireRegular
open KervaireSpectral
open scoped ComplexOrder
variable {A : Type*} [Group A]

@[simp] theorem star_leftOperator (a : A) : star (leftOperator a) = leftOperator a⁻¹ := by
  change ContinuousLinearMap.adjoint (left a).toContinuousLinearEquiv.toContinuousLinearMap = _
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  ext f x
  simp [leftOperator, left, reindex_symm, reindex_apply]

theorem leftOperator_mem (a : A) : InCommutant (leftOperator a) := by
  intro b
  apply ContinuousLinearMap.ext
  intro f
  exact left_right a b f

/-- The endpoint `τ(phase(L(a)))=0 → a=1`, on the full arbitrary group.
The positive trace faithfulness is proved above, not assumed. -/
theorem groupPhase_eq_zero_iff (a : A) : groupPhase 1 (one_mem _) a = 0 ↔ a = 1 := by
  let _ : Nontrivial ℓ²(A, ℂ) := by
    classical
    refine ⟨⟨delta (1 : A), 0, ?_⟩⟩
    intro h
    have hh := congrArg (fun f : ℓ²(A, ℂ) => f 1) h
    simp [delta] at hh
  let _ := isStarNormal_of_mem_unitary (leftOperator_unitary a)
  have hp : groupPhase 1 (one_mem _) a = vectorPhase (leftOperator a) (delta 1) := by
    simp only [groupPhase, one_smul]
  obtain ⟨B,hB,_,_,hexp,hvec,hcomm⟩ := exists_phaseOperator (leftOperator a) (leftOperator_unitary a)
  have hBm : InCommutant B := by
    intro b
    apply hcomm _ (leftOperator_mem a b)
    rw [star_leftOperator]
    exact leftOperator_mem a⁻¹ b
  constructor
  · intro hz
    have hre : (trace B).re = 0 := by rw [trace_apply, hvec, ← hp, hz]
    have him : (trace B).im = 0 := by
      exact (Complex.nonneg_iff.mp ((ContinuousLinearMap.nonneg_iff_isPositive.mp hB).inner_nonneg_right _)).2.symm
    have hzB : B = 0 := (trace_eq_zero_iff_of_nonneg hBm hB).mp (Complex.ext hre him)
    rw [hzB, smul_zero, NormedSpace.exp_zero] at hexp
    have he : delta (1 : A) = delta a := by
      simpa only [one_apply_eq_self, leftOperator_delta, mul_one] using
        congrArg (fun T : Operator A => T (delta 1)) hexp
    have hv := congrArg (fun f : ℓ²(A, ℂ) => f a) he
    classical
    by_contra ha
    simp [delta, ha] at hv
  · intro ha
    subst a
    simp only [groupPhase, vectorPhase]
    apply MeasureTheory.integral_eq_zero_of_ae
    filter_upwards [] with z
    have hspec : (z : ℂ) ∈ spectrum ℂ (1 : Operator A) := by
      simpa only [one_smul, leftOperator_one] using z.property
    have hz : (z : ℂ) = 1 := by
      simpa only [spectrum.one_eq, Set.mem_singleton_iff] using hspec
    simp [hz]

/-- The nonnegative cut convention gives precisely the right-hand continuity
used at the distinguished boundary. -/
theorem tendsto_groupPhase_rotation (a : A) {x : ℕ → ℝ}
    (hx : Filter.Tendsto x Filter.atTop (nhds 0)) (hx0 : ∀ n, 0 ≤ x n) :
    Filter.Tendsto (fun n => groupPhase (scalarRotation (x n)) (scalarRotation_unitary _) a)
      Filter.atTop (nhds (groupPhase 1 (one_mem _) a)) := by
  simpa only [groupPhase, one_smul] using
    tendsto_vectorPhase_rotation (leftOperator a) (leftOperator_unitary a) (delta 1) hx hx0
end KervaireRegular

namespace KervaireSpectral
open KervaireTraceCalculus
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Fixed vectors carry zero phase, including the atom at the phase cut. -/
theorem vectorPhase_eq_zero_of_fixed (U : Operator H) (hU : U ∈ unitary (Operator H))
    (ξ : H) (hξ : U ξ = ξ) :
    let _ := isStarNormal_of_mem_unitary hU
    vectorPhase U ξ = 0 := by
  let _ := isStarNormal_of_mem_unitary hU
  have hh : ∫ z, distanceSq U z ∂vectorMeasure U ξ = 0 := by
    simp [integral_distanceSq, hξ]
  have hi : Integrable (distanceSq U) (vectorMeasure U ξ) :=
    (distanceSq U).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hd : (fun z => distanceSq U z) =ᵐ[vectorMeasure U ξ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun z => Complex.normSq_nonneg _) hi).mp hh
  have hp : (fun z : spectrum ℂ U => phase z) =ᵐ[vectorMeasure U ξ] 0 := by
    filter_upwards [hd] with z hz
    have hz' : (z : ℂ) = 1 := sub_eq_zero.mp (Complex.normSq_eq_zero.mp hz)
    simp [hz']
  exact (integral_congr_ae hp).trans (integral_zero _ _)

/-- An inverse pair contributes at most one unit of phase per unit vector. -/
theorem vectorPhase_add_star_le (U : Operator H) (hU : U ∈ unitary (Operator H)) (ξ : H) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary (Unitary.star_mem hU)
    vectorPhase U ξ + vectorPhase (star U) ξ ≤ ‖ξ‖^2 := by
  let _ := isStarNormal_of_mem_unitary hU
  let _ := isStarNormal_of_mem_unitary (Unitary.star_mem hU)
  have hi : Integrable (fun z : spectrum ℂ U => phase (star (z : ℂ))) (vectorMeasure U ξ) := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
      (measurable_phase.comp (continuous_subtype_val.star.measurable)).aestronglyMeasurable
    filter_upwards [] with z
    change |phase (star (z : ℂ))| ≤ 1
    rw [abs_of_nonneg (phase_nonneg _)]
    exact (phase_lt_one _).le
  change vectorPhase U ξ + vectorPhase (star U) ξ ≤ ‖ξ‖^2
  rw [vectorPhase_star U hU, vectorPhase, ← integral_add (integrable_phase U ξ) hi]
  calc
    (∫ z, (phase (z : ℂ) + phase (star (z : ℂ))) ∂vectorMeasure U ξ) ≤ ∫ _z, (1 : ℝ) ∂vectorMeasure U ξ := by
      apply integral_mono ((integrable_phase U ξ).add hi) (integrable_const _)
      intro z
      exact phase_add_star_le_one (CStarRing.norm_of_mem_unitary
        (spectrum_subset_unitary_of_mem_unitary hU z.property))
    _ = ‖ξ‖^2 := by
      rw [integral_one_vectorMeasure, vectorCLM_apply]
      exact inner_self_eq_norm_sq (𝕜 := ℂ) ξ

end KervaireSpectral

end

end OAI
