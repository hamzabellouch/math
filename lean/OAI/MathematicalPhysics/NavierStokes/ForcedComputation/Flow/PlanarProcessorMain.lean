import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarMixedBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarProcessorData
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.CompactEuclideanBounds

namespace OAI

/-! The smooth planar processor theorem, assuming smooth dependence and the
first two variational equations for the actual transition, expressed by
PlanarVariations. -/

noncomputable section
namespace ForcedComputation

open ShearFlows PlanarHamiltonian PlanarRouting Set Filter
open scoped Topology ContDiff

/-- Euclidean, rather than coordinate-maximum, norms are used in this clause. -/
def ProcessorFlowBounds (V : ℝ → Plane → Plane) (Ψ : ℝ → ℝ → Plane → Plane)
    (L : ℕ) : Prop :=
  1 ≤ L ∧
  (∀ s x, ‖fderiv ℝ (euclideanMap (V s)) x‖ ≤ (L : ℝ) ∧
    ‖fderiv ℝ (fderiv ℝ (euclideanMap (V s))) x‖ ≤ (L : ℝ)) ∧
  ∀ a t, 0 ≤ t →
    (∀ x, (‖fderiv ℝ (euclideanMap (Ψ a t)) x‖ ≤ Real.exp ((L : ℝ) * t) ∧
      ‖fderiv ℝ (fderiv ℝ (euclideanMap (Ψ a t))) x‖ ≤
        Real.exp (2 * (L : ℝ) * t) - Real.exp ((L : ℝ) * t)) ∧
      (‖fderiv ℝ (euclideanMap (Ψ (a + t) (-t))) x‖ ≤ Real.exp ((L : ℝ) * t) ∧
      ‖fderiv ℝ (fderiv ℝ (euclideanMap (Ψ (a + t) (-t)))) x‖ ≤
        Real.exp (2 * (L : ℝ) * t) - Real.exp ((L : ℝ) * t))) ∧
    (∀ x y, dist (euclideanMap (Ψ a t) x) (euclideanMap (Ψ a t) y) ≤
      Real.exp ((L : ℝ) * t) * dist x y)

theorem periodic_zero_near_integers {V : ℝ → Plane → Plane}
    (hperiod : ∀ x, Function.Periodic (fun s => V s x) 1)
    (hzero : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x, V s x = 0) (n : ℤ) :
    ∀ᶠ s in 𝓝 (n : ℝ), ∀ x, V s x = 0 := by
  have ht : Tendsto (fun s : ℝ => s - (n : ℝ)) (𝓝 (n : ℝ)) (𝓝 (0 : ℝ)) := by
    have hc : Continuous (fun s : ℝ => s - (n : ℝ)) := continuous_id.sub continuous_const
    simpa only [sub_self] using hc.tendsto (n : ℝ)
  filter_upwards [ht.eventually hzero] with s hs
  intro x
  have he := (hperiod x).sub_int_mul_eq (x := s) n
  have he' : V s x = V (s - (n : ℝ)) x := by simpa only [mul_one] using he.symm
  exact he'.trans (hs x)

namespace Recorder.Planar

def processorHamiltonian (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (s : ℝ) (x : Plane) : ℝ :=
  SpatialExpression.spatialValue (normalizedHamiltonian I hI) (atHeight x s)

theorem processorHamiltonian_joint_smooth (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) :
    ContDiff ℝ ∞ (fun y : ℝ × Plane => processorHamiltonian I hI y.1 y.2) := by
  have he : ContDiff ℝ ∞ (fun y : ℝ × Plane => atHeight y.2 y.1) := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    · change ContDiff ℝ ∞ (fun y : ℝ × Plane => y.2 0)
      exact (contDiff_apply ℝ ℝ 0).comp contDiff_snd
    · change ContDiff ℝ ∞ (fun y : ℝ × Plane => y.2 1)
      exact (contDiff_apply ℝ ℝ 1).comp contDiff_snd
    · change ContDiff ℝ ∞ (fun y : ℝ × Plane => y.1)
      exact contDiff_fst
  exact (SpatialExpression.spatialValue_smooth (normalizedHamiltonian_valid I hI)).comp he

theorem processorVelocity_joint_smooth (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) :
    ContDiff ℝ ∞ (fun y : ℝ × Plane => planarSlice (normalizedHamiltonian I hI) y.1 y.2) := by
  have he : ContDiff ℝ ∞ (fun y : ℝ × Plane => atHeight y.2 y.1) := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    · change ContDiff ℝ ∞ (fun y : ℝ × Plane => y.2 0)
      exact (contDiff_apply ℝ ℝ 0).comp contDiff_snd
    · change ContDiff ℝ ∞ (fun y : ℝ × Plane => y.2 1)
      exact (contDiff_apply ℝ ℝ 1).comp contDiff_snd
    · change ContDiff ℝ ∞ (fun y : ℝ × Plane => y.1)
      exact contDiff_fst
  have hf := planeProjection.contDiff.comp
    ((SpatialExpression.suspensionField_smooth (normalizedHamiltonian_valid I hI)).comp he)
  convert hf using 1
  funext y
  simpa only [Function.comp_apply, planeProjection_apply] using
    planarSlice_eq_horizontal (normalizedHamiltonian_valid I hI) y.1 y.2

theorem compact_normalizedInstruction_period (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    {Ψ Ω : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (compactVelocity I hI) Ψ)
    (hΩ : IsPlanarTransition (planarSlice (normalizedHamiltonian I hI)) Ω)
    {y : Plane} (hy : y ∈ normalizedNeighborhood I hI b) :
    Ψ 0 1 y = (normalizedInstruction I hI b).affine y := by
  obtain ⟨z, ⟨x, hx, hzx⟩, rfl⟩ := hy
  have hc (j : Fin 2) : 0 < (translatedPoint (initialShift (freshInput I) (freshInput_valid hI)) z) j ∧
      (translatedPoint (initialShift (freshInput I) (freshInput_valid hI)) z) j < 1 := by
    simpa only [normalizedAnchors, branchAnchors_first, mem_Ioo] using
      normalizedAnchors_near_unit I hI b hx hzx 0 j
  rw [compactTransition_eq_slice I hI hΨ hΩ hc]
  exact normalizedInstruction_period I hI b hΩ ⟨z, ⟨x, hx, hzx⟩, rfl⟩

theorem normalizedNeighborhood_ball (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    {x y : Plane} (hx : x ∈ (normalizedInstruction I hI b).source.carrier)
    (hxy : dist y x < (branchRadius (freshMachine I.1) (freshInput_valid hI).1 b : ℝ)) :
    y ∈ normalizedNeighborhood I hI b := by
  let v := initialShift (freshInput I) (freshInput_valid hI)
  change x ∈ (translatedBox v (instruction (freshMachine I.1) (freshInput_valid hI).1 b).source).carrier at hx
  rw [← translatedBox_image] at hx
  obtain ⟨x₀, hx₀, he⟩ := hx
  let y₀ : Plane := fun j => y j - (v j : ℝ)
  have hy : translatedPoint v y₀ = y := by
    funext j
    simp only [translatedPoint, y₀, sub_add_cancel]
  refine ⟨y₀, ⟨x₀, hx₀, ?_⟩, hy⟩
  have hd := translatedPoint_dist v y₀ x₀
  rw [hy, he] at hd
  rw [← hd]
  exact hxy

theorem clockRectangle_in_unit {x : Plane} (hx : x ∈ clockRectangle.carrier) (j : Fin 2) :
    0 < x j ∧ x j < 1 := by
  have h := hx j
  fin_cases j <;> norm_num [clockRectangle] at h ⊢ <;> constructor <;> linarith [h.1, h.2]

/-- All clauses of Theorem 3.1, with the two equivalent chart interpretations
and the finite compiler data kept explicit. -/
structure ProcessorProperties (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (Ω Ψ : ℝ → ℝ → Plane → Plane) : Prop where
  expression_valid : (normalizedHamiltonian I hI).Valid
  expression_noTime : SpatialExpression.NoTime (normalizedHamiltonian I hI)
  expression_periods : SpatialExpression.UnitPeriods (normalizedHamiltonian I hI)
  torus_smooth : ContDiff ℝ ∞ (fun y : ℝ × Plane => planarSlice (normalizedHamiltonian I hI) y.1 y.2)
  compact_smooth : ContDiff ℝ ∞ (fun y : ℝ × Plane => compactVelocity I hI y.1 y.2)
  torus_periodic : ∀ x, Function.Periodic (fun s => planarSlice (normalizedHamiltonian I hI) s x) 1
  torus_spatial_periodic : ∀ s, PlanePeriodic (planarSlice (normalizedHamiltonian I hI) s)
  compact_periodic : ∀ x, Function.Periodic (fun s => compactVelocity I hI s x) 1
  integer_collars : ∀ n : ℤ, ∀ᶠ s in 𝓝 (n : ℝ),
    ∀ x, planarSlice (normalizedHamiltonian I hI) s x = 0 ∧ compactVelocity I hI s x = 0
  torus_solenoidal : ∀ s x, PlanarHamiltonian.divergence (planarSlice (normalizedHamiltonian I hI) s) x = 0
  torus_mean : ∀ s, (∫ x in Icc (0 : Plane) (fun _ => 1), planarSlice (normalizedHamiltonian I hI) s x) = 0
  compact_solenoidal : ∀ s x, PlanarHamiltonian.divergence (compactVelocity I hI s) x = 0
  compact_mean : ∀ s, (∫ x, compactVelocity I hI s x) = 0
  compact_support : IsCompact (commonSupport (normalizedPulse I hI)) ∧
    commonSupport (normalizedPulse I hI) ⊆ {x | ∀ j : Fin 2, 0 < x j ∧ x j < 1} ∧
    ∀ s, tsupport (compactVelocity I hI s) ⊆ commonSupport (normalizedPulse I hI) ∧
      tsupport (periodicHamiltonian (normalizedPulse I hI) s) ⊆ commonSupport (normalizedPulse I hI)
  hamiltonian : (∀ s, compactVelocity I hI s = field (periodicHamiltonian (normalizedPulse I hI) s)) ∧
    ContDiff ℝ ∞ (fun y : ℝ × Plane => periodicHamiltonian (normalizedPulse I hI) y.1 y.2) ∧
    (∀ x, Function.Periodic (fun s => periodicHamiltonian (normalizedPulse I hI) s x) 1) ∧
    ContDiff ℝ ∞ (fun y : ℝ × Plane => processorHamiltonian I hI y.1 y.2)
  chart_agreement : ∀ s x, (∀ j : Fin 2, 0 < x j ∧ x j < 1) →
    compactVelocity I hI s x = planarSlice (normalizedHamiltonian I hI) s x
  all_derivatives : ∀ α x,
    ‖planarMixed (planarField (planarSlice (normalizedHamiltonian I hI))) α x‖ ≤
      (planarMixedBound (normalizedHamiltonian I hI) α : ℝ) ∧
    ‖planarMixed (planarField (compactVelocity I hI)) α x‖ ≤
      (planarMixedBound (normalizedHamiltonian I hI) α : ℝ)
  finite_table : ∀ b, normalizedInstruction I hI b ∈ normalizedProgram I hI ∧
    (normalizedInstruction I hI b).source.positive ∧ (normalizedInstruction I hI b).target.positive ∧
    0 < (normalizedInstruction I hI b).factor ∧
    (normalizedInstruction I hI b).affine '' (normalizedInstruction I hI b).source.carrier =
      (normalizedInstruction I hI b).target.carrier
  separation : ∀ b c, b ≠ c →
    PositivelySeparated (normalizedInstruction I hI b).source.carrier (normalizedInstruction I hI c).source.carrier ∧
    PositivelySeparated (normalizedInstruction I hI b).target.carrier (normalizedInstruction I hI c).target.carrier
  neighborhoods : ∀ b, 0 < branchRadius (freshMachine I.1) (freshInput_valid hI).1 b ∧
    IsOpen (normalizedNeighborhood I hI b) ∧
    (normalizedInstruction I hI b).source.carrier ⊆ normalizedNeighborhood I hI b ∧
    ∀ y ∈ normalizedNeighborhood I hI b,
      Ω 0 1 y = (normalizedInstruction I hI b).affine y ∧
      Ψ 0 1 y = (normalizedInstruction I hI b).affine y
  neighborhood_radius : ∀ b x, x ∈ (normalizedInstruction I hI b).source.carrier →
    ∀ y, dist y x < (branchRadius (freshMachine I.1) (freshInput_valid hI).1 b : ℝ) →
      y ∈ normalizedNeighborhood I hI b
  encoded_branches : ∀ {C D}, Step (finiteMachine (freshMachine I.1) (freshInput_valid hI).1) C D →
    ∃ b, normalizedInstruction I hI b ∈ normalizedProgram I hI ∧
      normalizedPoint I hI C ∈ (normalizedInstruction I hI b).source.carrier ∧
      (normalizedInstruction I hI b).affine (normalizedPoint I hI C) = normalizedPoint I hI D
  torus_transition : IsPlanarTransition (planarSlice (normalizedHamiltonian I hI)) Ω
  compact_transition : IsPlanarTransition (compactVelocity I hI) Ψ
  integer_encoding : ∀ {n C},
    Steps (finiteMachine (freshMachine I.1) (freshInput_valid hI).1) n (normalizedInitial I hI) C →
    Ω 0 n ![1 / 4, 1 / 4] = normalizedPoint I hI C ∧
      Ψ 0 n ![1 / 4, 1 / 4] = normalizedPoint I hI C
  step_corridor : ∀ {C D}, Step (finiteMachine (freshMachine I.1) (freshInput_valid hI).1) C D →
    ∀ s ∈ Icc (0 : ℝ) 1,
      Ω 0 s (normalizedPoint I hI C) ∈ clockRectangle.carrier ∧
      Ψ 0 s (normalizedPoint I hI C) ∈ clockRectangle.carrier
  observation : ((∃ t : ℝ, 0 ≤ t ∧ Ω 0 t ![1 / 4, 1 / 4] ∈ observer) ↔ Alternating.Halts I) ∧
    ((∃ t : ℝ, 0 ≤ t ∧ Ψ 0 t ![1 / 4, 1 / 4] ∈ observer) ↔ Alternating.Halts I)
  nonhalting : ¬ Alternating.Halts I → ∀ t : ℝ, 0 ≤ t →
    (Ω 0 t ![1 / 4, 1 / 4] ∈ clockRectangle.carrier ∧ 3 / 16 ≤ Ω 0 t ![1 / 4, 1 / 4] 1) ∧
    (Ψ 0 t ![1 / 4, 1 / 4] ∈ clockRectangle.carrier ∧ 3 / 16 ≤ Ψ 0 t ![1 / 4, 1 / 4] 1)
  halt_clearance : Alternating.Halts I → ∃ n : ℕ,
    1 / 16 ≤ Ω 0 n ![1 / 4, 1 / 4] 1 ∧ Ω 0 n ![1 / 4, 1 / 4] 1 ≤ 3 / 32 ∧
    1 / 16 ≤ Ψ 0 n ![1 / 4, 1 / 4] 1 ∧ Ψ 0 n ![1 / 4, 1 / 4] 1 ≤ 3 / 32
  euclidean_bounds : ProcessorFlowBounds (planarSlice (normalizedHamiltonian I hI)) Ω
      (euclideanFlowBound (normalizedHamiltonian I hI)) ∧
    ProcessorFlowBounds (compactVelocity I hI) Ψ (euclideanFlowBound (normalizedHamiltonian I hI))

theorem smooth_planar_processor (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (Ω : ℝ → ℝ → Plane → Plane)
    (hΩ : IsPlanarTransition (planarSlice (normalizedHamiltonian I hI)) Ω)
    (hv : PlanarVariations (planarSlice (normalizedHamiltonian I hI)) Ω) :
    ∃ Ψ, ProcessorProperties I hI Ω Ψ := by
  obtain ⟨Ψ, hΨ⟩ := compactVelocity_transitions I hI
  have he (a t : ℝ) : Ψ a t ![1 / 4, 1 / 4] = Ω a t ![1 / 4, 1 / 4] :=
    compactTransition_eq_slice I hI hΨ hΩ (by intro j; fin_cases j <;> norm_num) a t
  refine ⟨Ψ, {
    expression_valid := normalizedHamiltonian_valid I hI
    expression_noTime := normalizedHamiltonian_noTime I hI
    expression_periods := normalizedHamiltonian_unitPeriods I hI
    torus_smooth := processorVelocity_joint_smooth I hI
    compact_smooth := compactVelocity_smooth I hI
    torus_periodic := planarSlice_periodic (normalizedHamiltonian_periodic I hI)
    torus_spatial_periodic := fun s => planarSlice_spatial_periodic (normalizedHamiltonian_valid I hI)
      (normalizedHamiltonian_periodic I hI) s
    compact_periodic := periodicVelocity_periodic (normalizedPulse I hI)
    integer_collars := ?_
    torus_solenoidal := planarSlice_divergence (normalizedHamiltonian_valid I hI)
    torus_mean := planarSlice_mean_zero (normalizedHamiltonian_valid I hI) (normalizedHamiltonian_periodic I hI)
    compact_solenoidal := fun s => (periodicVelocity_properties (normalizedPulse_valid I hI) s).2.1
    compact_mean := fun s => (periodicVelocity_properties (normalizedPulse_valid I hI) s).2.2
    compact_support := ⟨commonSupport_compact _, commonSupport_in_unit (normalizedPulse_inUnit I hI),
      fun s => ⟨compactVelocity_support I hI s, periodicHamiltonian_support (normalizedPulse_valid I hI) s⟩⟩
    hamiltonian := ⟨fun _ => rfl, periodicHamiltonian_smooth (normalizedPulse_valid I hI),
      periodicHamiltonian_periodic _, processorHamiltonian_joint_smooth I hI⟩
    chart_agreement := fun s x hx => normalized_planar_field_on_chart I hI s x (hx 0) (hx 1)
    all_derivatives := fun α x => ⟨planarMixed_slice_bound (normalizedHamiltonian_valid I hI)
      (normalizedHamiltonian_noTime I hI) α x, compactPlanar_mixed_bound I hI α x⟩
    finite_table := fun b => ⟨normalizedInstruction_mem I hI b, normalizedInstruction_properties I hI b⟩
    separation := fun _ _ hne => normalizedInstruction_separation I hI hne
    neighborhoods := ?_
    neighborhood_radius := fun _ _ hx _ hxy => normalizedNeighborhood_ball I hI _ hx hxy
    encoded_branches := normalizedInstruction_encodes I hI
    torus_transition := hΩ
    compact_transition := hΨ
    integer_encoding := ?_
    step_corridor := ?_
    observation := ?_
    nonhalting := ?_
    halt_clearance := ?_
    euclidean_bounds := ?_ }⟩
  · intro n
    have h₁ := periodic_zero_near_integers (planarSlice_periodic (normalizedHamiltonian_periodic I hI))
      (normalized_planar_zero_near_zero I hI) n
    have h₂ := periodic_zero_near_integers (periodicVelocity_periodic (normalizedPulse I hI))
      (periodicVelocity_zero_near_zero (normalizedPulse_valid I hI) (normalizedPulse_inUnit I hI)) n
    filter_upwards [h₁, h₂] with s hs₁ hs₂
    exact fun x => ⟨hs₁ x, hs₂ x⟩
  · intro b
    exact ⟨branchRadius_pos _ _ b, (normalizedInstruction_neighborhood I hI b).1,
      (normalizedInstruction_neighborhood I hI b).2, fun y hy =>
        ⟨normalizedInstruction_period I hI b hΩ hy, compact_normalizedInstruction_period I hI b hΨ hΩ hy⟩⟩
  · intro n C hs
    have hc := normalized_steps_realized I hI hΩ hs
    rw [normalizedPoint_initial] at hc
    exact ⟨hc, (he 0 n).trans hc⟩
  · intro C D hs s ht
    have hc := normalized_step_corridor I hI hΩ hs ht
    have h₀ := normalized_step_corridor I hI hΩ hs (s := 0) (by norm_num)
    rw [hΩ.initial] at h₀
    have hcmp := compactTransition_eq_slice I hI hΨ hΩ (clockRectangle_in_unit h₀) 0 s
    exact ⟨hc, hcmp.symm ▸ hc⟩
  · exact ⟨normalized_planar_observation I hI hΩ, by
      simpa only [he] using normalized_planar_observation I hI hΩ⟩
  · intro hno t ht
    have hc := normalized_nonhalting_corridor I hI hΩ hno ht
    exact ⟨hc, by simpa only [he] using hc⟩
  · intro hh
    obtain ⟨n, hn⟩ := normalized_halting_clearance I hI hΩ hh
    exact ⟨n, hn.1, hn.2, by simpa only [he] using hn.1, by simpa only [he] using hn.2⟩
  · exact ⟨planar_euclidean_flow_estimates (normalizedHamiltonian_valid I hI)
      (normalizedHamiltonian_noTime I hI) hv,
      ⟨euclideanFlowBound_one_le _, compact_euclidean_field_bounds I hI,
        compact_euclidean_flow_estimates I hI hΨ hΩ hv⟩⟩

end Recorder.Planar
end ForcedComputation

end

end OAI
