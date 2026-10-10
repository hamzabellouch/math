import OAI.GroupTheory.Kervaire.PhaseSubadditivity

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

namespace KervaireSpectral

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The cut-sensitive phase has the expected scalar-measure pullback under
continuous functional calculus. This is proved from triangular approximants. -/
theorem vectorPhase_cfcHom (U : Operator H) [hN : IsStarNormal U]
    (f : C(spectrum ℂ U, ℂ)) (hf : cfcHom hN f ∈ unitary (Operator H)) (ξ : H) :
    let _ := isStarNormal_of_mem_unitary hf
    vectorPhase (cfcHom hN f) ξ = ∫ z, phase (f z) ∂vectorMeasure U ξ := by
  let V := cfcHom hN f
  let _ := isStarNormal_of_mem_unitary hf
  let f' : C(spectrum ℂ U, spectrum ℂ V) :=
    ⟨fun z => ⟨f z, by
      rw [show spectrum ℂ V = Set.range f from cfcHom_map_spectrum hN f]
      exact Set.mem_range_self z⟩,
      continuous_induced_rng.mpr f.continuous⟩
  have he (n : ℕ) :
      (∫ z, phaseApprox V hf n z ∂vectorMeasure V ξ) =
        ∫ z, phaseApprox V hf n (f' z) ∂vectorMeasure U ξ := by
    change _ = ∫ z, ((phaseApprox V hf n).comp f') z ∂vectorMeasure U ξ
    rw [integral_vectorMeasure, integral_vectorMeasure]
    have hh := cfcHom_comp hN f f' (fun _ => rfl) (complexify (phaseApprox V hf n))
    exact congrArg (fun T : Operator H => (inner ℂ ξ (T ξ)).re) hh.symm
  have ht : Tendsto
      (fun n => ∫ z, phaseApprox V hf n (f' z) ∂vectorMeasure U ξ)
      atTop (𝓝 (∫ z, phase (f z) ∂vectorMeasure U ξ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => 1)
    · intro n
      exact ((phaseApprox V hf n).continuous.comp f'.continuous).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_of_nonneg (phaseApprox_nonneg V hf n (f' z))]
      exact phaseApprox_le_one V hf n (f' z)
    · exact Eventually.of_forall fun z => tendsto_phaseApprox V hf (f' z)
  exact tendsto_nhds_unique (tendsto_integral_phaseApprox V hf ξ)
    (by simpa only [he] using ht)

/-- Naturality for taking the inverse of a unitary. -/
theorem vectorPhase_star (U : Operator H) (hU : U ∈ unitary (Operator H)) (ξ : H) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary (Unitary.star_mem hU)
    vectorPhase (star U) ξ = ∫ z, phase (star (z : ℂ)) ∂vectorMeasure U ξ := by
  let hN := isStarNormal_of_mem_unitary hU
  let f : C(spectrum ℂ U, ℂ) := star ((ContinuousMap.id ℂ).restrict (spectrum ℂ U))
  have hf : cfcHom hN f = star U := by
    dsimp [f]
    rw [map_star, cfcHom_id]
  have hu : cfcHom hN f ∈ unitary (Operator H) := hf ▸ Unitary.star_mem hU
  simpa only [hf, f, ContinuousMap.star_apply, ContinuousMap.restrict_apply,
    ContinuousMap.id_apply] using vectorPhase_cfcHom U f hu ξ

/-- Naturality for positive powers, needed for the boundary-cycle calculation. -/
theorem vectorPhase_pow (U : Operator H) (hU : U ∈ unitary (Operator H)) (n : ℕ) (ξ : H) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary (pow_mem hU n)
    vectorPhase (U^n) ξ = ∫ z, phase ((z : ℂ)^n) ∂vectorMeasure U ξ := by
  let hN := isStarNormal_of_mem_unitary hU
  let f : C(spectrum ℂ U, ℂ) := ((ContinuousMap.id ℂ).restrict (spectrum ℂ U))^n
  have hf : cfcHom hN f = U^n := by
    dsimp [f]
    rw [map_pow, cfcHom_id]
  have hu : cfcHom hN f ∈ unitary (Operator H) := hf ▸ pow_mem hU n
  simpa only [hf, f, ContinuousMap.pow_apply, ContinuousMap.restrict_apply,
    ContinuousMap.id_apply] using vectorPhase_cfcHom U f hu ξ

end

def scalarRotation (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

@[simp] theorem scalarRotation_zero : scalarRotation 0 = 1 := by simp [scalarRotation]

@[simp] theorem norm_scalarRotation (x : ℝ) : ‖scalarRotation x‖ = 1 := by
  simp [scalarRotation, Complex.norm_exp]

@[simp] theorem scalarRotation_add (x y : ℝ) :
    scalarRotation (x+y) = scalarRotation x * scalarRotation y := by
  simp only [scalarRotation, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

@[simp] theorem star_scalarRotation (x : ℝ) : star (scalarRotation x) = scalarRotation (-x) := by
  unfold scalarRotation
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg,
    mul_neg, neg_mul]

theorem scalarRotation_unitary (x : ℝ) : scalarRotation x ∈ unitary ℂ := by
  rw [Unitary.mem_iff]
  simp only [star_scalarRotation, ← scalarRotation_add, neg_add_cancel, add_neg_cancel,
    scalarRotation_zero, and_self]

theorem phase_rotation {z : ℂ} (hz : ‖z‖ = 1) (x : ℝ) :
    phase (scalarRotation x * z) = Int.fract (x + phase z) := by
  conv_lhs => rw [← exp_phase hz]
  change phase (scalarRotation x * scalarRotation (phase z)) = _
  rw [← scalarRotation_add]
  exact phase_exp_normalized _

theorem phase_star {z : ℂ} (hz : ‖z‖ = 1) : phase (star z) = Int.fract (-phase z) := by
  conv_lhs => rw [← exp_phase hz]
  change phase (star (scalarRotation (phase z))) = _
  rw [star_scalarRotation]
  exact phase_exp_normalized _

theorem phase_add_star_le_one {z : ℂ} (hz : ‖z‖ = 1) :
    phase z + phase (star z) ≤ 1 := by
  rw [phase_star hz]
  simpa only [Int.fract_eq_self.mpr ⟨phase_nonneg z, phase_lt_one z⟩, add_neg_cancel, Int.fract_zero, zero_add] using
    Int.fract_add_fract_le (phase z) (-phase z)

/-- The exact one-sided convergence used at the exceptional boundary circle. -/
theorem tendsto_phase_rotation {ι : Type*} {l : Filter ι} {a : ι → ℝ}
    (ha : Tendsto a l (𝓝 0)) (ha0 : ∀ᶠ i in l, 0 ≤ a i)
    {z : ℂ} (hz : ‖z‖ = 1) :
    Tendsto (fun i => phase (scalarRotation (a i) * z)) l (𝓝 (phase z)) := by
  have ht : Tendsto (fun i => a i + phase z) l (𝓝 (phase z)) := by
    simpa only [zero_add] using ha.add_const (phase z)
  have he : (fun i => phase (scalarRotation (a i) * z)) =ᶠ[l]
      (fun i => a i + phase z) := by
    filter_upwards [ha0, ht.eventually (gt_mem_nhds (phase_lt_one z))] with i hi hi'
    rw [phase_rotation hz, Int.fract_eq_self.mpr ⟨add_nonneg hi (phase_nonneg z), hi'⟩]
  exact ht.congr' he.symm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The scalar-rotation formula for the exact spectral measure. -/
theorem vectorPhase_rotation (U : Operator H) (hU : U ∈ unitary (Operator H))
    (x : ℝ) (ξ : H) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary (Unitary.smul_mem ⟨scalarRotation x,
      scalarRotation_unitary x⟩ hU)
    vectorPhase (scalarRotation x • U) ξ =
      ∫ z, phase (scalarRotation x * (z : ℂ)) ∂vectorMeasure U ξ := by
  let hN := isStarNormal_of_mem_unitary hU
  let f : C(spectrum ℂ U, ℂ) := scalarRotation x •
    (ContinuousMap.id ℂ).restrict (spectrum ℂ U)
  have hf : cfcHom hN f = scalarRotation x • U := by
    dsimp [f]
    rw [map_smul, cfcHom_id]
  have hu : cfcHom hN f ∈ unitary (Operator H) := by
    rw [hf]
    exact Unitary.smul_mem ⟨scalarRotation x, scalarRotation_unitary x⟩ hU
  simpa only [hf, f, ContinuousMap.smul_apply, ContinuousMap.restrict_apply,
    ContinuousMap.id_apply, smul_eq_mul] using vectorPhase_cfcHom U f hu ξ

/-- Bounded convergence at the phase cut from the nonnegative-shift side. -/
theorem tendsto_vectorPhase_rotation (U : Operator H) (hU : U ∈ unitary (Operator H))
    (ξ : H) {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0)) (ha0 : ∀ n, 0 ≤ a n) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := fun n => isStarNormal_of_mem_unitary (Unitary.smul_mem
      ⟨scalarRotation (a n), scalarRotation_unitary (a n)⟩ hU)
    Tendsto (fun n => vectorPhase (scalarRotation (a n) • U) ξ) atTop (𝓝 (vectorPhase U ξ)) := by
  let _ := isStarNormal_of_mem_unitary hU
  simp_rw [vectorPhase_rotation U hU]
  apply tendsto_integral_of_dominated_convergence (fun _ => 1)
  · intro n
    exact (measurable_phase.comp ((continuous_const.mul continuous_subtype_val).measurable)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (phase_nonneg _)]
    exact (phase_lt_one _).le
  · filter_upwards [] with z
    exact tendsto_phase_rotation ha (Eventually.of_forall ha0)
      (CStarRing.norm_of_mem_unitary (spectrum_subset_unitary_of_mem_unitary hU z.property))

end KervaireSpectral

end

end OAI
