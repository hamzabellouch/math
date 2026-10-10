import OAI.GroupTheory.Kervaire.PhaseNaturality

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

/-- The unnormalized sum of the grid points `j/d`. -/
theorem sum_fin_val_real (d : ℕ) :
    (∑ j : Fin d, (j.val : ℝ)) = (d : ℝ) * ((d : ℝ)-1) / 2 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.cast_add, Nat.cast_one]
    ring

/-- The exact fractional-part grid identity, including values on the cut. -/
theorem sum_fract_grid (d : ℕ) (hd : 0 < d) (x : ℝ) (hx : 0 ≤ x ∧ x < 1) :
    (∑ j : Fin d, Int.fract (x + (j.val : ℝ) / d)) =
      ((d : ℝ)-1)/2 + Int.fract ((d : ℝ)*x) := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hdx : 0 ≤ (d : ℝ)*x := mul_nonneg hdR.le hx.1
  let q : Fin d := ⟨⌊(d : ℝ)*x⌋₊, by
    apply (Nat.floor_lt hdx).mpr
    nlinarith⟩
  let r : ℝ := Int.fract ((d : ℝ)*x)
  have hr0 : 0 ≤ r := Int.fract_nonneg _
  have hr1 : r < 1 := Int.fract_lt_one _
  have hqr : (q.val : ℝ) + r = (d : ℝ)*x := by
    dsimp [q,r]
    rw [natCast_floor_eq_intCast_floor hdx, Int.floor_add_fract]
  have hgrid (j : Fin d) :
      Int.fract (x+(j.val : ℝ)/d) = (r + ((q+j).val : ℝ)) / d := by
    let a : ℕ := (q.val+j.val)/d
    apply Int.fract_eq_iff.mpr
    refine ⟨div_nonneg (add_nonneg hr0 (Nat.cast_nonneg _)) hdR.le, ?_,
      (a : ℤ), ?_⟩
    · apply (div_lt_one hdR).mpr
      have hval : ((q+j).val : ℝ) + 1 ≤ d := by
        exact_mod_cast Nat.succ_le_of_lt (q+j).isLt
      linarith
    · change x + (j.val : ℝ) / d - (r + ((q+j).val : ℝ)) / d = (a : ℝ)
      have hm : (q+j).val + d * a = q.val+j.val :=
        Nat.mod_add_div _ _
      have hmR : ((q+j).val : ℝ) + (d : ℝ)*(a : ℝ) =
          (q.val : ℝ) + j.val := by exact_mod_cast hm
      apply (mul_right_inj' hdR.ne').mp
      field_simp
      nlinarith
  simp_rw [hgrid]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  have he : (∑ j : Fin d, ((q+j).val : ℝ)) = ∑ j : Fin d, (j.val : ℝ) :=
    Equiv.sum_comp (Equiv.addLeft q) (fun j : Fin d => (j.val : ℝ))
  rw [he, sum_fin_val_real]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  dsimp [r]
  field_simp
  ring

@[simp] theorem scalarRotation_nat_mul (x : ℝ) (d : ℕ) :
    scalarRotation ((d : ℝ)*x) = scalarRotation x ^ d := by
  unfold scalarRotation
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem phase_pow {z : ℂ} (hz : ‖z‖ = 1) (d : ℕ) :
    phase (z^d) = Int.fract ((d : ℝ)*phase z) := by
  conv_lhs => rw [← exp_phase hz]
  change phase (scalarRotation (phase z) ^ d) = _
  rw [← scalarRotation_nat_mul]
  exact phase_exp_normalized _

/-- The exact root-of-unity phase identity on the circle. -/
theorem sum_phase_grid {z : ℂ} (hz : ‖z‖ = 1) (d : ℕ) (hd : 0 < d) :
    (∑ j : Fin d, phase (scalarRotation ((j.val : ℝ)/d)*z)) =
      ((d : ℝ)-1)/2 + phase (z^d) := by
  simp_rw [phase_rotation hz, add_comm ((_:ℝ)/d) (phase z)]
  rw [sum_fract_grid d hd (phase z) ⟨phase_nonneg z, phase_lt_one z⟩, phase_pow hz]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Integrate the root-of-unity identity against a scalar spectral measure. -/
theorem sum_vectorPhase_grid (U : Operator H) (hU : U ∈ unitary (Operator H))
    (d : ℕ) (hd : 0 < d) (ξ : H) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary (pow_mem hU d)
    let _ := fun j : Fin d => isStarNormal_of_mem_unitary
      (Unitary.smul_mem ⟨scalarRotation ((j.val : ℝ)/d), scalarRotation_unitary _⟩ hU)
    (∑ j : Fin d, vectorPhase (scalarRotation ((j.val : ℝ)/d) • U) ξ) =
      ((d : ℝ)-1)/2 * ‖ξ‖^2 + vectorPhase (U^d) ξ := by
  let _ := isStarNormal_of_mem_unitary hU
  let _ := isStarNormal_of_mem_unitary (pow_mem hU d)
  change (∑ j : Fin d, vectorPhase (scalarRotation ((j.val : ℝ)/d) • U) ξ) = _
  simp_rw [vectorPhase_rotation U hU]
  have hi (j : Fin d) : Integrable
      (fun z : spectrum ℂ U => phase (scalarRotation ((j.val : ℝ)/d) * z))
      (vectorMeasure U ξ) := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
      (measurable_phase.comp ((continuous_const.mul continuous_subtype_val).measurable)).aestronglyMeasurable
    filter_upwards [] with z
    change |phase _| ≤ 1
    rw [abs_of_nonneg (phase_nonneg _)]
    exact (phase_lt_one _).le
  rw [← integral_finsetSum _ (fun j _ => hi j)]
  have hp : Integrable (fun z : spectrum ℂ U => phase ((z : ℂ)^d)) (vectorMeasure U ξ) := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
      (measurable_phase.comp (continuous_subtype_val.pow d).measurable).aestronglyMeasurable
    filter_upwards [] with z
    change |phase _| ≤ 1
    rw [abs_of_nonneg (phase_nonneg _)]
    exact (phase_lt_one _).le
  have he (z : spectrum ℂ U) := sum_phase_grid (CStarRing.norm_of_mem_unitary
    (spectrum_subset_unitary_of_mem_unitary hU z.property)) d hd
  simp_rw [he]
  rw [integral_add (integrable_const _) hp, vectorPhase_pow U hU]
  congr 1
  have hm : (∫ _z : spectrum ℂ U, (1 : ℝ) ∂vectorMeasure U ξ) = ‖ξ‖^2 := by
    rw [integral_one_vectorMeasure, vectorCLM_apply]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) ξ
  rw [← hm, ← integral_const_mul]
  simp only [mul_one]

end

open KervaireTraceCalculus KervaireScalarPhase
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Positive integral moments, including mass, determine the cut-sensitive phase.
This avoids assuming any Borel functional calculus naturality theorem. -/
theorem sumPhase_eq_of_moments
    (U : Operator H) (V : Operator K)
    (hU : U ∈ unitary (Operator H)) (hV : V ∈ unitary (Operator K))
    (ξ : ι → H) (η : κ → K)
    (hm : ∀ n : ℕ, vectorSum ξ (U ^ n) = vectorSum η (V ^ n)) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary hV
    sumPhase U ξ = sumPhase V η := by
  let _ := isStarNormal_of_mem_unitary hU
  let _ := isStarNormal_of_mem_unitary hV
  have hs (a : ℂ) : smoothTrace (vectorSum ξ) a U = smoothTrace (vectorSum η) a V := by
    have hmass := hm 0
    simp only [pow_zero] at hmass
    unfold smoothTrace traceLog
    rw [hmass]
    simp_rw [hm]
  exact tendsto_nhds_unique (tendsto_smoothTrace_vectorSum U hU ξ)
    (by simpa only [hs] using tendsto_smoothTrace_vectorSum V hV η)

end KervaireSpectral

end

end OAI
