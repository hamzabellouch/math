import OAI.MeasureTheory.Falconer.Fourier.MaskedStationaryJets

namespace OAI

/-! # Uniform mixed bounds for the actual stationary chart

The reflection formula preserves norm even when its direction parameter is
off the sphere. This permits ambient derivatives in that parameter while
the original symbol is evaluated only on sphere points.
-/

namespace Falconer
open Set Metric
open scoped ContDiff RealInnerProductSpace

theorem poleRotationFormula_eq_reflection {n : ℕ} (p e x : Space n) :
    poleRotationFormula p e x = (ℝ ∙ (p+e)).reflection x := by
  rw [Submodule.reflection_singleton_apply]
  simp [poleRotationFormula, two_smul, two_mul, add_div, add_smul]

theorem poleRotationFormula_norm {n : ℕ} (p e x : Space n) :
    ‖poleRotationFormula p e x‖ = ‖x‖ := by
  rw [poleRotationFormula_eq_reflection]
  exact (ℝ ∙ (p+e)).reflection.norm_map x

noncomputable def jointStationaryChart (m : ℕ)
    (z : Space (m+3) × Space (m+2)) : Space (m+3) :=
  poleRotationFormula (gnomonicChart (0 : Space (m+2))) z.1 (quadraticSpherePoint z.2)

def jointStationaryRegion (m : ℕ) : Set (Space (m+3) × Space (m+2)) :=
  {z | (gnomonicChart (0 : Space (m+2)) : Space (m+3))+z.1 ≠ 0 ∧ ‖z.2‖ < 2}

def jointStationaryCompact (m : ℕ) : Set (Space (m+3) × Space (m+2)) :=
  closedBall (gnomonicChart (0 : Space (m+2)) : Space (m+3)) (1/4) ×ˢ
    closedBall (0 : Space (m+2)) 1

theorem jointStationaryRegion_isOpen (m : ℕ) : IsOpen (jointStationaryRegion m) := by
  exact (isOpen_ne_fun (continuous_const.add continuous_fst) continuous_const).inter
    (isOpen_lt continuous_snd.norm continuous_const)

theorem jointStationaryCompact_isCompact (m : ℕ) : IsCompact (jointStationaryCompact m) :=
  (isCompact_closedBall (gnomonicChart (0 : Space (m+2)) : Space (m+3)) (1/4)).prod
    (isCompact_closedBall (0 : Space (m+2)) 1)

theorem jointStationaryCompact_subset (m : ℕ) :
    jointStationaryCompact m ⊆ jointStationaryRegion m := by
  intro z hz
  have he : ‖z.1-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/4 := by
    simpa only [mem_closedBall,dist_eq_norm] using hz.1
  have hu : ‖z.2‖ ≤ 1 := by
    simpa only [mem_closedBall,dist_zero_right] using hz.2
  exact ⟨stationary_patch_ne_antipode m he,by linarith⟩

theorem jointStationaryChart_contDiffAt (m : ℕ)
    {z : Space (m+3) × Space (m+2)} (hz : z ∈ jointStationaryRegion m) :
    ContDiffAt ℝ ∞ (jointStationaryChart m) z := by
  have hq := (quadraticSpherePoint_contDiffAt hz.2).comp z contDiffAt_snd
  have hr := (poleRotationFormula_contDiffAt (gnomonicChart (0 : Space (m+2)))
    z.1 (quadraticSpherePoint z.2) hz.1).comp z (contDiffAt_fst.prodMk hq)
  exact hr

theorem jointStationaryChart_norm (m : ℕ)
    (z : Space (m+3) × Space (m+2)) (hz : ‖z.2‖ ≤ 2) :
    ‖jointStationaryChart m z‖ = 1 := by
  rw [jointStationaryChart,poleRotationFormula_norm]
  exact quadraticSpherePoint_norm hz

theorem unmaskedStationaryAmplitude_contDiffAt_region (m : ℕ)
    {B : Space (m+3) → ℂ} (hB : ContDiff ℝ ∞ B)
    {z : Space (m+3) × Space (m+2)} (hz : z ∈ jointStationaryRegion m) :
    ContDiffAt ℝ ∞ (unmaskedStationaryAmplitude m B) z := by
  exact ((quadraticChartDensity_contDiffAt m hz.2).comp z contDiffAt_snd).mul
    (hB.contDiffAt.comp z (jointStationaryChart_contDiffAt m hz))

theorem joint_stationary_geometry_bounds (m K : ℕ) :
    ∃ Q R : ℝ, 0 ≤ Q ∧ 0 ≤ R ∧ ∀ j ≤ K, ∀ z ∈ jointStationaryCompact m,
      ‖iteratedFDeriv ℝ j (jointStationaryChart m) z‖ ≤ Q ∧
      ‖iteratedFDeriv ℝ j (fun z : Space (m+3) × Space (m+2) =>
        quadraticChartDensity m z.2) z‖ ≤ R := by
  obtain ⟨Q,hQ,hQb⟩ := compact_iteratedFDeriv_bound_at (jointStationaryCompact_isCompact m)
    (fun z hz => jointStationaryChart_contDiffAt m (jointStationaryCompact_subset m hz)) K
  obtain ⟨R,hR,hRb⟩ := compact_iteratedFDeriv_bound_at (jointStationaryCompact_isCompact m)
    (fun z hz => (quadraticChartDensity_contDiffAt m
      (jointStationaryCompact_subset m hz).2).comp z contDiffAt_snd) K
  exact ⟨Q,R,hQ,hR,fun j hj z hz => ⟨hQb j hj z hz,hRb j hj z hz⟩⟩

/-- All mixed chart derivatives cost only their total order in the original
symbol scale. The direction parameter is differentiated in ambient space. -/
theorem joint_stationary_amplitude_budget (m K : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ B : Space (m+3) → ℂ,
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ K, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ j ≤ K, ∀ z ∈ jointStationaryCompact m,
        ‖iteratedFDeriv ℝ j (unmaskedStationaryAmplitude m B) z‖ ≤ A*C*D^K := by
  obtain ⟨Q,R,hQ,hR,hgeometry⟩ := joint_stationary_geometry_bounds m K
  let a : ℕ → ℝ := fun j => mixedCompositionBudget (fun _ => Q) j
  have ha (j : ℕ) : 0 ≤ a j := mixedCompositionBudget_nonneg (fun _ => hQ) j
  let H := ∑ j ∈ Finset.range (K+1), a j
  have hH : 0 ≤ H := Finset.sum_nonneg (fun j _ => ha j)
  have haH (j : ℕ) (hj : j ≤ K) : a j ≤ H :=
    Finset.single_le_sum (fun j _ => ha j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  refine ⟨2^K*R*H,by positivity,?_⟩
  intro B hB C D hC hD hb j hj z hz
  have hzU := jointStationaryCompact_subset m hz
  have hCE : 0 ≤ C*D^K := mul_nonneg hC (pow_nonneg (zero_le_one.trans hD) K)
  let w : Sphere (m+3) := ⟨jointStationaryChart m z,by
    rw [mem_sphere,dist_zero_right]
    exact jointStationaryChart_norm m z hzU.2.le⟩
  have hcomp (i : ℕ) (hi : i ≤ j) :
      ‖iteratedFDeriv ℝ i (B ∘ jointStationaryChart m) z‖ ≤ H*(C*D^K) := by
    have hh := mixed_composition_derivative_bound (B := fun _ => Q) (D := 1)
      (jointStationaryChart_contDiffAt m hzU)
      hB.contDiffAt hCE i
      (fun l hl => (hb l ((hl.trans hi).trans hj) w).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD ((hl.trans hi).trans hj)) hC))
      (fun l _ hl => by simpa only [one_pow,mul_one] using
        (hgeometry l ((hl.trans hi).trans hj) z hz).1)
    exact hh.trans (by
      simp only [one_pow,mul_one]
      exact mul_le_mul_of_nonneg_right (haH i (hi.trans hj)) hCE)
  have hh := mixed_product_uniform_bound_at
    ((quadraticChartDensity_contDiffAt m hzU.2).comp z contDiffAt_snd)
    (hB.contDiffAt.comp z (jointStationaryChart_contDiffAt m hzU))
    hR (mul_nonneg hH hCE) j
    (fun i hi => (hgeometry i (hi.trans hj) z hz).2) hcomp
  change ‖iteratedFDeriv ℝ j (fun z => quadraticChartDensity m z.2 *
    (B ∘ jointStationaryChart m) z) z‖ ≤ _
  apply hh.trans
  calc
    _ ≤ 2^K*R*(H*(C*D^K)) := by gcongr; norm_num
    _ = _ := by ring

end Falconer

end OAI
