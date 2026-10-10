import Mathlib
import OAI.Geometry.PrescribedPotential.VariablePoisson

namespace OAI

/-! Metric Localization. -/

section

 

noncomputable section
open Filter Topology Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.Elementwise ContDiff

namespace MetricLocalization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ}

lemma contDiffOn_matrix_det {U : Set E} {H : E → Matrix (Fin n) (Fin n) ℂ}
    (hH : ContDiffOn ℝ ∞ H U) : ContDiffOn ℝ ∞ (fun z => (H z).det) U := by
  classical
  simp_rw [Matrix.det_apply']
  apply ContDiffOn.sum
  intro σ _
  apply contDiffOn_const.mul
  apply contDiffOn_prod
  intro i _
  exact contDiffOn_pi.mp (contDiffOn_pi.mp hH (σ i)) i

lemma contDiffOn_matrix_adjugate {U : Set E} {H : E → Matrix (Fin n) (Fin n) ℂ}
    (hH : ContDiffOn ℝ ∞ H U) : ContDiffOn ℝ ∞ (fun z => (H z).adjugate) U := by
  classical
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  simp_rw [Matrix.adjugate_apply]
  apply contDiffOn_matrix_det
  apply contDiffOn_pi.mpr
  intro k
  apply contDiffOn_pi.mpr
  intro l
  by_cases hk : k = j
  · subst k
    simp only [Matrix.updateRow_self]
    exact contDiffOn_const
  · simp only [Matrix.updateRow_ne hk]
    exact contDiffOn_pi.mp (contDiffOn_pi.mp hH k) l

lemma contDiffOn_matrix_inv {U : Set E} {H : E → Matrix (Fin n) (Fin n) ℂ}
    (hH : ContDiffOn ℝ ∞ H U) (hh : ∀ x ∈ U, (H x).det ≠ 0) :
    ContDiffOn ℝ ∞ (fun z => (H z)⁻¹) U := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv']
  exact ((contDiffOn_matrix_det hH).inv hh).smul (contDiffOn_matrix_adjugate hH)

lemma trace_coefficient_smooth {U : Set (EllipticKernel.EC n)}
    {H : EllipticKernel.EC n → Matrix (Fin n) (Fin n) ℂ}
    (hH : ContDiffOn ℝ ∞ H U) (hh : ∀ x ∈ U, (H x).PosDef)
    (B : EllipticKernel.Bilin (EllipticKernel.EC n)) :
    ContDiffOn ℝ ∞ (fun z => (EllipticKernel.traceBilin (H z) B : ℂ)) U := by
  have hi := contDiffOn_matrix_inv hH (fun x hx => ne_of_gt (hh x hx).det_pos)
  have hir : ContDiffOn ℝ ∞
      (fun z => ((H z)⁻¹ * PotentialKaehler.hermitianPartMatrix
        (EllipticKernel.pullBilin B)).trace.re) U := by
    apply Complex.reCLM.contDiff.comp_contDiffOn
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    apply ContDiffOn.sum
    intro i _
    apply ContDiffOn.sum
    intro j _
    exact (contDiffOn_pi.mp (contDiffOn_pi.mp hi i) j).mul contDiffOn_const
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn hir

section Extension
variable [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma smooth_bump_smul {x : E} (ψ : ContDiffBump x) (f : E → F)
    (hf : ∀ y ∈ tsupport ψ, ContDiffAt ℝ ∞ f y) :
    ContDiff ℝ ∞ (fun y => ψ y • f y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ tsupport ψ
  · exact ψ.contDiff.contDiffAt.smul (hf y hy)
  · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp [hz]

 

lemma small_smooth_extension {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f U) (hfx : f x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : E → F, ContDiff ℝ ∞ a ∧ HasCompactSupport a ∧
      tsupport a ⊆ U ∧ (a =ᶠ[𝓝 x] f) ∧ ∀ y, ‖a y‖ ≤ ε := by
  have hnear : ∀ᶠ y in 𝓝 x, ‖f y‖ < ε := by
    have hc := (hf x hx).continuousWithinAt.continuousAt (hU.mem_nhds hx)
    exact hc.norm.eventually (gt_mem_nhds (by simpa [hfx] using hε))
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem (hU.mem_nhds hx) hnear)
  let ψ : ContDiffBump x :=
    { rIn := r / 2, rOut := r, rIn_pos := half_pos hr, rIn_lt_rOut := half_lt_self hr }
  let a : E → F := fun y => ψ y • f y
  have hsupp : tsupport a ⊆ tsupport ψ := tsupport_smul_subset_left _ _
  have hψ : tsupport ψ ⊆ U ∩ {y | ‖f y‖ < ε} := by
    simpa only [ψ, ContDiffBump.tsupport_eq] using hsub
  refine ⟨a, ?_, ?_, hsupp.trans (hψ.trans inter_subset_left), ?_, ?_⟩
  · apply smooth_bump_smul ψ f
    intro y hy
    exact (hf y (hψ hy).1).contDiffAt (hU.mem_nhds (hψ hy).1)
  · exact ψ.hasCompactSupport.smul_right
  · filter_upwards [ψ.eventuallyEq_one] with y hy
    simp [a, hy]
  · intro y
    by_cases hy : y ∈ tsupport ψ
    · have hf' := (hψ hy).2
      calc
        ‖a y‖ = |ψ y| * ‖f y‖ := norm_smul _ _
        _ = ψ y * ‖f y‖ := by rw [abs_of_nonneg ψ.nonneg]
        _ ≤ 1 * ‖f y‖ := mul_le_mul_of_nonneg_right ψ.le_one (norm_nonneg _)
        _ ≤ ε := by simpa using hf'.le
    · have hz : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [a, hz, hε.le]

end Extension
end MetricLocalization

namespace MetricLocalization
open EllipticKernel FrozenPoisson SobolevChart
open scoped BoundedContinuousFunction
variable {n : ℕ} {ι : Type*} [Fintype ι]

 

theorem local_coefficient_extension {U : Set (EC n)} (hU : IsOpen U)
    (H : EC n → Matrix (Fin n) (Fin n) ℂ) (hH : ContDiffOn ℝ ∞ H U)
    (hh : ∀ y ∈ U, (H y).PosDef) {x : EC n} (hx : x ∈ U) (v : ι → EC n) :
    ∃ a : ι → ι → EC n →ᵇ ℂ,
      (∀ i j, (a i j : EC n → ℂ).HasTemperateGrowth) ∧
      (∀ i j, HasCompactSupport (a i j : EC n → ℂ)) ∧
      perturbationBound v a * ellipticBound (H x) (hh x hx) < 1 ∧
      ∀ᶠ y in 𝓝 x, ∀ i j,
        a i j y = (traceBilin (H y) (rankTwo (v i) (v j)) : ℂ) -
          (traceBilin (H x) (rankTwo (v i) (v j)) : ℂ) := by
  classical
  let C := ellipticBound (H x) (hh x hx)
  have hC : 0 < C := ellipticBound_pos _ _
  let Q : ℝ := ∑ i, ∑ j, (2 * Real.pi)^2 * ‖v i‖ * ‖v j‖
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  let ε : ℝ := 1 / (1 + Q * C)
  have hden : 0 < 1 + Q * C := by positivity
  have hε : 0 < ε := one_div_pos.mpr hden
  let F : EC n → ι → ι → ℂ := fun y i j =>
    (traceBilin (H y) (rankTwo (v i) (v j)) : ℂ) -
      (traceBilin (H x) (rankTwo (v i) (v j)) : ℂ)
  have hF : ContDiffOn ℝ ∞ F U := by
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    exact (trace_coefficient_smooth hH hh _).sub contDiffOn_const
  have hFx : F x = 0 := by ext i j; exact sub_self _
  obtain ⟨b, hb, hbc, _, hbe, hbn⟩ := small_smooth_extension hU hx F hF hFx hε
  have hbij i j : ContDiff ℝ ∞ (fun y => b y i j) :=
    contDiff_pi.mp (contDiff_pi.mp hb i) j
  have hbijc i j : HasCompactSupport (fun y => b y i j) :=
    hbc.comp_left (g := fun M : ι → ι → ℂ => M i j) rfl
  have hbound i j y : ‖b y i j‖ ≤ ε :=
    (norm_le_pi_norm (b y i) j).trans ((norm_le_pi_norm (b y) i).trans (hbn y))
  let a : ι → ι → EC n →ᵇ ℂ := fun i j =>
    BoundedContinuousFunction.ofNormedAddCommGroup (fun y => b y i j)
      (hbij i j).continuous ε (hbound i j)
  have han i j : ‖a i j‖ ≤ ε :=
    (BoundedContinuousFunction.norm_le hε.le).mpr (hbound i j)
  have hp : perturbationBound v a ≤ ε * Q := by
    simp only [perturbationBound, Q, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_right (han i j) (by positivity)
  refine ⟨a, fun i j => (hbijc i j).hasTemperateGrowth (hbij i j), hbijc, ?_, ?_⟩
  · change perturbationBound v a * C < 1
    calc
      _ ≤ (ε * Q) * C := mul_le_mul_of_nonneg_right hp hC.le
      _ = (Q * C) / (1 + Q * C) := by dsimp [ε]; ring
      _ < 1 := (div_lt_one hden).mpr (by linarith)
  · filter_upwards [hbe] with y hy
    intro i j
    exact congrFun (congrFun hy i) j

end MetricLocalization

namespace Anticanonical.SourceSmooth
open EllipticKernel FrozenPoisson SobolevChart
open scoped BoundedContinuousFunction
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

 

theorem KaehlerMetric.local_inverse_coefficients (g : KaehlerMetric A)
    (i : Fin A.count) {x : EC d} (hx : coordinateEquiv d x ∈ (A.chart i).target) :
    let b := stdOrthonormalBasis ℝ (EC d)
    let H := fun y => g.matrix i (coordinateEquiv d y)
    ∃ a : Fin (Module.finrank ℝ (EC d)) → Fin (Module.finrank ℝ (EC d)) → EC d →ᵇ ℂ,
      (∀ k l, (a k l : EC d → ℂ).HasTemperateGrowth) ∧
      (∀ k l, HasCompactSupport (a k l : EC d → ℂ)) ∧
      perturbationBound b a * ellipticBound (H x) (g.positive i _ hx) < 1 ∧
      ∀ᶠ y in 𝓝 x, ∀ k l,
        a k l y = (traceBilin (H y) (rankTwo (b k) (b l)) : ℂ) -
          (traceBilin (H x) (rankTwo (b k) (b l)) : ℂ) := by
  have hs := (g.smooth i).comp (coordinateEquiv d).contDiff.contDiffOn (fun _ h => h)
  exact MetricLocalization.local_coefficient_extension
    ((A.chart i).open_target.preimage (coordinateEquiv d).continuous)
    _ hs (fun y hy => g.positive i _ hy) hx _

end Anticanonical.SourceSmooth

end
end

end OAI
