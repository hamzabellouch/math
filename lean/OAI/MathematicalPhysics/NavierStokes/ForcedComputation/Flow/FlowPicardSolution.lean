import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.FlowPicardSmooth

namespace OAI

/-! Identification of the local implicit Picard family with an actual flow.
The short-time uniqueness proof is a norm estimate in the compact path space. -/

noncomputable section
namespace ForcedComputation.Flow
open Set Filter
open scoped Topology ContDiff NNReal

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NormedSpace ℝ E] in
theorem postcompose_norm_sub_le (Z : C(E, E)) {L : ℝ≥0}
    (hZ : LipschitzWith L Z) (γ η : C(UnitTime, E)) :
    ‖postcompose Z γ - postcompose Z η‖ ≤ (L : ℝ) * ‖γ - η‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg L.coe_nonneg (norm_nonneg _))).mpr
  intro s
  exact (hZ.norm_sub_le (γ s) (η s)).trans
    (mul_le_mul_of_nonneg_left ((γ - η).norm_coe_le_norm s) L.coe_nonneg)

omit [FiniteDimensional ℝ E] in
theorem picard_solution_unique (Z : C(E, E)) {L : ℝ≥0}
    (hZ : LipschitzWith L Z) {τ : ℝ} (hτ : |τ| * (L : ℝ) < 1)
    (x : E) {γ η : C(UnitTime, E)}
    (hγ : picardResidual Z ((τ, x), γ) = 0)
    (hη : picardResidual Z ((τ, x), η) = 0) : γ = η := by
  have hγ' : γ - ContinuousLinearMap.const ℝ UnitTime x =
      τ • primitivePathL (postcompose Z γ) := sub_eq_zero.mp hγ
  have hη' : η - ContinuousLinearMap.const ℝ UnitTime x =
      τ • primitivePathL (postcompose Z η) := sub_eq_zero.mp hη
  have he : γ - η = τ • primitivePathL (postcompose Z γ - postcompose Z η) := by
    rw [map_sub, smul_sub, ← hγ', ← hη']
    abel
  have hb : ‖γ - η‖ ≤ (|τ| * (L : ℝ)) * ‖γ - η‖ := by
    calc
      ‖γ - η‖ = |τ| * ‖primitivePathL (postcompose Z γ - postcompose Z η)‖ := by
        rw [he, norm_smul, Real.norm_eq_abs]
      _ ≤ |τ| * ‖postcompose Z γ - postcompose Z η‖ :=
        mul_le_mul_of_nonneg_left (primitivePath_norm _) (abs_nonneg τ)
      _ ≤ |τ| * ((L : ℝ) * ‖γ - η‖) :=
        mul_le_mul_of_nonneg_left (postcompose_norm_sub_le Z hZ γ η) (abs_nonneg τ)
      _ = _ := by ring
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hn := norm_nonneg (γ - η)
  nlinarith

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
def orbitPath {Z : E → E} {Ψ : ℝ → E → E}
    (hΨ : ∀ t x, HasDerivAt (fun s => Ψ s x) (Z (Ψ t x)) t)
    (τ : ℝ) (x : E) : C(UnitTime, E) :=
  ⟨fun s => Ψ (τ * s.1) x,
    (continuous_iff_continuousAt.mpr fun t => (hΨ t x).continuousAt).comp
      (continuous_const.mul continuous_subtype_val)⟩

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
@[simp] theorem orbitPath_apply {Z : E → E} {Ψ : ℝ → E → E}
    (hΨ : ∀ t x, HasDerivAt (fun s => Ψ s x) (Z (Ψ t x)) t)
    (τ : ℝ) (x : E) (s : UnitTime) : orbitPath hΨ τ x s = Ψ (τ * s.1) x := rfl

omit [FiniteDimensional ℝ E] in
theorem orbitPath_picard (Z : C(E, E)) {Ψ : ℝ → E → E}
    (hΨ : ∀ t x, HasDerivAt (fun s => Ψ s x) (Z (Ψ t x)) t)
    (hzero : ∀ x, Ψ 0 x = x) (τ : ℝ) (x : E) :
    picardResidual Z ((τ, x), orbitPath hΨ τ x) = 0 := by
  let γ := orbitPath hΨ τ x
  have hc : Continuous (fun s : ℝ => Ψ (τ * s) x) :=
    (continuous_iff_continuousAt.mpr fun t => (hΨ t x).continuousAt).comp
      (continuous_const.mul continuous_id)
  have hd (s : ℝ) : HasDerivAt (fun r => Ψ (τ * r) x)
      (τ • Z (Ψ (τ * s) x)) s := by
    simpa only [Function.comp_def, mul_one] using
      (hΨ (τ * s) x).scomp s ((hasDerivAt_id s).const_mul τ)
  ext t
  change Ψ (τ * t.1) x - x - τ •
    (∫ s in (0 : ℝ)..t.1, extendPath (postcompose Z γ) s) = 0
  have he : (∫ s in (0 : ℝ)..t.1, extendPath (postcompose Z γ) s) =
      ∫ s in (0 : ℝ)..t.1, Z (Ψ (τ * s) x) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := by
      rw [uIcc_of_le t.2.1] at hs
      exact ⟨hs.1, hs.2.trans t.2.2⟩
    simp only [extendPath_apply, postcompose, ContinuousMap.comp_apply,
      projIcc_of_mem zero_le_one hs', γ, orbitPath_apply]
  rw [he]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hd s) (((Z.continuous.comp hc).const_smul τ).intervalIntegrable 0 t.1)
  rw [intervalIntegral.integral_smul, mul_zero, hzero] at hi
  exact sub_eq_zero.mpr hi.symm

/-- Joint smoothness in short elapsed time and the initial point. -/
theorem flow_contDiffAt_short (Z : C(E, E))
    (hZ : ContDiff ℝ ∞ (Z : E → E)) {L : ℝ≥0} (hL : LipschitzWith L Z)
    {Ψ : ℝ → E → E}
    (hΨ : ∀ t x, HasDerivAt (fun s => Ψ s x) (Z (Ψ t x)) t)
    (hzero : ∀ x, Ψ 0 x = x) (τ : ℝ) (x : E)
    (hτ : |τ| * (L : ℝ) < 1) :
    ContDiffAt ℝ ∞ (fun p : ℝ × E => Ψ p.1 p.2) (τ, x) := by
  let γ := orbitPath hΨ τ x
  obtain ⟨Γ, hΓ, _, hΓeq⟩ := exists_local_picard_family Z hZ L.coe_nonneg
    (fun _ => norm_fderiv_le_of_lipschitz ℝ hL) hτ x γ
    (orbitPath_picard Z hΨ hzero τ x)
  let e : UnitTime := ⟨1, by norm_num⟩
  have hs : ContDiffAt ℝ ∞ (fun p => Γ p e) (τ, x) :=
    (ContinuousMap.evalCLM ℝ e : C(UnitTime, E) →L[ℝ] E).contDiff.contDiffAt.comp (τ, x) hΓ
  have hn : ∀ᶠ p : ℝ × E in 𝓝 (τ, x), |p.1| * (L : ℝ) < 1 :=
    (isOpen_lt (continuous_fst.abs.mul continuous_const) continuous_const).mem_nhds hτ
  have he : (fun p => Γ p e) =ᶠ[𝓝 (τ, x)] fun p => Ψ p.1 p.2 := by
    filter_upwards [hΓeq, hn] with p hp hsmall
    have hu := picard_solution_unique Z hL hsmall p.2 hp
      (orbitPath_picard Z hΨ hzero p.1 p.2)
    have hv := congrArg (fun η : C(UnitTime, E) => η e) hu
    simpa only [orbitPath_apply, e, mul_one] using hv
  exact hs.congr_of_eventuallyEq he.symm

end ForcedComputation.Flow

end

end OAI
