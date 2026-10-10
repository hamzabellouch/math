import OAI.Geometry.CylinderCovering.Nilpotent.FieldDefinitions

namespace OAI

open Set RuledApproximation Filter
open scoped Topology
open scoped ContDiff

noncomputable section
namespace CylinderCovering.Nilpotent

private theorem hasFDerivAt_pair {f g : Plane → ℝ} {f' g' : Plane →L[ℝ] ℝ}
    {b : Plane} (hf : HasFDerivAt f f' b) (hg : HasFDerivAt g g' b) :
    HasFDerivAt (fun z => vec2 (f z) (g z))
      (f'.smulRight (vec2 1 0) + g'.smulRight (vec2 0 1)) b := by
  have heq : (fun z => vec2 (f z) (g z)) =
      (fun z => f z • vec2 1 0 + g z • vec2 0 1) := by
    funext z
    ext i
    fin_cases i <;> simp [vec2]
  rw [heq]
  exact (hf.smul_const _).add (hg.smul_const _)

theorem signedField_hasFDerivAt (σ k : ℝ) {b : Plane} (hb : b 1 ≠ 0) :
    HasFDerivAt (signedField σ k) (angularDerivative σ k b) b := by
  let P : Plane →L[ℝ] ℝ := EuclideanSpace.proj 0
  let Q : Plane →L[ℝ] ℝ := EuclideanSpace.proj 1
  have hp := P.hasFDerivAt (x := b)
  have hq := Q.hasFDerivAt (x := b)
  have hquot := hp.mul ((hasDerivAt_inv hb).comp_hasFDerivAt b hq)
  have hfirst := ((hquot.pow 2).const_add 1).const_mul (σ * k / 4)
  have hsecond := hquot.const_mul (σ * k / 2)
  have hpairs := hasFDerivAt_pair hfirst hsecond
  convert hpairs using 1
  · funext z
    ext i
    fin_cases i <;> simp [signedField, v, w, vec2, P, Q, div_eq_mul_inv] <;> ring
  · ext z i
    fin_cases i <;>
      simp [angularDerivative, P, Q, vec2, ContinuousLinearMap.smulRight_apply] <;>
      field_simp [hb] <;> ring

theorem angularDerivative_square_zero (σ k : ℝ) (b : Plane) :
    (angularDerivative σ k b).comp (angularDerivative σ k b) = 0 := by
  ext z i
  fin_cases i <;>
    simp [angularDerivative, vec2, ContinuousLinearMap.smulRight_apply]

theorem signedField_fderiv_square_zero (σ k : ℝ) {b : Plane} (hb : b 1 ≠ 0) :
    (fderiv ℝ (signedField σ k) b).comp (fderiv ℝ (signedField σ k) b) = 0 := by
  rw [(signedField_hasFDerivAt σ k hb).fderiv]
  exact angularDerivative_square_zero σ k b

theorem signedField_contDiffAt (σ k : ℝ) {b : Plane} (hb : b 1 ≠ 0) :
    ContDiffAt ℝ ∞ (signedField σ k) b := by
  have hp : ContDiffAt ℝ ∞ (fun z : Plane => z 0) b :=
    (EuclideanSpace.proj 0 : Plane →L[ℝ] ℝ).contDiff.contDiffAt
  have hq : ContDiffAt ℝ ∞ (fun z : Plane => z 1) b :=
    (EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).contDiff.contDiffAt
  have hquot : ContDiffAt ℝ ∞ (fun z : Plane => z 0 / z 1) b := hp.div hq hb
  have hf : ContDiffAt ℝ ∞ (fun z : Plane => σ * k * v (z 0 / z 1)) b := by
    unfold v
    fun_prop
  have hg : ContDiffAt ℝ ∞ (fun z : Plane => σ * k * w (z 0 / z 1)) b := by
    unfold w
    fun_prop
  have heq : signedField σ k = (fun z : Plane =>
      (σ * k * v (z 0 / z 1)) • vec2 1 0 +
      (σ * k * w (z 0 / z 1)) • vec2 0 1) := by
    funext z
    ext i
    fin_cases i <;> simp [signedField, vec2]
  rw [heq]
  exact (hf.smul contDiffAt_const).add (hg.smul contDiffAt_const)

theorem signedField_contDiffOn (σ k : ℝ) :
    ContDiffOn ℝ ∞ (signedField σ k) {b : Plane | 0 < b 1} := by
  intro b hb
  exact (signedField_contDiffAt σ k (ne_of_gt hb)).contDiffWithinAt

theorem signedField_smoothNear (σ k : ℝ) {D : Set Plane}
    (hD : ∀ b ∈ D, 0 < b 1) : SmoothNear ∞ D (signedField σ k) := by
  refine ⟨{b : Plane | 0 < b 1}, ?_, hD, signedField_contDiffOn σ k⟩
  exact isOpen_lt continuous_const (EuclideanSpace.proj 1).continuous

theorem signedField_on_ray (σ k p t : ℝ) (ht : t ≠ 0) :
    signedField σ k (vec2 (p * t) t) = vec2 (σ * k * v p) (σ * k * w p) := by
  simp [signedField, vec2, ht]

theorem angularDerivative_on_ray (σ k p t : ℝ) (ht : t ≠ 0) (z : Plane) :
    angularDerivative σ k (vec2 (p * t) t) z =
      (σ * k / (2 * t) * (z 0 - p * z 1)) • vec2 p 1 := by
  simp [angularDerivative, vec2, ht, smul_smul]

theorem continuous_extension_ray_value {σ k : ℝ} {F : Plane → Plane}
    (hF : ContinuousAt F 0)
    (hagree : ∀ b : Plane, 0 < b 1 → F b = signedField σ k b) (p : ℝ) :
    F 0 = vec2 (σ * k * v p) (σ * k * w p) := by
  have hpath : Tendsto (fun t : ℝ => t • vec2 p 1) (𝓝[>] 0) (𝓝 (0 : Plane)) := by
    have hc : Continuous (fun t : ℝ => t • vec2 p 1) := continuous_id.smul continuous_const
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hlimit := hF.tendsto.comp hpath
  have hevent : (fun t : ℝ => F (t • vec2 p 1)) =ᶠ[𝓝[>] 0]
      (fun _ => vec2 (σ * k * v p) (σ * k * w p)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := ht
    rw [hagree _ (by simpa [vec2] using htpos)]
    have hpoint : t • vec2 p 1 = vec2 (p * t) t := by
      ext i
      fin_cases i <;> simp [vec2]
      ring
    rw [hpoint]
    exact signedField_on_ray σ k p t htpos.ne'
  have hconstant : Tendsto (fun t : ℝ => F (t • vec2 p 1)) (𝓝[>] 0)
      (𝓝 (vec2 (σ * k * v p) (σ * k * w p))) := by
    exact tendsto_const_nhds.congr' hevent.symm
  exact tendsto_nhds_unique hlimit hconstant

theorem no_continuous_extension {σ k : ℝ} (hκ : σ * k ≠ 0) :
    ¬ ∃ F : Plane → Plane, ContinuousAt F 0 ∧
      ∀ b : Plane, 0 < b 1 → F b = signedField σ k b := by
  rintro ⟨F, hF, hagree⟩
  have h0 := continuous_extension_ray_value hF hagree 0
  have h1 := continuous_extension_ray_value hF hagree 1
  have heq := congrArg (fun b : Plane => b 1) (h0.symm.trans h1)
  simp [vec2, w] at heq
  rcases heq with hσ | hk
  · exact hκ (by simp [hσ])
  · exact hκ (by simp [hk])

theorem signedField_not_continuousAt_apex {σ k : ℝ} (hκ : σ * k ≠ 0) :
    ¬ ContinuousAt (signedField σ k) 0 := by
  intro h
  exact no_continuous_extension hκ ⟨signedField σ k, h, fun _ _ => rfl⟩

end CylinderCovering.Nilpotent

end

end OAI
