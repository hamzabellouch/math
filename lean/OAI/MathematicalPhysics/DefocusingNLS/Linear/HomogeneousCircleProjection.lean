import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDoubleCircle
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent

namespace OAI

/-! # Nested resolvent circles

The product identity is obtained from the resolvent identity and two scalar
Cauchy integrals. It supplies idempotence once nearby resolvent circles are
identified by the annulus theorem.
-/

open Complex Set

namespace DefocusingNLS

private theorem circleIntegral_inverse_left_outside {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    {r : ℝ} (hr : 0 ≤ r) {w : ℂ} (hw : r < ‖w‖) (x : A) :
    (∮ z in C(0, r), (w - z)⁻¹ • x) = 0 := by
  have hn (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) r) : w - z ≠ 0 := by
    have hz' : ‖z‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    intro he
    rw [← sub_eq_zero.mp he] at hz'
    exact (not_le_of_gt hw) hz'
  have hd : DifferentiableOn ℂ (fun z : ℂ => (w - z)⁻¹ • x)
      (Metric.closedBall (0 : ℂ) r) := by
    intro z hz
    exact ((((differentiableAt_const w).sub differentiableAt_id).inv (hn z hz)).smul
      (differentiableAt_const x)).differentiableWithinAt
  exact (hd.diffContOnCl_ball (Subset.refl _)).circleIntegral_eq_zero hr

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem finiteDimensional_range_of_compact_projection (P : E →L[ℂ] E)
    (hP : IsIdempotentElem P) (hc : IsCompactOperator P) :
    FiniteDimensional ℂ P.range := by
  have hclosed := ContinuousLinearMap.IsIdempotentElem.isClosed_range hP
  have hkeep : ∀ x ∈ P.range, P.toLinearMap x ∈ P.range :=
    fun x _ => ⟨x, rfl⟩
  have hr := IsCompactOperator.restrict (f := P.toLinearMap) hc hkeep hclosed
  apply FiniteDimensional.of_isCompactOperator_id (𝕜 := ℂ)
  convert hr using 1
  funext x
  apply Subtype.ext
  obtain ⟨y, hy⟩ := x.property
  change (x : E) = P (x : E)
  rw [← hy]
  exact (congrArg (fun L : E →L[ℂ] E => L y) hP).symm

private theorem resolvent_continuousOn_circle (T : E →L[ℂ] E) {r : ℝ}
    (hres : ∀ z : ℂ, ‖z‖ = r → z ∈ resolventSet ℂ T) :
    ContinuousOn (resolvent T) (Metric.sphere (0 : ℂ) r) := by
  intro z hz
  exact ((spectrum.hasDerivAt_resolvent_const_left (hres z
    (by simpa only [Metric.mem_sphere, dist_zero_right] using hz))).continuousAt).continuousWithinAt

theorem circleResolventOperator_mul_nested (T : E →L[ℂ] E)
    {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hresr : ∀ z : ℂ, ‖z‖ = r → z ∈ resolventSet ℂ T)
    (hresR : ∀ z : ℂ, ‖z‖ = R → z ∈ resolventSet ℂ T) :
    circleResolventOperator T r * circleResolventOperator T R =
      circleResolventOperator T r := by
  let A := E →L[ℂ] E
  let c : ℂ := 2 * Real.pi * I
  let Qr : A := ∮ z in C(0, r), resolvent T z
  let QR : A := ∮ w in C(0, R), resolvent T w
  let H : ℂ → A := fun z => ∮ w in C(0, R), (w - z)⁻¹ • resolvent T w
  have hR : 0 ≤ R := hr.trans hrR.le
  have hcr := resolvent_continuousOn_circle T hresr
  have hcR := resolvent_continuousOn_circle T hresR
  have hir := circleIntegrable_resolvent T hr hresr
  have hiR := circleIntegrable_resolvent T hR hresR
  have hn {z w : ℂ} (hz : z ∈ Metric.sphere (0 : ℂ) r)
      (hw : w ∈ Metric.sphere (0 : ℂ) R) : w ≠ z := by
    have hzr : ‖z‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
    have hwR : ‖w‖ = R := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
    intro he
    rw [he, hzr] at hwR
    exact hrR.ne hwR
  have hinner (z : ℂ) (hz : z ∈ Metric.sphere (0 : ℂ) r) :
      H z = c • resolvent T z - resolvent T z * QR := by
    have hzr : ‖z‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
    have hinv : ContinuousOn (fun w : ℂ => (w - z)⁻¹) (Metric.sphere 0 R) :=
      (continuousOn_id.sub continuousOn_const).inv₀ fun w hw => sub_ne_zero.mpr (hn hz hw)
    have hif : CircleIntegrable (fun w : ℂ => (w - z)⁻¹ • resolvent T z) 0 R :=
      (hinv.smul continuousOn_const).circleIntegrable hR
    have hig : CircleIntegrable (fun w : ℂ => (w - z)⁻¹ • resolvent T w) 0 R :=
      (hinv.smul hcR).circleIntegrable hR
    have he : resolvent T z * QR = c • resolvent T z - H z := by
      calc
        resolvent T z * QR = ∮ w in C(0, R), resolvent T z * resolvent T w := by
          have hmap := circleIntegral_map_clm
            (ContinuousLinearMap.mul ℂ A (resolvent T z)) hiR
          change (∮ w in C(0, R), resolvent T z * resolvent T w) =
            resolvent T z * QR at hmap
          exact hmap.symm
        _ = ∮ w in C(0, R), (w - z)⁻¹ • resolvent T z -
            (w - z)⁻¹ • resolvent T w := by
          apply circleIntegral.integral_congr hR
          intro w hw
          have hwR : ‖w‖ = R := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
          dsimp only
          rw [resolvent_first_identity T (hresr z hzr) (hresR w hwR) (hn hz hw), smul_sub]
        _ = c • resolvent T z - H z := by
          rw [circleIntegral.integral_sub hif hig, circleIntegral.integral_smul_const,
            circleIntegral.integral_sub_inv_of_mem_ball
              (by simpa only [Metric.mem_ball, dist_zero_right, hzr] using hrR)]
    exact (eq_sub_iff_add_eq.mpr (by
      have hh := eq_sub_iff_add_eq.mp he
      simpa only [add_comm] using hh))
  have hgc : ContinuousOn (fun p : ℂ × ℂ => (p.2 - p.1)⁻¹ • resolvent T p.2)
      (Metric.sphere (0 : ℂ) r ×ˢ Metric.sphere (0 : ℂ) R) := by
    intro p hp
    have hs : ContinuousAt (fun p : ℂ × ℂ => (p.2 - p.1)⁻¹) p :=
      (continuous_snd.sub continuous_fst).continuousAt.inv₀
        (sub_ne_zero.mpr (hn hp.1 hp.2))
    have hres : ContinuousAt (fun p : ℂ × ℂ => resolvent T p.2) p :=
      (spectrum.hasDerivAt_resolvent_const_left (hresR p.2
        (by simpa only [Metric.mem_sphere, dist_zero_right] using hp.2))).continuousAt.comp
          continuous_snd.continuousAt
    exact (hs.smul hres).continuousWithinAt
  have hHzero : (∮ z in C(0, r), H z) = 0 := by
    change (∮ z in C(0, r), ∮ w in C(0, R), (w - z)⁻¹ • resolvent T w) = 0
    rw [circleIntegral_swap hr hR hgc]
    calc
      (∮ w in C(0, R), ∮ z in C(0, r), (w - z)⁻¹ • resolvent T w) =
          ∮ w in C(0, R), (0 : A) := by
        apply circleIntegral.integral_congr hR
        intro w hw
        apply circleIntegral_inverse_left_outside hr
        have hwR : ‖w‖ = R := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
        simpa only [hwR] using hrR
      _ = 0 := by simp [circleIntegral]
  have hic : CircleIntegrable (fun z => c • resolvent T z) 0 r := by
    apply ContinuousOn.circleIntegrable hr
    intro z hz
    exact ((show ContinuousAt (fun _ : ℂ => c) z from continuousAt_const).smul
      (spectrum.hasDerivAt_resolvent_const_left (hresr z
        (by simpa only [Metric.mem_sphere, dist_zero_right] using hz))).continuousAt).continuousWithinAt
  have hip : CircleIntegrable (fun z => resolvent T z * QR) 0 r :=
    (hcr.mul continuousOn_const).circleIntegrable hr
  have he := circleIntegral.integral_congr hr hinner
  have hmap := circleIntegral_map_clm ((ContinuousLinearMap.mul ℂ A).flip QR) hir
  change (∮ z in C(0, r), resolvent T z * QR) = Qr * QR at hmap
  rw [he, circleIntegral.integral_sub hic hip, circleIntegral.integral_smul, hmap] at hHzero
  have hp : Qr * QR = c • Qr := (sub_eq_zero.mp hHzero).symm
  have hc : c ≠ 0 := by simp [c, Real.pi_ne_zero, I_ne_zero]
  change (c⁻¹ • Qr) * (c⁻¹ • QR) = c⁻¹ • Qr
  rw [smul_mul_smul_comm, hp, smul_smul]
  congr 1
  field_simp

theorem circleResolventOperator_idempotent_of_annulus (T : E →L[ℂ] E)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hres : ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R → z ∈ resolventSet ℂ T) :
    circleResolventOperator T r * circleResolventOperator T r =
      circleResolventOperator T r := by
  have he := circleResolventOperator_eq_of_annulus T hr hrR.le hres
  calc
    circleResolventOperator T r * circleResolventOperator T r =
        circleResolventOperator T r * circleResolventOperator T R := by rw [he]
    _ = circleResolventOperator T r := circleResolventOperator_mul_nested T hr.le hrR
      (fun z hz => hres z hz.ge (hz.le.trans hrR.le))
      (fun z hz => hres z (hrR.le.trans hz.ge) hz.le)

/-- A compact spectrum disjoint from a circle is disjoint from a slightly
larger closed annulus as well. -/
theorem exists_resolvent_annulus (T : E →L[ℂ] E) {r : ℝ}
    (hres : ∀ z : ℂ, ‖z‖ = r → z ∈ resolventSet ℂ T) :
    ∃ R : ℝ, r < R ∧
      ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R → z ∈ resolventSet ℂ T := by
  let S : Set ℝ := norm '' spectrum ℂ T
  have hclosed : IsClosed S := ((spectrum.isCompact T).image continuous_norm).isClosed
  have hrS : r ∉ S := by
    rintro ⟨z, hz, hzr⟩
    exact (spectrum.notMem_iff.mpr (hres z hzr)) hz
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hrS)
  refine ⟨r + ε / 2, by linarith, fun z hz hR => ?_⟩
  apply spectrum.notMem_iff.mp
  intro hspec
  have hn : ‖z‖ ∈ Metric.ball r ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hz)]
    linarith
  exact hball hn ⟨z, hspec, rfl⟩

theorem circleResolventOperator_idempotent (T : E →L[ℂ] E)
    {r : ℝ} (hr : 0 < r)
    (hres : ∀ z : ℂ, ‖z‖ = r → z ∈ resolventSet ℂ T) :
    IsIdempotentElem (circleResolventOperator T r) := by
  obtain ⟨R, hrR, hR⟩ := exists_resolvent_annulus T hres
  exact circleResolventOperator_idempotent_of_annulus T hr hrR hR

end

end DefocusingNLS

end OAI
