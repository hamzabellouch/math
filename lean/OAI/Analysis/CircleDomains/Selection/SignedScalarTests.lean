import OAI.Analysis.CircleDomains.Sobolev.SmoothPlaneSobolev
import OAI.Analysis.CircleDomains.Rigidity.AffineTracePairs

namespace OAI

/-! Compact real tests can be encoded by unit-interval tests and a common
cutoff. On the dust this is an affine coordinate change, so pair-nullity
is preserved exactly. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def signedScalarEncoding (η u : EuclideanPlane → ℝ) (C : ℝ) (x : EuclideanPlane) : ℝ :=
  (η x + u x / C) / 2

 theorem signedScalarEncoding_unit
    {η u : EuclideanPlane → ℝ} {C : ℝ} (hC : 0 < C)
    (hη : ∀ x, η x ∈ Icc 0 1) (hu : ∀ x, ‖u x‖ ≤ C)
    (hone : ∀ x, u x ≠ 0 → η x = 1) (x : EuclideanPlane) :
    signedScalarEncoding η u C x ∈ Icc 0 1 := by
  have hb : -C ≤ u x ∧ u x ≤ C := abs_le.mp (by simpa only [Real.norm_eq_abs] using hu x)
  by_cases hz : u x = 0
  · unfold signedScalarEncoding
    rw [hz, zero_div, add_zero]
    constructor <;> linarith [(hη x).1, (hη x).2]
  · have hl : -1 ≤ u x / C := (le_div_iff₀ hC).mpr (by nlinarith [hb.1])
    have hh : u x / C ≤ 1 := (div_le_iff₀ hC).mpr (by nlinarith [hb.2])
    unfold signedScalarEncoding
    rw [hone x hz]
    constructor <;> linarith

 theorem signedScalarEncoding_continuous
    {η u : EuclideanPlane → ℝ} (hη : Continuous η) (hu : Continuous u) (C : ℝ) :
    Continuous (signedScalarEncoding η u C) :=
  (hη.add (hu.div_const C)).div_const 2

 theorem signedScalarEncoding_compact
    {η u : EuclideanPlane → ℝ} (hη : HasCompactSupport η) (hu : HasCompactSupport u) (C : ℝ) :
    HasCompactSupport (signedScalarEncoding η u C) := by
  change HasCompactSupport (fun x => (η x + u x / C) / 2)
  simp only [div_eq_mul_inv]
  exact (hη.add hu.mul_right).mul_right

 def signedScalarEncoding_witness
    {U : Set EuclideanPlane} {η u : EuclideanPlane → ℝ}
    (Hη : DeGiorgi.MemW1pWitness 2 η U) (Hu : DeGiorgi.MemW1pWitness 2 u U) (C : ℝ) :
    DeGiorgi.MemW1pWitness 2 (signedScalarEncoding η u C) U :=
  ((Hη.add (Hu.smul C⁻¹)).smul (2 : ℝ)⁻¹).congr_ae (Eventually.of_forall fun x => by
    simp only [signedScalarEncoding, div_eq_mul_inv]
    ring)

 theorem signedScalarEncoding_recovery (η u : EuclideanPlane → ℝ)
    {C : ℝ} (hC : C ≠ 0) (x : EuclideanPlane) :
    (2 * C) * signedScalarEncoding η u C x - C * η x = u x := by
  unfold signedScalarEncoding
  field_simp
  ring

 def smoothCompactPlaneWitness {η : EuclideanPlane → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hs : HasCompactSupport η) :
    DeGiorgi.MemW1pWitness 2 η univ :=
  smoothPlaneSobolevWitness isOpen_univ (hη.of_le (by simp)).contDiffOn
    ((hη.continuous.memLp_of_hasCompactSupport hs).restrict univ)
    (fun i => (((hη.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1))).restrict univ)

end CircleDomainRigidity

end

end OAI
