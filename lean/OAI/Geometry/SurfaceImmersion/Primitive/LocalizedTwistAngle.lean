import OAI.Geometry.SurfaceImmersion.Geometry.TransverseSupport

namespace OAI

/-! An arbitrary compact longitudinal angle is extended to a compact
 surface angle without changing any of its germs on the central axis. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def localizedTwistAngle (r : ℝ) (α : ℝ → ℝ) (x : Base) : ℝ :=
  transverseCutoff r x * α (x 1)

lemma localizedTwistAngle_smooth (r : ℝ) {α : ℝ → ℝ} (hα : ContDiff ℝ ∞ α) :
    ContDiff ℝ ∞ (localizedTwistAngle r α) :=
  (transverseCutoff_smooth r).mul (hα.comp (contDiff_apply ℝ ℝ 1))

lemma localizedTwistAngle_germ (r t : ℝ) (α : ℝ → ℝ) :
    localizedTwistAngle r α =ᶠ[𝓝 (crosscapAxis t)] fun x => α (x 1) := by
  filter_upwards [transverseCutoff_axis_germ r t] with x hx
  change transverseCutoff r x * α (x 1) = _
  simp only [Pi.one_apply] at hx
  rw [hx,one_mul]

lemma localizedTwistAngle_support {r : ℝ} (hr : 0 < r) (α : ℝ → ℝ) :
    tsupport (localizedTwistAngle r α) ⊆ {x | |x 0| ≤ r ∧ x 1 ∈ tsupport α} := by
  intro x hx
  have h0 := transverseCutoff_tsupport hr (tsupport_mul_subset_left (f := transverseCutoff r) (g := fun y : Base => α (y 1)) hx)
  have h1 : x 1 ∈ tsupport α := by
    have hc : IsClosed {x : Base | x 1 ∈ tsupport α} :=
      (isClosed_tsupport α).preimage (continuous_apply 1)
    have hs : tsupport (localizedTwistAngle r α) ⊆ {x : Base | x 1 ∈ tsupport α} := by
      apply closure_minimal _ hc
      intro y hy
      apply subset_tsupport
      intro hz
      exact hy (by simp [localizedTwistAngle,hz])
    exact hs hx
  exact ⟨h0,h1⟩

lemma localizedTwistAngle_compact {r : ℝ} (hr : 0 < r) {α : ℝ → ℝ}
    (hc : HasCompactSupport α) : HasCompactSupport (localizedTwistAngle r α) := by
  let T : ℝ × ℝ → Base := fun z => ![z.1,z.2]
  have hT : Continuous T := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst
    · exact continuous_snd
  apply (((isCompact_Icc : IsCompact (Icc (-r) r)).prod hc).image hT).of_isClosed_subset
    (isClosed_tsupport (localizedTwistAngle r α))
  intro x hx
  obtain ⟨h0,h1⟩ := localizedTwistAngle_support hr α hx
  refine ⟨(x 0,x 1),⟨abs_le.mp h0,h1⟩,?_⟩
  ext i; fin_cases i <;> rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
