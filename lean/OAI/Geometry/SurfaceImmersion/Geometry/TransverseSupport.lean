import OAI.Geometry.SurfaceImmersion.Whitney.RulingRemainder

namespace OAI

/-! The same longitudinal compact set bounds every narrowed transverse correction. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def narrowedRuling (f : Base → ProjectionTarget 3) (η : ℝ → ℝ) (r : ℝ) (x : Base) :=
  transverseCutoff r x • rulingRemainder f η x

lemma narrowedRuling_smooth {f : Base → ProjectionTarget 3} {η : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hη : ContDiff ℝ ∞ η) (r : ℝ) :
    ContDiff ℝ ∞ (narrowedRuling f η r) :=
  (transverseCutoff_smooth r).smul (rulingRemainder_smooth hf hη)

lemma narrowedRuling_support (f : Base → ProjectionTarget 3) (η : ℝ → ℝ)
    {r : ℝ} (hr : 0 < r) :
    tsupport (narrowedRuling f η r) ⊆ {x | |x 0| ≤ r ∧ x 1 ∈ tsupport η} := by
  intro x hx
  have hleft : x ∈ tsupport (transverseCutoff r) := tsupport_smul_subset_left _ _ hx
  have hright : x ∈ tsupport (rulingRemainder f η) := tsupport_smul_subset_right _ _ hx
  exact ⟨transverseCutoff_tsupport hr hleft,rulingRemainder_support f η hright⟩

lemma narrowedRuling_compact (f : Base → ProjectionTarget 3) {η : ℝ → ℝ}
    (hη : HasCompactSupport η) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (narrowedRuling f η r) := by
  let T : ℝ × ℝ → Base := fun z => ![z.1,z.2]
  have hT : Continuous T := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst
    · exact continuous_snd
  have hK : IsCompact (T '' (Icc (-r) r ×ˢ tsupport η)) :=
    (isCompact_Icc.prod hη).image hT
  apply hK.of_isClosed_subset (isClosed_tsupport _) _
  intro x hx
  obtain ⟨h0,h1⟩ := narrowedRuling_support f η hr hx
  refine ⟨(x 0,x 1),⟨abs_le.mp h0,h1⟩,?_⟩
  ext i; fin_cases i <;> rfl

lemma narrowedRuling_fixed_ball (f : Base → ProjectionTarget 3) {η : ℝ → ℝ}
    (hη : HasCompactSupport η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      tsupport (narrowedRuling f η r) ⊆ closedBall (0 : Base) ρ := by
  obtain ⟨C,hC⟩ := hη.exists_bound_of_continuousOn continuous_id.continuousOn
  let ρ := |C|+2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  refine ⟨ρ,hρ,?_⟩
  intro r hr hr1 x hx
  obtain ⟨h0,h1⟩ := narrowedRuling_support f η hr hx
  rw [mem_closedBall,dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg hρ.le).mpr
  intro i
  fin_cases i
  · rw [Real.norm_eq_abs]
    exact h0.trans (hr1.trans (by dsimp [ρ]; linarith [abs_nonneg C]))
  · exact (hC (x 1) h1).trans (by dsimp [ρ]; linarith [le_abs_self C])

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
