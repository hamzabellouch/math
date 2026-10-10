import OAI.Geometry.SurfaceImmersion.Geometry.PrescribedTransverseDerivative
import Mathlib.Geometry.Manifold.PartitionOfUnity

namespace OAI

/-! Compact transverse correction from local defining functions, with the cutoffs constructed. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.TransverseSmallFunction

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Local defining functions on the support of the desired derivative suffice. -/
theorem compact_transverse_correction {K O : Set E} {T : E → ℝ} (v : E)
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) (hT : ContDiff ℝ ∞ T)
    (hlocal : ∀ p ∈ K ∩ tsupport T, ∃ U : Set E, IsOpen U ∧ p ∈ U ∧
      ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧ (∀ x ∈ K ∩ U, f x = 0) ∧
        ∀ x ∈ U, fderiv ℝ f x v ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : E → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ tsupport H ⊆ O ∧
      (∀ x, |H x| < ε) ∧ ∀ x ∈ K, fderiv ℝ H x v = T x := by
  classical
  let I := {p : E // p ∈ K ∩ tsupport T}
  have hl (p : I) := hlocal p.val p.property
  choose U hU hpU f hf hzero hden using hl
  let W : I → Set E := fun p => (U p ∩ O) ∩ Metric.ball p.val 1
  have hW (p : I) : IsOpen (W p) := ((hU p).inter hO).inter Metric.isOpen_ball
  have hpW (p : I) : p.val ∈ W p :=
    ⟨⟨hpU p, hKO p.property.1⟩, Metric.mem_ball_self zero_lt_one⟩
  have hcover : K ∩ tsupport T ⊆ ⋃ p : I, W p := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hpW ⟨x, hx⟩⟩
  have hC : IsCompact (K ∩ tsupport T) := hK.inter_right (isClosed_tsupport T)
  obtain ⟨J, hJ⟩ := hC.elim_finite_subcover W hW hcover
  have hcJ : K ∩ tsupport T ⊆ ⋃ p : J, W p.val := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (hJ hx)
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, hxp⟩
  obtain ⟨χ, hχs⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, E))
    hC.isClosed (fun p : J => W p.val) (fun p => hW p.val) hcJ
  have hχ (p : J) : ContDiff ℝ ∞ (χ p) := (χ p).contMDiff.contDiff
  have hχc (p : J) : HasCompactSupport (χ p) := by
    apply (isCompact_closedBall p.val.val 1).of_isClosed_subset (isClosed_tsupport _)
    intro x hx
    exact Metric.mem_closedBall.mpr (Metric.mem_ball.mp (hχs p hx).2).le
  obtain ⟨H, hH, hHc, hHs, hHb, hHd⟩ := exists_prescribed_transverse_derivative
    (f := fun p : J => f p.val) (χ := fun p : J => χ p) (K := K) v
    (fun p => hf p.val) hχ hχc hT
    (fun p x hx => hden p.val x (hχs p hx).1.1)
    (fun p x hx hs => hzero p.val x ⟨hx, (hχs p hs).1.1⟩)
    (fun x hx hTx => by
      simpa only [finsum_eq_sum_of_fintype] using
        χ.sum_eq_one ⟨hx, subset_tsupport T (Function.mem_support.mpr hTx)⟩) hε
  refine ⟨H, hH, hHc, ?_, hHb, hHd⟩
  intro x hx
  obtain ⟨p, hp⟩ := mem_iUnion.mp (hHs hx)
  exact (hχs p hp).1.2

end ClosedSurfaceR4.TransverseSmallFunction

end

end OAI
