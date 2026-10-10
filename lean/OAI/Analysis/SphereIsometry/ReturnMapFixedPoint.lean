import OAI.Analysis.SphereIsometry.ReturnMapNoncompactness
import OAI.Analysis.SphereIsometry.CondensingFixedPoint

namespace OAI

/-!
# A fixed point from the return map's radius estimates

The finite-bin noncompactness estimate and the proved condensing fixed-point
theorem discharge the analytic step from the elementary geometric data.
Continuity is needed only on the actual invariant closed convex set.
-/

namespace Tingley

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [CompleteSpace X]

/-- The radius bounds and two-point estimate imply an actual fixed point.
The hypotheses contain neither a noncompactness estimate nor a fixed-point
principle: both are supplied by the preceding constructive proofs. -/
theorem exists_fixedPoint_of_return_estimate
    {C : Set X} {g : X → X} {p s u r : X → ℝ} {t M : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hM : 0 < M)
    (hCne : C.Nonempty) (hCclosed : IsClosed C)
    (hCb : Bornology.IsBounded C) (hCconvex : Convex ℝ C)
    (hg : ContinuousOn g C) (hgC : Set.MapsTo g C C)
    (hbounds : ∀ v ∈ C,
      (1 - t ≤ p v ∧ p v ≤ 1 + t) ∧
      (1 - t ≤ s v ∧ s v ≤ 1 + t) ∧
      (1 - t ≤ u v ∧ u v ≤ 1 + t) ∧
      (1 - t ≤ r v ∧ r v ≤ 1 + t))
    (hs : ∀ v ∈ C, s v = p v + M)
    (hr : ∀ v ∈ C, r v = u v + M)
    (hpair : ∀ v ∈ C, ∀ v' ∈ C,
      dist (g v) (g v') ≤
        (u v * p v / (r v * s v)) * dist v v' +
        2 * |u v - u v'| / r v +
        2 * u v * |p v - p v'| / (r v * s v)) :
    ∃ x ∈ C, g x = x := by
  have hfactor := return_contraction_factor_mem_Ico ht0 ht1 hM hCne
    (fun v hv => (hbounds v hv).1.1)
    (fun v hv => (hbounds v hv).2.1.2) hs
  apply exists_fixedPoint_of_kuratowski_contraction hCne hCclosed hCb
    hCconvex hg hgC hfactor.1 hfactor.2
  intro H hHC
  exact chi_return_image_le ht0 ht1 hM hCne hCb hgC hbounds hs hr hpair hHC

end Tingley

end OAI
