import OAI.Analysis.CircleDomains.Uniformization.AnalyticCapRounding
import OAI.Analysis.CircleDomains.Topology.DisjointSupportedHomeomorphs
import OAI.Analysis.CircleDomains.Topology.DisjointClosedNeighborhoods
import OAI.Analysis.CircleDomains.Uniformization.JordanCircularizationSequence

namespace OAI

/-! Simultaneous smooth rounding of a finite disjoint analytic Jordan family.
The actual ambient diffeomorphism fixes the complement of a bounded disk. -/
open Set Function Metric Bornology
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma exists_finite_analytic_rounding {I : Type*} [Finite I]
    (C : FiniteJordanConfiguration I) (ha : ∀i,IsAnalyticJordanCap (C.hole i)) :
    ∃ (P : ℂ ≃ₜ ℂ) (c : I → ℂ) (r : I → ℝ) (R : ℝ),0<R ∧
      ContDiff ℝ ∞ (P : ℂ → ℂ) ∧ ContDiff ℝ ∞ (P.symm : ℂ → ℂ) ∧
      (∀z,R≤‖z‖ → P z=z) ∧ (∀i,0<r i) ∧
      ∀i,P '' closure (jordanInterior (C.hole i))=closedBall (c i) (r i) := by
  classical
  let := Fintype.ofFinite I
  let A := fun i => closure (jordanInterior (C.hole i))
  have hA (i : I) : IsCompact (A i) := isCompact_closure_jordanInterior (C.hole i)
  obtain ⟨R,hR,hbound⟩ := (isCompact_iUnion hA).isBounded.exists_pos_norm_lt
  obtain ⟨U,hU,hAU,hUR,hUd⟩ := finite_disjoint_closed_neighborhoods A
    (fun _ => ball (0:ℂ) R) (fun i => (hA i).isClosed) (fun _ => isOpen_ball)
    (fun i z hz => mem_ball_zero_iff.mpr (hbound _ (mem_iUnion.mpr ⟨i,hz⟩))) C.disjoint
  choose T c r hr hTs hTis hfix himage using fun i =>
    exists_smooth_analytic_cap_rounding (ha i) (hU i) (hAU i)
  have hUd' : Pairwise (fun i j => Disjoint (U i) (U j)) := by
    intro i j hij
    exact (hUd hij).mono subset_closure subset_closure
  obtain ⟨P,hPs,hPis,hPf,hP⟩ := exists_disjoint_supported_composition A U hAU hUd'
    T hTs hTis hfix
  refine ⟨P,c,r,R,hR,hPs,hPis,?_,hr,?_⟩
  · intro z hz
    apply hPf
    intro i hi
    exact (not_lt_of_ge hz) (mem_ball_zero_iff.mp (hUR i (subset_closure hi)))
  · intro i
    exact (hP i).trans (himage i)

end CircleDomainRigidity

end

end OAI
