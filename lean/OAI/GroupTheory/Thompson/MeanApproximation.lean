import OAI.GroupTheory.Thompson.InvariantMean
import OAI.GroupTheory.Thompson.ProbabilityDefects
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Convex.Topology

namespace OAI

/-!
# Finite probabilities approximately invariant under a finite set

The usual positive normalized invariant mean forces zero to lie in the
closure of the actual finite-probability defect set. The separation argument
uses bounded coordinate functions of a continuous linear functional on ℓ¹;
no identification of the full dual of ℓ¹ is assumed.
-/

noncomputable section

open scoped ENNReal BigOperators

universe uG

namespace ThompsonNonamenability

variable {G : Type uG} [Group G] [DecidableEq G]

local instance : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩

/-- A separator gives one bounded real function for each translation. -/
def separatorCoordinate {S : Finset G} (ell : DefectSpace S →L[ℝ] ℝ)
    (h : {h : G // h ∈ S}) : BoundedReal G :=
  ⟨fun g => ell (lp.single 1 (h, g) 1), memℓp_infty ⟨‖ell‖, by
    rintro y ⟨g, rfl⟩
    have hb := ell.le_opNorm (lp.single 1 (h, g) 1)
    simpa only [lp.norm_single (by norm_num : 0 < (1 : ℝ≥0∞)),
      norm_one, mul_one] using hb⟩⟩

omit [Group G] in
@[simp]
theorem separatorCoordinate_apply [Group G] {S : Finset G}
    (ell : DefectSpace S →L[ℝ] ℝ) (h : {h : G // h ∈ S}) (g : G) :
    separatorCoordinate ell h g = ell (lp.single 1 (h, g) 1) := rfl

/-- The finite sum whose mean vanishes by left invariance. -/
def separatorDefect {S : Finset G} (ell : DefectSpace S →L[ℝ] ℝ) : BoundedReal G :=
  ∑ h : {h : G // h ∈ S},
    (leftPull h.val (separatorCoordinate ell h) - separatorCoordinate ell h)

theorem separatorDefect_apply {S : Finset G} (ell : DefectSpace S →L[ℝ] ℝ)
    (g : G) : separatorDefect ell g = ell (diracDefect S g) := by
  classical
  cases Subsingleton.elim (inferInstance : DecidableEq G) (Classical.decEq G)
  simp only [separatorDefect, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_sub, Pi.sub_apply, leftPull_apply, separatorCoordinate_apply,
    diracDefect, map_sum, map_sub]

theorem InvariantMean.separatorDefect_eq_zero (M : InvariantMean G)
    {S : Finset G} (ell : DefectSpace S →L[ℝ] ℝ) : M (separatorDefect ell) = 0 := by
  classical
  change M.toLinearMap (∑ h : {h : G // h ∈ S},
    (leftPull h.val (separatorCoordinate ell h) - separatorCoordinate ell h)) = 0
  simp only [map_sum, map_sub, M.left_invariant, sub_self, Finset.sum_const_zero]

/-- Separation contradicts the existence of a positive normalized invariant mean. -/
theorem InvariantMean.zero_mem_closure_defectSet (M : InvariantMean G)
    (S : Finset G) : (0 : DefectSpace S) ∈ closure (defectSet S) := by
  classical
  by_contra hout
  obtain ⟨ell, c, hc, hsep⟩ := geometric_hahn_banach_point_closed
    (convex_defectSet S).closure isClosed_closure hout
  have hcpos : 0 < c := by simpa only [ell.map_zero] using hc
  have hpoint (g : G) : c ≤ separatorDefect ell g := by
    rw [separatorDefect_apply]
    apply le_of_lt
    apply hsep
    apply subset_closure
    exact diracDefect_mem_defectSet S g
  have hmean : c ≤ M (separatorDefect ell) := by
    simpa only [InvariantMean.map_const] using
      M.mono (f := c • (1 : BoundedReal G)) (g := separatorDefect ell)
        (fun g => by simpa only [BoundedReal.smul_one_apply] using hpoint g)
  rw [M.separatorDefect_eq_zero] at hmean
  exact (not_le_of_gt hcpos) hmean

/-- Actual nonnegative finite probabilities with arbitrarily small total defect. -/
theorem InvariantMean.exists_probability_small_defect (M : InvariantMean G)
    (S : Finset G) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : G →₀ ℝ, IsProbabilityWeights p ∧ ‖defectMap S p‖ < ε := by
  classical
  obtain ⟨v, hv, hvsmall⟩ := Metric.mem_closure_iff.mp
    (M.zero_mem_closure_defectSet S) ε hε
  obtain ⟨p, hp, rfl⟩ := hv
  refine ⟨p, hp, ?_⟩
  simpa only [dist_zero_left] using hvsmall

end ThompsonNonamenability

end

end OAI
