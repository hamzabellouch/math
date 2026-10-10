import OAI.Analysis.LipschitzEquivalence.CompleteContinuity

namespace OAI

universe uM uE

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.FreeSpace
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem exists_finite_approx (μ : Space M) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : M →₀ ℝ, ‖μ - Finsupp.linearCombination ℝ point a‖ < ε := by
  obtain ⟨a,ha⟩ := dense_combinations.exists_dist_lt μ hε
  exact ⟨a,by simpa only [dist_eq_norm] using ha⟩

theorem combination_mem_supported (a : M →₀ ℝ) {K : Set M}
    (ha : ∀ x ∈ a.support, x ∈ K) : Finsupp.linearCombination ℝ point a ∈ supported K := by
  rw [Finsupp.linearCombination_apply]
  exact Submodule.sum_mem _ (fun x hx => Submodule.smul_mem _ _ (point_mem_supported (ha x hx)))

theorem dual_point_lipschitz (T : Space M →L[ℝ] ℝ) :
    LipschitzWith ‖T‖₊ (fun x => T (point x)) := by
  simpa only [mul_one,Function.comp_def] using T.lipschitzWith.comp isometry_point.lipschitzWith

theorem dual_as_test (T : Space M →L[ℝ] ℝ) :
    test (normalized (fun x => T (point x)) (dual_point_lipschitz T)) = T := by
  have hzero : T (point 0) = 0 := by simp
  exact (linearize_unique _ (dual_point_lipschitz T) hzero _ (by
    intro x
    change T (point x)-T (point 0) = T (point x)
    rw [hzero,sub_zero])).symm.trans
    (linearize_unique _ (dual_point_lipschitz T) hzero T (fun _ => rfl))

theorem exists_vanishing_test (K : Set M) (μ : Space M) {ε : ℝ}
    (hfar : ∀ ν : Space M, ν ∈ supported K → ε ≤ ‖μ-ν‖) :
    ∃ f : M → ℝ, LipschitzWith 1 f ∧ f 0 = 0 ∧ (∀ x ∈ K, f x = 0) ∧
      ∀ hf : LipschitzWith 1 f, ε ≤ test (normalized f hf) μ := by
  let S := supported K
  let : IsClosed (S : Set (Space M)) := supported_isClosed K
  have hnorm : ε ≤ ‖S.mkQL μ‖ := by
    by_contra h
    have ht : 0 < ε-‖S.mkQL μ‖ := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨x,hx,hxnorm⟩ := Submodule.Quotient.norm_mk_lt (S.mkQL μ) ht
    have hmem : μ-x ∈ S := by
      apply (Submodule.Quotient.mk_eq_zero S).mp
      change S.mkQ (μ-x) = 0
      rw [map_sub]
      change S.mkQL μ-(Submodule.Quotient.mk x) = 0
      rw [hx,sub_self]
    have hbad := hfar (μ-x) hmem
    rw [sub_sub_cancel] at hbad
    linarith
  obtain ⟨g,hgn,hg⟩ := exists_dual_vector'' ℝ (S.mkQL μ)
  let T := g.comp S.mkQL
  have hT : ‖T‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    exact (g.le_opNorm _).trans (by
      have hm := Submodule.Quotient.norm_mk_le S v
      change ‖S.mkQL v‖ ≤ ‖v‖ at hm
      change ‖g‖ * ‖S.mkQL v‖ ≤ 1 * ‖v‖
      exact mul_le_mul hgn hm (norm_nonneg _) zero_le_one)
  have hf : LipschitzWith 1 (fun x => T (point x)) :=
    (dual_point_lipschitz T).weaken (by exact_mod_cast hT)
  refine ⟨(fun x => T (point x)),hf,by simp,?_,?_⟩
  · intro x hx
    change g (Submodule.Quotient.mk (point x)) = 0
    rw [(Submodule.Quotient.mk_eq_zero S).mpr (point_mem_supported hx),map_zero]
  · intro hf'
    have he : normalized (fun x => T (point x)) hf' =
        normalized (fun x => T (point x)) (dual_point_lipschitz T) := rfl
    rw [he,dual_as_test]
    change ε ≤ g (S.mkQL μ)
    rw [hg]
    exact hnorm

end LipschitzCounterexample.FreeSpace
namespace LipschitzCounterexample.LocalizedLinearization
open scoped NNReal Topology
open Filter Set
variable {M : Type uM} {E : Type uE} [MetricSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem lipschitz_effective_smul (p : M → E) (φ : M → ℝ) {A B C P : ℝ≥0}
    (hp : LipschitzWith C p) (hφ : LipschitzWith B φ)
    (hA : ∀ x, |φ x| ≤ A) (hP : ∀ x, φ x ≠ 0 → ‖p x‖ ≤ P) :
    LipschitzWith (A*C+B*P) (fun x => φ x • p x) := by
  have hsmall (x y : M) (hx : ‖p x‖ ≤ P) :
      ‖φ x • p x-φ y • p y‖ ≤ (A*C+B*P : ℝ≥0) * dist x y := by
    have hid : φ x • p x-φ y • p y =
        φ y • (p x-p y)+(φ x-φ y) • p x := by
      simp only [smul_sub,sub_smul]
      abel
    rw [hid]
    calc
      _ ≤ ‖φ y • (p x-p y)‖+‖(φ x-φ y) • p x‖ := norm_add_le _ _
      _ = |φ y| * ‖p x-p y‖+|φ x-φ y| * ‖p x‖ := by simp only [norm_smul,Real.norm_eq_abs]
      _ ≤ (A : ℝ)*(C*dist x y)+(B*dist x y)*P :=
        add_le_add (mul_le_mul (hA y) (by simpa only [dist_eq_norm] using hp.dist_le_mul x y)
          (norm_nonneg _) A.coe_nonneg)
          (mul_le_mul (hφ.dist_le_mul x y) hx (norm_nonneg _) (by positivity))
      _ = _ := by push_cast; ring
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  by_cases hx : φ x = 0
  · by_cases hy : φ y = 0
    · simp only [hx,hy,zero_smul,sub_self,norm_zero]
      positivity
    · rw [norm_sub_rev,dist_comm]
      exact hsmall y x (hP y hy)
  · exact hsmall x y (hP x hx)

def setCutoff (K : Set M) (r : ℝ≥0) (x : M) : ℝ :=
  cutoff (0 : ℝ) r (Metric.infDist x K)

theorem setCutoff_lipschitz (K : Set M) (r : ℝ≥0) :
    LipschitzWith (2/r) (setCutoff K r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact ((cutoff_lipschitz (0 : ℝ) r).dist_le_mul (Metric.infDist x K) (Metric.infDist y K)).trans
    (mul_le_mul_of_nonneg_left (by simpa only [one_mul,NNReal.coe_one] using
      (Metric.lipschitz_infDist_pt K).dist_le_mul x y) (by positivity))

theorem setCutoff_nonneg (K : Set M) (r : ℝ≥0) (x : M) : 0 ≤ setCutoff K r x :=
  cutoff_nonneg _ _ _

theorem setCutoff_le_one (K : Set M) (r : ℝ≥0) (x : M) : setCutoff K r x ≤ 1 :=
  cutoff_le_one _ _ _

theorem setCutoff_one {K : Set M} {r : ℝ≥0} (hr : 0 < r) {x : M}
    (hx : Metric.infDist x K ≤ r/2) : setCutoff K r x = 1 := by
  apply cutoff_one _ hr
  simpa only [dist_zero_right,Real.norm_of_nonneg Metric.infDist_nonneg] using hx

theorem setCutoff_zero {K : Set M} {r : ℝ≥0} (hr : 0 < r) {x : M}
    (hx : (r : ℝ) ≤ Metric.infDist x K) : setCutoff K r x = 0 := by
  apply cutoff_zero _ hr
  simpa only [dist_zero_right,Real.norm_of_nonneg Metric.infDist_nonneg] using hx

theorem setCutoff_nonzero {K : Set M} {r : ℝ≥0} (hr : 0 < r) {x : M}
    (hx : setCutoff K r x ≠ 0) : Metric.infDist x K < r := by
  by_contra h
  exact hx (setCutoff_zero hr (le_of_not_gt h))

variable [Zero M]

theorem setCutoff_support_bounded {K : Set M} (hK : K.Nonempty) {R r : ℝ≥0}
    (hR : ∀ x ∈ K, dist x 0 ≤ R) (hr : 0 < r) {x : M}
    (hx : setCutoff K r x ≠ 0) : dist x 0 ≤ R+r := by
  obtain ⟨y,hy,hxy⟩ := (Metric.infDist_lt_iff hK).mp (setCutoff_nonzero hr hx)
  exact (dist_triangle x y 0).trans (by exact_mod_cast (add_le_add hxy.le (hR y hy)).trans_eq (add_comm _ _))

end LipschitzCounterexample.LocalizedLinearization

end

end OAI
