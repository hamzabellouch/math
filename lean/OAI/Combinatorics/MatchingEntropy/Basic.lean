import OAI.Combinatorics.MatchingEntropy.Coupling

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.LooplessGraph

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [Fintype E] [DecidableEq V] in
@[simp] theorem indicator_nonneg (G : LooplessGraph V E) (M : G.Matching) (e : E) :
    0 ≤ G.indicator M e := by
  simp only [indicator]
  split <;> norm_num

omit [Fintype V] [Fintype E] [DecidableEq V] in
@[simp] theorem indicator_le_one (G : LooplessGraph V E) (M : G.Matching) (e : E) :
    G.indicator M e ≤ 1 := by
  simp only [indicator]
  split <;> norm_num

omit [Fintype V] [DecidableEq V] in
theorem continuous_mean (G : LooplessGraph V E) : Continuous G.mean := by
  unfold mean
  fun_prop

def meanLinear (G : LooplessGraph V E) : (G.Matching → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun := G.mean
  map_add' p q := by
    ext e
    simp [mean, add_mul, Finset.sum_add_distrib]
  map_smul' a p := by
    ext e
    simp [mean, mul_assoc, Finset.mul_sum]

omit [Fintype V] [DecidableEq V] in
theorem mean_mem_polytope (G : LooplessGraph V E) {p : G.Matching → ℝ}
    (hp : p ∈ probabilitySimplex G.Matching) : G.mean p ∈ G.polytope := by
  have h := (convex_convexHull ℝ (Set.range G.indicator)).sum_mem
    (fun M _ ↦ hp.1 M) hp.2 (fun M _ ↦ subset_convexHull ℝ _ (Set.mem_range_self M))
  have he : G.mean p = ∑ M, p M • G.indicator M := by
    ext e
    simp [mean]
  rw [he]
  exact h

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mean_single (G : LooplessGraph V E) (M : G.Matching) :
    G.mean (Pi.single M 1) = G.indicator M := by
  classical
  ext e
  simp [mean, Pi.single_apply, ite_mul]

omit [Fintype V] [DecidableEq V] in

theorem mem_polytope_iff (G : LooplessGraph V E) (y : E → ℝ) :
    y ∈ G.polytope ↔ (G.feasibleLaws y).Nonempty := by
  classical
  constructor
  · intro hy
    have hc : Convex ℝ (G.mean '' probabilitySimplex G.Matching) :=
      (convex_probabilitySimplex G.Matching).linear_image G.meanLinear
    have hs : Set.range G.indicator ⊆ G.mean '' probabilitySimplex G.Matching := by
      rintro _ ⟨M, rfl⟩
      exact ⟨Pi.single M 1, single_mem_probabilitySimplex M, G.mean_single M⟩
    obtain ⟨p, hp, rfl⟩ := convexHull_min hs hc hy
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact G.mean_mem_polytope hp

omit [Fintype V] [DecidableEq V] in
theorem compact_feasibleLaws (G : LooplessGraph V E) (y : E → ℝ) :
    IsCompact (G.feasibleLaws y) := by
  exact (isCompact_probabilitySimplex G.Matching).inter_right
    (isClosed_eq G.continuous_mean continuous_const)

omit [Fintype V] [DecidableEq V] in
theorem compact_polytope (G : LooplessGraph V E) : IsCompact G.polytope := by
  have heq : G.polytope = G.mean '' probabilitySimplex G.Matching := by
    ext y
    rw [G.mem_polytope_iff]
    rfl
  rw [heq]
  exact (isCompact_probabilitySimplex G.Matching).image G.continuous_mean

end MatchingEntropyBounds.LooplessGraph

end

end OAI
