import OAI.Combinatorics.MatchingEntropy.Continuity

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter Matrix

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def matchingNormalized (G : LooplessGraph V E) (x : E → ℝ) :
    G.Matching → {e // 0 < x e} → ℝ :=
  normalizedCentered (fun M e => G.indicator M e.val) (fun e => x e.val)

omit [Fintype V] [DecidableEq V] in
theorem matchingNormalized_average (G : LooplessGraph V E) {x y : E → ℝ}
    {q : G.Matching → ℝ} (hq : q ∈ G.feasibleLaws y) (e : {e // 0 < x e}) :
    (∑ M, q M*matchingNormalized G x M e)=(y e.val-x e.val)/Real.sqrt (x e.val) := by
  simp only [matchingNormalized,normalizedCentered,← mul_div_assoc,mul_sub,
    ← Finset.sum_div,Finset.sum_sub_distrib,← Finset.sum_mul,hq.1.2,one_mul]
  rw [show (∑ M, q M*G.indicator M e.val)=y e.val from congrFun hq.2 e.val]

omit [Fintype V] [DecidableEq V] in

theorem midpoint_law_support (G : LooplessGraph V E) {x v : E → ℝ} {a : ℝ}
    {p q r : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (hopt : entropy p=maxMatchingEntropy G x)
    (hq : q ∈ G.feasibleLaws (x+a • v))
    (hr : r ∈ G.feasibleLaws (x+(-a) • v)) :
    ∀ M, 0 < q M → 0 < p M := by
  let w : G.Matching → ℝ := (1/2:ℝ) • q+(1/2:ℝ) • r
  have hw : w ∈ G.feasibleLaws x := by
    refine ⟨convex_probabilitySimplex _ hq.1 hr.1 (by norm_num) (by norm_num) (by norm_num),?_⟩
    change G.meanLinear ((1/2:ℝ) • q+(1/2:ℝ) • r) = _
    rw [map_add,map_smul,map_smul]
    change (1/2:ℝ) • G.mean q+(1/2:ℝ) • G.mean r = _
    rw [hq.2,hr.2]
    ext e
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  intro M hM
  apply matching_optimizer_support G hp hw hopt
  change 0 < (1/2:ℝ)*q M+(1/2:ℝ)*r M
  have hh := hr.1.1 M
  linarith

theorem normalized_face_mem (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) {p : G.Matching → ℝ}
    (hp : p ∈ G.feasibleLaws x) (hopt : entropy p=maxMatchingEntropy G x)
    {u : {e // 0 < x e} → ℝ} (hu : u ∈ G.faceSpace x) :
    (fun e => u e/Real.sqrt (x e.val)) ∈ weightedDirectionSpace p (matchingNormalized G x) := by
  have hx : x ∈ G.polytope := (G.mem_polytope_iff x).mpr ⟨p,hp⟩
  have hev := G.faceSpace_eventually_line (G.polytope_subset_constraintPolytope hx) hu
  have hneg : ∀ᶠ t : ℝ in 𝓝 0, x+(-t) • LooplessGraph.positiveExtension x u ∈ G.constraintPolytope := by
    have hc : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by simpa using continuous_neg.tendsto (0:ℝ)
    exact hc.eventually hev
  have hh : ∀ᶠ t : ℝ in 𝓝[>] 0,
      (x+t • LooplessGraph.positiveExtension x u ∈ G.constraintPolytope ∧
      x+(-t) • LooplessGraph.positiveExtension x u ∈ G.constraintPolytope) ∧ 0 < t :=
    ((hev.and hneg).filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin
  obtain ⟨a,⟨ha,hna⟩,ha0⟩ := hh.exists
  rw [← G.polytope_eq_constraints heven] at ha hna
  obtain ⟨q,hq⟩ := (G.mem_polytope_iff _).mp ha
  obtain ⟨r,hr⟩ := (G.mem_polytope_iff _).mp hna
  have hsupp := midpoint_law_support G hp hopt hq hr
  have hsum : (∑ M, q M • matchingNormalized G x M) ∈
      weightedDirectionSpace p (matchingNormalized G x) := by
    apply Submodule.sum_mem
    intro M _
    by_cases hM : 0 < p M
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨M,hM⟩,rfl⟩)
    · have hq0 : q M=0 := le_antisymm (le_of_not_gt fun hqM => hM (hsupp M hqM)) (hq.1.1 M)
      simp only [hq0,zero_smul]
      exact Submodule.zero_mem _
  have hin := Submodule.smul_mem _ a⁻¹ hsum
  have he : a⁻¹ • (∑ M, q M • matchingNormalized G x M) =
      (fun e => u e/Real.sqrt (x e.val)) := by
    ext e
    simp only [Pi.smul_apply,Finset.sum_apply,smul_eq_mul]
    rw [matchingNormalized_average G hq]
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,LooplessGraph.positiveExtension_pos]
    field_simp
    ring
  rwa [he] at hin

def normalizeLinear (x : E → ℝ) :
    ({e // 0 < x e} → ℝ) →ₗ[ℝ] ({e // 0 < x e} → ℝ) where
  toFun := fun u e => u e/Real.sqrt (x e.val)
  map_add' := by intro u v; ext e; exact add_div _ _ _
  map_smul' := by intro a u; ext e; exact mul_div_assoc _ _ _

omit [DecidableEq E] in
theorem sum_positive_support (x f : E → ℝ) (hf : ∀ e, ¬ 0 < x e → f e=0) :
    (∑ e, f e) = ∑ e : {e // 0 < x e}, f e.val := by
  classical
  have hz : (∑ e : {e // ¬ 0 < x e}, f e.val)=0 :=
    Finset.sum_eq_zero fun e _ => hf e.val e.property
  have hh := Fintype.sum_subtype_add_sum_subtype (fun e => 0 < x e) f
  rw [hz,add_zero] at hh
  exact hh.symm

def matchingScoreWeights (x : E → ℝ) (u : {e // 0 < x e} → ℝ) : E → ℝ :=
  LooplessGraph.positiveExtension x (fun e => u e/Real.sqrt (x e.val))

omit [Fintype V] [DecidableEq V] in
theorem matchingNormalized_score (G : LooplessGraph V E) (x : E → ℝ)
    (u : {e // 0 < x e} → ℝ) (M : G.Matching) :
    linearScore G (matchingScoreWeights x u) (∑ e, matchingScoreWeights x u e*x e) M =
      matchingNormalized G x M ⬝ᵥ u := by
  classical
  unfold linearScore
  rw [← Finset.sum_sub_distrib]
  rw [sum_positive_support x _ (fun e he => by simp [matchingScoreWeights,LooplessGraph.positiveExtension,he])]
  rw [dotProduct]
  apply Finset.sum_congr rfl
  intro e _
  simp only [matchingScoreWeights,LooplessGraph.positiveExtension_pos,matchingNormalized,normalizedCentered]
  ring

omit [Fintype V] [DecidableEq V] in
theorem matchingNormalized_mulVec (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (u : {e // 0 < x e} → ℝ) (e : {e // 0 < x e}) :
    (covariance p (matchingNormalized G x) *ᵥ u) e =
      G.mean (fun M => p M * linearScore G (matchingScoreWeights x u)
        (∑ e, matchingScoreWeights x u e*x e) M) e.val / Real.sqrt (x e.val) := by
  let a := linearScore G (matchingScoreWeights x u) (∑ e, matchingScoreWeights x u e*x e)
  have hcenter : ∑ M, p M*a M=0 := by
    dsimp only [a]
    rw [linearScore_expectation,hp.2,hp.1.2,mul_one,sub_self]
  calc
    _ = ∑ M, (p M*a M*G.indicator M e.val-x e.val*(p M*a M))/Real.sqrt (x e.val) := by
      rw [covariance_mulVec hp.1.1]
      apply Finset.sum_congr rfl
      intro M _
      rw [← matchingNormalized_score G x u M]
      change p M*((G.indicator M e.val-x e.val)/Real.sqrt (x e.val))*a M = _
      ring
    _ = _ := by
      rw [← Finset.sum_div,Finset.sum_sub_distrib,← Finset.mul_sum,hcenter,mul_zero,sub_zero]
      rfl

end MatchingEntropyBounds

end

end OAI
