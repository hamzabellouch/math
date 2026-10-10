import OAI.Combinatorics.PerfectMatching.Continuity
import OAI.Combinatorics.PerfectMatching.Covariance

namespace OAI

/-!
Normalized matching covariance: face rank, exact trace, and second variation.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Normalized matching directions on exactly the positive edge support. -/
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
/-- A feasible two-sided direction has a positive-side law supported on the
entropy optimizer at its midpoint. -/
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

/-- Every active-face direction belongs to the optimizer's normalized covariance
span. No face support or dimension assertion is being supplied as a hypothesis. -/
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

/-- Face codimension gives a lower bound for the rank of the genuine covariance. -/
theorem matching_covariance_rank (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) {p : G.Matching → ℝ}
    (hp : p ∈ G.feasibleLaws x) (hopt : entropy p=maxMatchingEntropy G x) :
    Fintype.card {e // 0 < x e} ≤ 2*Fintype.card V+
      (covariance p (matchingNormalized G x)).rank := by
  let W := weightedDirectionSpace p (matchingNormalized G x)
  let L : G.faceSpace x →ₗ[ℝ] W :=
    ((normalizeLinear x).comp (G.faceSpace x).subtype).codRestrict W
      (fun u => normalized_face_mem G heven hp hopt u.property)
  have hi : Function.Injective L := by
    intro u v huv
    apply Subtype.ext
    funext e
    have hh := congrFun (congrArg Subtype.val huv) e
    change u.val e/Real.sqrt (x e.val)=v.val e/Real.sqrt (x e.val) at hh
    exact (div_left_inj' (ne_of_gt (Real.sqrt_pos.mpr e.property))).mp hh
  have hdim := LinearMap.finrank_le_finrank_of_injective hi
  have hq := (G.faceSpace x).finrank_quotient_add_finrank
  have hc := G.faceCodimension_bound heven ((G.mem_polytope_iff x).mpr ⟨p,hp⟩)
  rw [covariance_rank hp.1.1]
  have hq' : G.faceCodimension x+Module.finrank ℝ (G.faceSpace x)=Fintype.card {e // 0 < x e} := by
    simpa only [LooplessGraph.faceCodimension,Module.finrank_pi,Module.finrank_self,Finset.sum_const,
      Finset.card_univ,smul_eq_mul,mul_one] using hq
  change Module.finrank ℝ (G.faceSpace x) ≤ Module.finrank ℝ W at hdim
  dsimp only [W] at hdim
  omega


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

/-- The normalized covariance has the exact trace s-m. -/
theorem matching_covariance_trace (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x) {m : ℕ}
    (hV : Fintype.card V=2*m) :
    (covariance p (matchingNormalized G x)).trace = Fintype.card {e // 0 < x e}-(m:ℝ) := by
  have hx : x ∈ G.polytope := (G.mem_polytope_iff x).mpr ⟨p,hp⟩
  have hsum : (∑ e : {e // 0 < x e}, x e.val)=(m:ℝ) := by
    rw [← G.marginal_sum hV hx]
    exact (sum_positive_support x x (fun e he => le_antisymm (le_of_not_gt he) (G.coordinate_mem_Icc hx e).1)).symm
  unfold matchingNormalized
  rw [normalized_covariance_trace hp.1 _ ?_ _ ?_ (fun e => e.property),hsum]
  · intro M e
    simp only [LooplessGraph.indicator]
    split <;> norm_num
  · intro e
    exact congrFun hp.2 e.val

omit [Fintype V] [DecidableEq V] in
/-- Convert the genuine second variation into the covariance spectral inequality. -/
theorem matching_covariance_second_variation (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (hopt : entropy p=maxMatchingEntropy G x) {m : ℝ} (hm : 0 < m)
    (hmax : ∀ y ∈ G.polytope, entropyDefect G m y ≤ entropyDefect G m x)
    (u : {e // 0 < x e} → ℝ) :
    (8*Real.exp (-entropy x/m)-1)*
        ((covariance p (matchingNormalized G x) *ᵥ u) ⬝ᵥ
          (covariance p (matchingNormalized G x) *ᵥ u)) +
      u ⬝ᵥ (covariance p (matchingNormalized G x) *ᵥ u) ≤ 0 := by
  let w := matchingScoreWeights x u
  let c := ∑ e, w e*x e
  let a := linearScore G w c
  have hcenter : ∑ M, p M*a M=0 := by
    dsimp only [a,c]
    rw [linearScore_expectation,hp.2,hp.1.2,mul_one,sub_self]
  have hh := matching_defect_second_variation G hp hopt hm.ne' hmax w c hcenter
  have hnorm : (∑ e, (G.mean (fun M => p M*a M) e)^2/x e) =
      (covariance p (matchingNormalized G x) *ᵥ u) ⬝ᵥ
        (covariance p (matchingNormalized G x) *ᵥ u) := by
    have hx : x ∈ G.polytope := (G.mem_polytope_iff x).mpr ⟨p,hp⟩
    rw [sum_positive_support x _ (fun e he => by
      have hz : x e=0 := le_antisymm (le_of_not_gt he) (G.coordinate_mem_Icc hx e).1
      simp [hz])]
    rw [dotProduct]
    apply Finset.sum_congr rfl
    intro e _
    rw [matchingNormalized_mulVec G hp,← sq,div_pow,Real.sq_sqrt e.property.le]
  have hquad : (∑ M, p M*(a M)^2) = u ⬝ᵥ (covariance p (matchingNormalized G x) *ᵥ u) := by
    rw [covariance_quadratic hp.1.1]
    apply Finset.sum_congr rfl
    intro M _
    rw [← matchingNormalized_score G x u M]
  change (8*Real.exp (-entropy x/m)-1)*(∑ e, (G.mean (fun M => p M*a M) e)^2/x e)+
    (8*Real.exp (-entropy x/m)/m)*(entropyLineD x (G.mean (fun M => p M*a M)) 0)^2+
    (∑ M, p M*(a M)^2) ≤ 0 at hh
  rw [hnorm,hquad] at hh
  have hpterm : 0 ≤ (8*Real.exp (-entropy x/m)/m)*
      (entropyLineD x (G.mean (fun M => p M*a M)) 0)^2 := by positivity
  linarith

end MatchingEntropy

end

end OAI
