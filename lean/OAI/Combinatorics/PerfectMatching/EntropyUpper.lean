import OAI.Combinatorics.PerfectMatching.SeparableLower

namespace OAI

universe u_1 u_2

section

noncomputable section
open scoped BigOperators
namespace MatchingEntropy

theorem entropy_le_subprob_crossEntropy {I : Type*} [Fintype I] {p q : I → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i ≤ 1) (hq : q ∈ probabilitySimplex I)
    (hsupp : ∀ i, p i=0 → q i=0) :
    entropy q ≤ -∑ i, q i*Real.log (p i) := by
  have hterm : ∀ i, Real.negMulLog (q i) ≤ -(q i*Real.log (p i))+p i-q i := by
    intro i
    by_cases hi : p i=0
    · simp [hi,hsupp i hi]
    · simpa only [neg_mul] using negMulLog_tangent (hq.1 i)
        (lt_of_le_of_ne (hp i) (Ne.symm hi))
  have hh := Finset.sum_le_sum (s := Finset.univ) fun i _ => hterm i
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_neg_distrib,hq.2] at hh
  change entropy q ≤ -(∑ i, q i*Real.log (p i))+(∑ i,p i)-1 at hh
  linarith

variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

def matchingBits (G : LooplessGraph V E) (M : G.Matching) : E → Bool :=
  fun e => decide (e ∈ M.val)

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem matchingBits_injective (G : LooplessGraph V E) : Function.Injective G.matchingBits := by
  intro M N h
  apply Subtype.ext
  ext e
  have he := congrFun h e
  simpa only [matchingBits,decide_eq_decide] using he

end LooplessGraph

def productBoolean (x : E → ℝ) (b : E → Bool) : ℝ :=
  ∏ e, if b e then x e else 1-x e

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem productBoolean_nonneg {x : E → ℝ} (hx : ∀ e, x e ∈ Set.Icc (0:ℝ) 1)
    (b : E → Bool) : 0 ≤ productBoolean x b := by
  apply Finset.prod_nonneg
  intro e _
  split
  · exact (hx e).1
  · exact sub_nonneg.mpr (hx e).2

omit [Fintype V] [DecidableEq V] in
theorem productBoolean_sum (x : E → ℝ) : (∑ b : E → Bool, productBoolean x b)=1 := by
  unfold productBoolean
  rw [← Fintype.prod_sum (fun e (b : Bool) => if b then x e else 1-x e)]
  simp

omit [Fintype V] [DecidableEq V] in
theorem matchingBoolean_sum_le (G : LooplessGraph V E) {x : E → ℝ}
    (hx : ∀ e, x e ∈ Set.Icc (0:ℝ) 1) :
    (∑ M, productBoolean x (G.matchingBits M)) ≤ 1 := by
  rw [← productBoolean_sum x]
  classical
  calc
    _ = ∑ b ∈ Finset.univ.image G.matchingBits, productBoolean x b := by
      rw [Finset.sum_image]
      intro M _ N _ h
      exact G.matchingBits_injective h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun b _ _ => productBoolean_nonneg hx b)

omit [Fintype V] [DecidableEq V] in
theorem matching_boolean_factor_pos (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x) {M : G.Matching} (hM : 0<p M) (e : E) :
    0<(if G.matchingBits M e then x e else 1-x e) := by
  unfold LooplessGraph.matchingBits
  by_cases he : e ∈ M.val
  · simp only [he,decide_true,ite_true]
    have hh := Finset.single_le_sum (f := fun N => p N*G.indicator N e)
      (s := Finset.univ) (fun N _ => mul_nonneg (hp.1.1 N) (G.indicator_nonneg N e))
      (Finset.mem_univ M)
    have hm : G.indicator M e=1 := by simp [LooplessGraph.indicator,he]
    rw [hm,mul_one] at hh
    change p M ≤ G.mean p e at hh
    rw [hp.2] at hh
    exact hM.trans_le hh
  · simp only [he,decide_false]
    have hh := Finset.single_le_sum (f := fun N => p N*(1-G.indicator N e))
      (s := Finset.univ) (fun N _ => mul_nonneg (hp.1.1 N)
        (sub_nonneg.mpr (G.indicator_le_one N e))) (Finset.mem_univ M)
    have hm : G.indicator M e=0 := by simp [LooplessGraph.indicator,he]
    simp only [hm,sub_zero,mul_one,mul_sub,Finset.sum_sub_distrib,hp.1.2] at hh
    change p M ≤ 1-G.mean p e at hh
    rw [hp.2] at hh
    exact hM.trans_le hh

omit [Fintype V] [DecidableEq V] in

theorem matching_entropy_le_binary (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x) : entropy p ≤ binaryEntropy x := by
  have hx := G.coordinate_mem_Icc ((G.mem_polytope_iff x).mpr ⟨p,hp⟩)
  have hprod (M : G.Matching) (hM : 0<p M) : 0<productBoolean x (G.matchingBits M) :=
    Finset.prod_pos (fun e _ => matching_boolean_factor_pos G hp hM e)
  have hcross := entropy_le_subprob_crossEntropy
    (fun M => productBoolean_nonneg hx (G.matchingBits M)) (matchingBoolean_sum_le G hx) hp.1
    (fun M hzero => le_antisymm (le_of_not_gt (fun hM => (ne_of_gt (hprod M hM)) hzero)) (hp.1.1 M))
  have hlog (M : G.Matching) : p M*Real.log (productBoolean x (G.matchingBits M)) =
      ∑ e, p M*(G.indicator M e*Real.log (x e)+(1-G.indicator M e)*Real.log (1-x e)) := by
    by_cases hzero : p M=0
    · simp [hzero]
    · have hpos : 0<p M := lt_of_le_of_ne (hp.1.1 M) (Ne.symm hzero)
      rw [productBoolean,Real.log_prod (fun e _ => ne_of_gt (matching_boolean_factor_pos G hp hpos e)),
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      simp only [LooplessGraph.matchingBits,LooplessGraph.indicator]
      by_cases he : e ∈ M.val <;> simp [he]
  have heq : -(∑ M, p M*Real.log (productBoolean x (G.matchingBits M)))=binaryEntropy x := by
    simp_rw [hlog]
    rw [Finset.sum_comm]
    have he (e : E) : (∑ M, p M*(G.indicator M e*Real.log (x e)+
        (1-G.indicator M e)*Real.log (1-x e)))=
        x e*Real.log (x e)+(1-x e)*Real.log (1-x e) := by
      simp_rw [mul_add,← mul_assoc,Finset.sum_add_distrib,← Finset.sum_mul]
      have hmean : (∑ M,p M*G.indicator M e)=x e := congrFun hp.2 e
      have hbar : (∑ M,p M*(1-G.indicator M e))=1-x e := by
        simp_rw [mul_sub,mul_one,Finset.sum_sub_distrib,hp.1.2,hmean]
      rw [hmean,hbar]
    simp_rw [he]
    rw [Finset.sum_add_distrib,neg_add_rev]
    dsimp only [binaryEntropy]
    rw [entropy_eq,entropy_eq]
    ring
  rwa [heq] at hcross

omit [Fintype V] [DecidableEq V] in
theorem maxMatchingEntropy_le_binary (G : LooplessGraph V E) (x : E → ℝ)
    (hx : x ∈ G.polytope) : maxMatchingEntropy G x ≤ binaryEntropy x := by
  obtain ⟨p,hp,hopt⟩ := maxMatchingEntropy_attained G hx
  rw [← hopt]
  exact matching_entropy_le_binary G hp

end MatchingEntropy
end
end

end OAI
