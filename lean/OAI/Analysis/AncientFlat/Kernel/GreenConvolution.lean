import Mathlib

namespace OAI
noncomputable section
open scoped Topology BoundedContinuousFunction
namespace FlatRecursion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def shift (n : ℤ) : C(ℤ,ℤ) := ⟨fun j => j-n, continuous_of_discreteTopology⟩
def greenTerm (G : E →L[ℂ] E) (n : ℤ) : (ℤ →ᵇ E) →L[ℂ] (ℤ →ᵇ E) :=
  (G.compLeftContinuousBounded ℤ).comp (BoundedContinuousFunction.compContinuousCLM E ℂ (shift n))
@[simp] lemma greenTerm_apply (G : E →L[ℂ] E) (n : ℤ) (f : ℤ →ᵇ E) (j : ℤ) :
    greenTerm G n f j=G (f (j-n)) := rfl
lemma greenTerm_norm (G : E →L[ℂ] E) (n : ℤ) : ‖greenTerm G n‖≤‖G‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg G) (fun f => ?_)
  refine (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr ?_
  intro j
  exact G.le_opNorm_of_le (f.norm_coe_le_norm (j-n))
variable [CompleteSpace E]
lemma greenTerm_summable (G : ℤ → E →L[ℂ] E) (hG : Summable (fun n => ‖G n‖)) :
    Summable (fun n => greenTerm (G n) n) :=
  Summable.of_norm_bounded hG (fun index => greenTerm_norm (G index) index)
def greenOperator (G : ℤ → E →L[ℂ] E) : (ℤ →ᵇ E) →L[ℂ] (ℤ →ᵇ E) :=
  ∑' n : ℤ, greenTerm (G n) n
lemma convolution_summable (G : ℤ → E →L[ℂ] E) (hG : Summable (fun n => ‖G n‖))
    (f : ℤ →ᵇ E) (j : ℤ) : Summable (fun n => G n (f (j-n))) := by
  refine Summable.of_norm_bounded (hG.mul_right ‖f‖) (fun n => ?_)
  exact (G n).le_opNorm_of_le (f.norm_coe_le_norm _)
lemma greenOperator_apply (G : ℤ → E →L[ℂ] E) (hG : Summable (fun n => ‖G n‖))
    (f : ℤ →ᵇ E) (j : ℤ) : greenOperator G f j=∑' n : ℤ, G n (f (j-n)) := by
  exact ((BoundedContinuousFunction.evalCLM ℂ j).comp
    (ContinuousLinearMap.apply ℂ (ℤ →ᵇ E) f)).map_tsum (greenTerm_summable G hG)
lemma greenOperator_solves (P : E →L[ℂ] E) (q : ℂ) (G : ℤ → E →L[ℂ] E)
    (hG : Summable (fun n => ‖G n‖))
    (hrec : ∀ n : ℤ, q • G (n+1)-P*G n=if n=0 then 1 else 0)
    (f : ℤ →ᵇ E) (j : ℤ) : q • greenOperator G f (j+1)=P (greenOperator G f j)+f j := by
  have hs := convolution_summable G hG f j
  have hs' := convolution_summable G hG f (j+1)
  have hshift : (∑' n : ℤ, G n (f (j+1-n)))=∑' n : ℤ, G (n+1) (f (j-n)) := by
    rw [← (Equiv.addRight (1:ℤ)).tsum_eq]
    congr 1
    funext n
    simp only [Equiv.coe_addRight]
    congr 2
    omega
  have hs2 : Summable (fun n : ℤ => G (n+1) (f (j-n))) := by
    convert hs'.comp_injective (i := fun n : ℤ => n+1) (fun a b h => add_right_cancel h) using 1
    funext n
    dsimp
    congr 2
    omega
  rw [greenOperator_apply G hG, greenOperator_apply G hG, hshift]
  apply sub_eq_zero.mp
  rw [sub_add_eq_sub_sub, P.map_tsum hs, ← Summable.tsum_const_smul q hs2, ← Summable.tsum_sub (Summable.const_smul q hs2) (P.summable hs)]
  have he : (fun n : ℤ => q • G (n+1) (f (j-n))-P (G n (f (j-n))))=
      (fun n : ℤ => if n=0 then f j else 0) := by
    funext n
    have hn := congrArg (fun L : E →L[ℂ] E => L (f (j-n))) (hrec n)
    by_cases hn0 : n=0
    · simpa [hn0] using hn
    · simpa [hn0] using hn
  rw [he, tsum_ite_eq, sub_self]
end FlatRecursion

end

end OAI
