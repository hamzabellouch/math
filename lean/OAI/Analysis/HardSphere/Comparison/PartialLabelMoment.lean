import Mathlib
import OAI.Analysis.HardSphere.Comparison.LabelMoment

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace HardSphere.Comparison
lemma partial_match_eq_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι→Type*} [∀i,DecidableEq (A i)] (S : Finset ι) (G : ℝ) (p : ∀i,A i×A i) :
    (∏i,if i∈S then (if (p i).1=(p i).2 then G else 1) else 1)=
      G^(S.filter (fun i ↦ (p i).1=(p i).2)).card := by
  have he (i : ι) : (if i∈S then (if (p i).1=(p i).2 then G else 1) else 1)=
      if i∈S ∧ (p i).1=(p i).2 then G else 1 := by
    by_cases hi : i∈S <;> simp [hi]
  simp_rw [he]
  rw [Finset.prod_ite]
  have hs : (Finset.univ.filter (fun i:ι ↦ i∈S ∧ (p i).1=(p i).2))=
      S.filter (fun i ↦ (p i).1=(p i).2) := by ext i; simp
  simp only [Finset.prod_const, one_pow, mul_one, hs]

lemma partial_label_match_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι→Type*) [∀i,Fintype (A i)] [∀i,Nonempty (A i)] [∀i,DecidableEq (A i)]
    [∀i,MeasurableSpace (A i)] [∀i,MeasurableSingletonClass (A i)]
    (S : Finset ι) (G M : ℝ) (hG : 1≤G) (hM : 0<M)
    (hcard : ∀i∈S,M≤2*(Fintype.card (A i):ℝ)) :
    (∫p:∀i,A i×A i,G^(S.filter (fun i ↦ (p i).1=(p i).2)).card
      ∂Measure.pi (fun i ↦ (PMF.uniformOfFintype (A i)).toMeasure.prod
        (PMF.uniformOfFintype (A i)).toMeasure))≤
      Real.exp ((2*(G-1)/M)*(S.card:ℝ)) := by
  simp_rw [←partial_match_eq_pow S G]
  rw [integral_fintype_prod_eq_prod (fun (i:ι) (p:A i×A i) ↦
    if i∈S then (if p.1=p.2 then G else 1) else 1)]
  have hi (i : ι) : (∫p:A i×A i, (if i∈S then (if p.1=p.2 then G else 1) else 1)
      ∂((PMF.uniformOfFintype (A i)).toMeasure.prod (PMF.uniformOfFintype (A i)).toMeasure))=
      if i∈S then 1+(G-1)/(Fintype.card (A i):ℝ) else 1 := by
    by_cases h : i∈S
    · simp only [h,ite_true,uniform_pair_match_integral]
    · simp [h]
  simp_rw [hi]
  calc
    _ ≤ ∏i:ι,Real.exp (if i∈S then 2*(G-1)/M else 0) := by
      apply Finset.prod_le_prod₀
      · intro i _
        by_cases h : i∈S
        · simp only [h,ite_true]
          have := div_nonneg (sub_nonneg.mpr hG) (Nat.cast_nonneg (Fintype.card (A i)))
          linarith
        · simp [h]
      · intro i _
        by_cases h : i∈S
        · simp only [h,ite_true]
          have hn : (0:ℝ)<Fintype.card (A i) := by exact_mod_cast Fintype.card_pos
          have hd : (G-1)/(Fintype.card (A i):ℝ)≤2*(G-1)/M := by
            apply (div_le_div_iff₀ hn hM).mpr
            nlinarith [hcard i h]
          linarith [Real.add_one_le_exp (2*(G-1)/M)]
        · simp [h]
    _ = _ := by
      rw [←Real.exp_sum]
      congr 1
      rw [←Finset.sum_filter]
      simp [mul_comm]

end HardSphere.Comparison

end
end

end

end OAI
