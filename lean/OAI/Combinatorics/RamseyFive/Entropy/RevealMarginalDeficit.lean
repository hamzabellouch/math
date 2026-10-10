import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.SplitLaw

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {ι β : Type*} [Fintype ι] [Fintype β]
noncomputable local instance revealMarginalDeficitDecidableEq (E : Finset ι) :
    DecidableEq E := Classical.decEq _

theorem reveal_marginal_deficit (p : Law (ι → β)) (E : Finset ι) (J : ℝ)
    (hcap : ∀ i∈E,entropy (map p (fun x => x i)) ≤ J) :
    (∑ a,first (reveal p E) a*(∑ i∈Eᶜ,
      (J-entropy (map (fiber (reveal p E) a) (fun x => x i))))) ≤
      Fintype.card ι*J-entropy p := by
  have hb := reveal_information_budget p E
  have htc : 0 ≤ ∑ a,first (reveal p E) a*totalCorrelation (fiber (reveal p E) a) := by
    exact Finset.sum_nonneg fun a _ => mul_nonneg ((first (reveal p E)).nonneg a)
      (totalCorrelation_nonneg _)
  have hI (i : ι) : information (mapSnd (reveal p E) (fun x => x i)) =
      entropy (map p (fun x => x i))-
        ∑ a,first (reveal p E) a*entropy (map (fiber (reveal p E) a) (fun x => x i)) := by
    rw [information_conditional,second_mapSnd,second_reveal,first_mapSnd]
    simp only [fiber_mapSnd]
  have he : (∑ a,first (reveal p E) a*(∑ i∈Eᶜ,
      (J-entropy (map (fiber (reveal p E) a) (fun x => x i))))) =
      (Eᶜ.card:ℝ)*J-(∑ i∈Eᶜ,entropy (map p (fun x => x i)))+
      ∑ i∈Eᶜ,information (mapSnd (reveal p E) (fun x => x i)) := by
    have hswap : (∑ a,first (reveal p E) a*(∑ i∈Eᶜ,
        (J-entropy (map (fiber (reveal p E) a) (fun x => x i))))) =
        ∑ i∈Eᶜ,∑ a,first (reveal p E) a*
          (J-entropy (map (fiber (reveal p E) a) (fun x => x i))) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [hswap]
    calc
      _ = ∑ i∈Eᶜ,(J-entropy (map p (fun x => x i))+
          information (mapSnd (reveal p E) (fun x => x i))) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hI]
        simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,
          (first (reveal p E)).sum_one,one_mul]
        ring
      _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,
        Finset.sum_const,nsmul_eq_mul]
  have hs : (∑ i∈E,entropy (map p (fun x => x i))) ≤ (E.card:ℝ)*J := by
    calc
      _ ≤ ∑ _i∈E,J := Finset.sum_le_sum hcap
      _ = _ := by simp
  have hu := Finset.sum_add_sum_compl E (fun i => entropy (map p (fun x => x i)))
  have hc : (E.card:ℝ)+(Eᶜ.card:ℝ) = Fintype.card ι := by
    exact_mod_cast Finset.card_add_card_compl E
  have hcm : (E.card:ℝ)*J+(Eᶜ.card:ℝ)*J = Fintype.card ι*J := by rw [←add_mul,hc]
  rw [he]
  change (∑ i∈Eᶜ,information (mapSnd (reveal p E) (fun x => x i)))+
    (∑ a,first (reveal p E) a*totalCorrelation (fiber (reveal p E) a)) ≤
    (∑ i,entropy (map p (fun x => x i)))-entropy p at hb
  linarith

theorem totalCorrelation_le_joint_deficit (p : Law (ι → β)) (J : ℝ)
    (hcap : ∀ i,entropy (map p (fun x => x i)) ≤ J) :
    totalCorrelation p ≤ Fintype.card ι*J-entropy p := by
  apply sub_le_sub_right
  calc
    _ ≤ ∑ _i : ι,J := Finset.sum_le_sum fun i _ => hcap i
    _ = _ := by simp

end SharpRamseyFive.FiniteEntropy

end OAI
