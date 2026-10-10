import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.LogSum

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped BigOperators Classical
variable {ι κ β : Type*} [Fintype ι] [Fintype κ] [Fintype β]

noncomputable local instance : DecidableEq (ι ⊕ κ) := Classical.decEq _

noncomputable def splitLaw (p : Law ((ι ⊕ κ) → β)) : Law ((ι → β) × (κ → β)) :=
  pair p (fun x i => x (Sum.inl i)) (fun x j => x (Sum.inr j))

lemma entropy_splitLaw (p : Law ((ι ⊕ κ) → β)) : entropy (splitLaw p)=entropy p := by
  apply entropy_map_injective
  intro x y he
  funext i
  cases i with
  | inl i => exact congrFun (congrArg Prod.fst he) i
  | inr j => exact congrFun (congrArg Prod.snd he) j

lemma first_splitLaw_eval (p : Law ((ι ⊕ κ) → β)) (i : ι) :
    map (first (splitLaw p)) (fun x => x i)=map p (fun x => x (Sum.inl i)) := by
  rw [splitLaw,first_pair,map_comp]
  rfl

lemma second_splitLaw_eval (p : Law ((ι ⊕ κ) → β)) (j : κ) :
    map (second (splitLaw p)) (fun x => x j)=map p (fun x => x (Sum.inr j)) := by
  rw [splitLaw,second_pair,map_comp]
  rfl

theorem total_correlation_split_drop (p : Law ((ι ⊕ κ) → β)) :
    totalCorrelation (ι := ι ⊕ κ) (β := β) p -
      (∑ a,first (splitLaw p) a*totalCorrelation (ι := κ) (β := β) (fiber (splitLaw p) a)) =
      totalCorrelation (ι := ι) (β := β) (first (splitLaw p))+
        ∑ j,information (mapSnd (splitLaw p) (fun x => x j)) := by
  have hh:=total_correlation_drop (α := ι → β) (ι := κ) (β := β) (splitLaw p)
  simp only [totalCorrelation,Fintype.sum_sum_type,first_splitLaw_eval,
    second_splitLaw_eval,entropy_splitLaw] at hh ⊢
  linarith

theorem information_split_budget (p : Law ((ι ⊕ κ) → β)) :
    (∑ j,information (mapSnd (splitLaw p) (fun x => x j))) +
      (∑ a,first (splitLaw p) a*totalCorrelation (ι := κ) (β := β) (fiber (splitLaw p) a)) ≤
      totalCorrelation (ι := ι ⊕ κ) (β := β) p := by
  have hh:=total_correlation_split_drop p
  have hn:=totalCorrelation_nonneg (first (splitLaw p))
  linarith

end

section
open scoped BigOperators Classical
variable {ι β : Type*} [Fintype ι] [Fintype β]

noncomputable local instance (E : Finset ι) : DecidableEq E := Classical.decEq _

noncomputable def reveal (p : Law (ι → β)) (E : Finset ι) : Law ((E → β) × (ι → β)) :=
  pair p (fun x i => x i.val) id

lemma first_reveal (p : Law (ι → β)) (E : Finset ι) :
    first (reveal p E) = map p (fun x (i : E) => x i.val) := first_pair _ _ _

lemma second_reveal (p : Law (ι → β)) (E : Finset ι) :
    second (reveal p E) = p := by rw [reveal,second_pair,map_id]

lemma entropy_reveal (p : Law (ι → β)) (E : Finset ι) :
    entropy (reveal p E) = entropy p := by
  apply entropy_map_injective
  intro x y he
  exact congrArg Prod.snd he

lemma information_reveal_selected (p : Law (ι → β)) (E : Finset ι) (i : ι) (hi : i∈E) :
    information (mapSnd (reveal p E) (fun x => x i)) = entropy (map p (fun x => x i)) := by
  let e : E := ⟨i,hi⟩
  have he : mapSnd (reveal p E) (fun x => x i)=
      map (first (reveal p E)) (fun y => (y,y e)) := by
    rw [first_reveal]
    simp only [reveal,mapSnd,pair,map_comp,Function.comp_def,id_eq]
    rfl
  have hH : entropy (mapSnd (reveal p E) (fun x => x i))=
      entropy (first (reveal p E)) := by
    rw [he]
    apply entropy_map_injective
    intro x y h
    exact congrArg Prod.fst h
  simp only [information,first_mapSnd,second_mapSnd,second_reveal,hH]
  ring

lemma entropy_reveal_le_coordinate_sum (p : Law (ι → β)) (E : Finset ι) :
    entropy (first (reveal p E)) ≤ ∑ i∈E,entropy (map p (fun x => x i)) := by
  have hh := totalCorrelation_nonneg (first (reveal p E))
  simp only [totalCorrelation,first_reveal,map_comp,Function.comp_def] at hh
  rw [Finset.sum_coe_sort E (fun i : ι => entropy (map p (fun x => x i)))] at hh
  simpa only [first_reveal] using (sub_nonneg.mp hh)

theorem reveal_information_budget (p : Law (ι → β)) (E : Finset ι) :
    (∑ i∈Eᶜ,information (mapSnd (reveal p E) (fun x => x i)))+
      (∑ a,first (reveal p E) a*totalCorrelation (fiber (reveal p E) a)) ≤
        totalCorrelation p := by
  have hh := total_correlation_drop (reveal p E)
  simp only [second_reveal,entropy_reveal] at hh
  have hb := entropy_reveal_le_coordinate_sum p E
  have hs := Finset.sum_add_sum_compl E
    (fun i => information (mapSnd (reveal p E) (fun x => x i)))
  have hsel : (∑ i∈E,information (mapSnd (reveal p E) (fun x => x i)))=
      ∑ i∈E,entropy (map p (fun x => x i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact information_reveal_selected p E i hi
  rw [hsel] at hs
  change (∑ i∈Eᶜ,information (mapSnd (reveal p E) (fun x => x i)))+
      (∑ a,first (reveal p E) a*totalCorrelation (fiber (reveal p E) a)) ≤
        (∑ i,entropy (map p (fun x => x i)))-entropy p
  linarith

theorem reveal_coordinate_information_le (p : Law (ι → β)) (E : Finset ι)
    (j : E) (i : ι) :
    information (pair p (fun x => x j.val) (fun x => x i)) ≤
      information (mapSnd (reveal p E) (fun x => x i)) := by
  have hh := information_observation_le (mapSnd (reveal p E) (fun x => x i))
    (fun y => y j)
  simpa only [reveal,mapSnd,pair,map_comp,Function.comp_def,id_eq] using hh

end

open scoped BigOperators Classical
variable {ι β : Type} [Fintype ι] [Fintype β]

noncomputable local instance (E : Finset ι) : DecidableEq E := Classical.decEq _

inductive RevealPlan (ι β : Type) [Fintype ι] [Fintype β] : ℕ → Type
  | stop : RevealPlan ι β 0
  | step {n : ℕ} (choice : Law (Finset ι))
      (next : (E : Finset ι) → (E → β) → RevealPlan ι β n) : RevealPlan ι β (n+1)

noncomputable def revealCost (p : Law (ι → β)) (E : Finset ι) : ℝ :=
  ∑ i∈Eᶜ,information (mapSnd (reveal p E) (fun x => x i))

noncomputable def revealRoundCost (p : Law (ι → β)) {n : ℕ} (t : RevealPlan ι β n) : Fin n → ℝ :=
  match t with
  | .stop => Fin.elim0
  | .step q next => Fin.cases (∑ E,q E*revealCost p E)
      (fun i => ∑ E,q E*(∑ a,first (reveal p E) a*
        revealRoundCost (fiber (reveal p E) a) (next E a) i))

lemma revealCost_nonneg (p : Law (ι → β)) (E : Finset ι) : 0 ≤ revealCost p E := by
  exact Finset.sum_nonneg fun i _ => information_nonneg _

lemma revealRoundCost_nonneg (p : Law (ι → β)) {n : ℕ} (t : RevealPlan ι β n)
    (i : Fin n) : 0 ≤ revealRoundCost p t i := by
  induction t generalizing p with
  | stop => exact Fin.elim0 i
  | @step n q next ih =>
    cases i using Fin.cases with
    | zero =>
      exact Finset.sum_nonneg fun E _ => mul_nonneg (q.nonneg E) (revealCost_nonneg p E)
    | succ i =>
      exact Finset.sum_nonneg fun E _ => mul_nonneg (q.nonneg E)
        (Finset.sum_nonneg fun a _ => mul_nonneg ((first (reveal p E)).nonneg a)
          (ih E a (fiber (reveal p E) a) i))

theorem adaptive_reveal_information (p : Law (ι → β)) {n : ℕ} (t : RevealPlan ι β n) :
    (∑ i,revealRoundCost p t i) ≤ totalCorrelation p := by
  induction t generalizing p with
  | stop => simpa using totalCorrelation_nonneg p
  | @step n q next ih =>
    have htail : (∑ i : Fin n,∑ E,q E*(∑ a,first (reveal p E) a*
        revealRoundCost (fiber (reveal p E) a) (next E a) i)) =
        ∑ E,q E*(∑ a,first (reveal p E) a*
          (∑ i,revealRoundCost (fiber (reveal p E) a) (next E a) i)) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro E _
      rw [Finset.sum_comm]
    simp only [revealRoundCost,Fin.sum_univ_succ,Fin.cases_zero,Fin.cases_succ,htail]
    rw [←Finset.sum_add_distrib]
    calc
      _ ≤ ∑ E,q E*(revealCost p E+
          (∑ a,first (reveal p E) a*totalCorrelation (fiber (reveal p E) a))) := by
        apply Finset.sum_le_sum
        intro E _
        rw [mul_add]
        apply add_le_add_right
        apply mul_le_mul_of_nonneg_left _ (q.nonneg E)
        apply Finset.sum_le_sum
        intro a _
        exact mul_le_mul_of_nonneg_left (ih E a (fiber (reveal p E) a))
          ((first (reveal p E)).nonneg a)
      _ ≤ ∑ E,q E*totalCorrelation p := by
        apply Finset.sum_le_sum
        intro E _
        exact mul_le_mul_of_nonneg_left (reveal_information_budget p E) (q.nonneg E)
      _ = totalCorrelation p := by rw [←Finset.sum_mul,q.sum_one,one_mul]

theorem exists_low_information_round (p : Law (ι → β)) {n : ℕ} (hn : 0<n)
    (t : RevealPlan ι β n) : ∃ i : Fin n,revealRoundCost p t i ≤ totalCorrelation p/n := by
  by_contra h
  push Not at h
  have hh : (∑ _i : Fin n,totalCorrelation p/n)<∑ i,revealRoundCost p t i := by
    apply Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0,hn⟩⟩)
    intro i _
    exact h i
  have hc : (∑ _i : Fin n,totalCorrelation p/n)=totalCorrelation p := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  rw [hc] at hh
  exact (not_lt_of_ge (adaptive_reveal_information p t)) hh

end SharpRamseyFive.FiniteEntropy

end OAI
