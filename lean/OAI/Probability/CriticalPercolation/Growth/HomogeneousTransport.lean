import Mathlib
import OAI.Probability.CriticalPercolation.Modular.ActionOrbitTransport

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis
universe u v
variable {G : Type u} {X : Type v} [Group G] [MulAction G X]
open ActionOrbitTransport

lemma pair_fiber_eq_suborbit (x y : X) :
    {w : X | pairOrbit G X x w=pairOrbit G X x y}=stabilizerOrbit G X x y := by
  ext w
  simp only [Set.mem_ofPred_eq]
  rw [eq_comm,pairOrbit_eq,mem_stabilizerOrbit]

lemma reversed_pair_fiber_eq_suborbit (x y : X) :
    {w : X | pairOrbit G X w y=pairOrbit G X x y}=stabilizerOrbit G X y x := by
  ext w
  simp only [Set.mem_ofPred_eq]
  rw [eq_comm,pairOrbit_eq,mem_stabilizerOrbit]
  exact exists_congr (fun g => and_comm)

variable (ht : ∀ x y : X, ∃ g : G, g • x=y)
  (hf : ∀ x y : X, (stabilizerOrbit G X x y).Finite)
  (hu : ∀ x y : X, suborbitCard G X x y=suborbitCard G X y x)

include ht hf in
lemma pair_row_finite (o b x : X) :
    {y : X | pairOrbit G X x y=pairOrbit G X o b}.Finite := by
  obtain ⟨g,rfl⟩ := ht o x
  rw [←smul_pairOrbit G X g o b]
  simpa only [pair_fiber_eq_suborbit] using hf (g • o) (g • b)

include ht in
lemma pair_row_card (o b x : X) :
    {y : X | pairOrbit G X x y=pairOrbit G X o b}.ncard=suborbitCard G X o b := by
  obtain ⟨g,rfl⟩ := ht o x
  rw [←smul_pairOrbit G X g o b,pair_fiber_eq_suborbit]
  exact smul_suborbitCard G X g o b

include ht hf in
lemma pair_column_finite (o b y : X) :
    {x : X | pairOrbit G X x y=pairOrbit G X o b}.Finite := by
  obtain ⟨g,rfl⟩ := ht b y
  rw [←smul_pairOrbit G X g o b,reversed_pair_fiber_eq_suborbit]
  exact hf (g • b) (g • o)

include ht hu in
lemma pair_column_card (o b y : X) :
    {x : X | pairOrbit G X x y=pairOrbit G X o b}.ncard=suborbitCard G X o b := by
  obtain ⟨g,rfl⟩ := ht b y
  rw [←smul_pairOrbit G X g o b,reversed_pair_fiber_eq_suborbit]
  change suborbitCard G X (g • b) (g • o)=_
  rw [smul_suborbitCard,hu]

include ht hf hu in
lemma finite_row_sum_bound (o b : X) (F Y : Finset X) (f : X → ℝ)
    (hn : ∀ y∈Y, 0≤f y)
    (hY : ∀ x∈F, ∀ y, pairOrbit G X x y=pairOrbit G X o b → y∈Y) :
    (∑ x∈F, ∑ y∈(pair_row_finite ht hf o b x).toFinset, f y) ≤
      (suborbitCard G X o b : ℝ)*∑ y∈Y, f y := by
  have hr (x : X) (hx : x∈F) :
      ∑ y∈(pair_row_finite ht hf o b x).toFinset, f y=
        ∑ y∈Y, if pairOrbit G X x y=pairOrbit G X o b then f y else 0 := by
    rw [←Finset.sum_filter]
    apply Finset.sum_congr
    · ext y
      simp only [Set.Finite.mem_toFinset,Set.mem_ofPred_eq,Finset.mem_filter]
      exact ⟨fun h => ⟨hY x hx y h,h⟩,And.right⟩
    · intros; rfl
  rw [Finset.sum_congr rfl hr,Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (hn y hy)
  have hsub : F.filter (fun x => pairOrbit G X x y=pairOrbit G X o b)⊆
      (pair_column_finite ht hf o b y).toFinset := by
    intro x hx
    exact (pair_column_finite ht hf o b y).mem_toFinset.mpr (Finset.mem_filter.mp hx).2
  have hc := Finset.card_le_card hsub
  rw [←Set.ncard_eq_toFinset_card _ (pair_column_finite ht hf o b y), pair_column_card ht hu] at hc
  exact_mod_cast hc

end CriticalPercolation.HomogeneousAnalysis
end
end

end OAI
