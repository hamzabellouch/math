import OAI.Combinatorics.ContingencyTables.Transport.IntegerLeafEnergy

namespace OAI

/-! # Repair edges are charged once in a symmetric physical graph -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical

noncomputable def pairTerm {X : Type*} (f H : X → ℝ) (p : X×X) : ℝ :=
  min (f p.1) (f p.2)*(H p.1-H p.2)^2

noncomputable def symmetricEnergy {X : Type*} (E : Finset (X×X)) (f H : X → ℝ) : ℝ :=
  (∑ p ∈ E,pairTerm f H p)/2

lemma pairTerm_nonnegative {X : Type*} (f H : X → ℝ) (hf : ∀ x,0 ≤ f x) (p : X×X) :
    0 ≤ pairTerm f H p := mul_nonneg (le_min (hf _) (hf _)) (sq_nonneg _)

lemma pairTerm_reverse {X : Type*} (f H : X → ℝ) (x y : X) :
    pairTerm f H (y,x)=pairTerm f H (x,y) := by
  unfold pairTerm
  rw [min_comm]
  congr 1
  ring

theorem symmetricEnergy_mono {X : Type*} (E F : Finset (X×X)) (hEF : E ⊆ F)
    (f H : X → ℝ) (hf : ∀ x,0 ≤ f x) : symmetricEnergy E f H ≤ symmetricEnergy F f H := by
  unfold symmetricEnergy
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact Finset.sum_le_sum_of_subset_of_nonneg hEF (fun p _ _ => pairTerm_nonnegative f H hf p)

/-- Distinct defects give distinct unoriented repair edges. Both directed
copies together use twice their weight and hence cancel the energy's half. -/
theorem repair_energy_le {X D : Type*} [Fintype D] (E : Finset (X×X))
    (f H : X → ℝ) (hf : ∀ x,0 ≤ f x) (x y : D → X)
    (hx : Function.Injective x) (hxy : ∀ d e,x d≠y e)
    (hforward : ∀ d,(x d,y d) ∈ E) (hreverse : ∀ d,(y d,x d) ∈ E) :
    (∑ d,pairTerm f H (x d,y d)) ≤ symmetricEnergy E f H := by
  let a := fun d => (x d,y d)
  let b := fun d => (y d,x d)
  let A := Finset.univ.image a
  let B := Finset.univ.image b
  have ha : Function.Injective a := fun d e he => hx (congrArg Prod.fst he)
  have hb : Function.Injective b := fun d e he => hx (congrArg Prod.snd he)
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨d,_,hd⟩ := Finset.mem_image.mp hp
    obtain ⟨e,_,he⟩ := Finset.mem_image.mp hq
    exact hxy d e (congrArg Prod.fst (hd.trans he.symm))
  have hsub : A ∪ B ⊆ E := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp|hp
    · obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hp
      exact hforward d
    · obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hp
      exact hreverse d
  have hA : (∑ p ∈ A,pairTerm f H p)=∑ d,pairTerm f H (x d,y d) :=
    Finset.sum_image (fun d _ e _ he => ha he)
  have hB : (∑ p ∈ B,pairTerm f H p)=∑ d,pairTerm f H (x d,y d) := by
    rw [Finset.sum_image (fun d _ e _ he => hb he)]
    apply Finset.sum_congr rfl
    intro d _
    exact pairTerm_reverse f H (x d) (y d)
  have hs : 2*(∑ d,pairTerm f H (x d,y d)) ≤ ∑ p ∈ E,pairTerm f H p := by
    calc
      _ = ∑ p ∈ A ∪ B,pairTerm f H p := by rw [Finset.sum_union hdis,hA,hB]; ring
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => pairTerm_nonnegative f H hf p)
  unfold symmetricEnergy
  linarith

end ContingencyTables.IntegerWeightedTransport

end OAI
