import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.SplitLaw
import OAI.Combinatorics.RamseyFive.Decoding.Swap

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical NNReal
variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]

noncomputable local instance : DecidableEq ((B × A) ⊕ T) := Classical.decEq _
noncomputable local instance (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _

noncomputable def representativeSet (s : B → A) : Finset ((B × A) ⊕ T) :=
  Finset.univ.image fun b => Sum.inl (b,s b)

omit [Fintype A] [Fintype T] in
lemma mem_representativeSet_left (s : B → A) (b : B) (a : A) :
    Sum.inl (b,a) ∈ representativeSet (T := T) s ↔ a=s b := by
  simp [representativeSet,eq_comm]

omit [Fintype A] [Fintype T] in
lemma not_mem_representativeSet_right (s : B → A) (t : T) :
    Sum.inr t ∉ representativeSet s := by simp [representativeSet]

noncomputable def coordinateInformation (p : Law (((B × A) ⊕ T) → β))
    (i j : (B × A) ⊕ T) : ℝ≥0 :=
  ⟨information (pair p (fun x => x j) (fun x => x i)),information_nonneg _⟩

noncomputable def blockInformation (p : Law (((B × A) ⊕ T) → β))
    (s : B → A) (b : B) (a : A) : ℝ≥0 :=
  (Finset.univ.erase b).sup fun c => coordinateInformation p (Sum.inl (b,a)) (Sum.inl (c,s c))

noncomputable def middleInformation (p : Law (((B × A) ⊕ T) → β))
    (s : B → A) (t : T) : ℝ≥0 :=
  Finset.univ.sup fun c => coordinateInformation p (Sum.inr t) (Sum.inl (c,s c))

lemma blockInformation_own_independent (p : Law (((B × A) ⊕ T) → β))
    (s : B → A) (b : B) (a i : A) :
    blockInformation p (Function.update s b a) b i=blockInformation p s b i := by
  apply Finset.sup_congr rfl
  intro c hc
  rw [Function.update_of_ne (Finset.mem_erase.mp hc).1]

lemma blockInformation_le_reveal (p : Law (((B × A) ⊕ T) → β))
    (s : B → A) (b : B) (a : A) :
    (blockInformation p s b a:ℝ) ≤ information
      (mapSnd (reveal p (representativeSet s)) (fun x => x (Sum.inl (b,a)))) := by
  let z : ℝ≥0 := ⟨information (mapSnd (reveal p (representativeSet s)) (fun x => x (Sum.inl (b,a)))),information_nonneg _⟩
  change (blockInformation p s b a:ℝ) ≤ (z:ℝ)
  rw [NNReal.coe_le_coe]
  apply Finset.sup_le
  intro c _
  exact reveal_coordinate_information_le p (representativeSet s)
    ⟨Sum.inl (c,s c),(mem_representativeSet_left s c (s c)).mpr rfl⟩ (Sum.inl (b,a))

lemma middleInformation_le_reveal (p : Law (((B × A) ⊕ T) → β))
    (s : B → A) (t : T) :
    (middleInformation p s t:ℝ) ≤ information
      (mapSnd (reveal p (representativeSet s)) (fun x => x (Sum.inr t))) := by
  let z : ℝ≥0 := ⟨information (mapSnd (reveal p (representativeSet s)) (fun x => x (Sum.inr t))),information_nonneg _⟩
  change (middleInformation p s t:ℝ) ≤ (z:ℝ)
  rw [NNReal.coe_le_coe]
  apply Finset.sup_le
  intro c _
  exact reveal_coordinate_information_le p (representativeSet s)
    ⟨Sum.inl (c,s c),(mem_representativeSet_left s c (s c)).mpr rfl⟩ (Sum.inr t)

theorem representative_unselected_le_cost (p : Law (((B × A) ⊕ T) → β)) (s : B → A) :
    (∑ b,∑ a∈Finset.univ.erase (s b),(blockInformation p s b a:ℝ))+
      (∑ t,(middleInformation p s t:ℝ)) ≤ revealCost p (representativeSet s) := by
  classical
  let f : ((B × A) ⊕ T) → ℝ := fun i =>
    information (mapSnd (reveal p (representativeSet s)) (fun x => x i))
  have he : revealCost p (representativeSet s)=
      (∑ b,∑ a∈Finset.univ.erase (s b),f (Sum.inl (b,a)))+∑ t,f (Sum.inr t) := by
    unfold revealCost
    change (∑ i∈(representativeSet s)ᶜ,f i)=_
    have hfilt : (representativeSet (T := T) s)ᶜ=Finset.univ.filter (fun i => i∉representativeSet s) := by ext i; simp
    rw [hfilt,Finset.sum_filter,Fintype.sum_sum_type]
    simp only [mem_representativeSet_left,not_mem_representativeSet_right,
      not_false_eq_true,ite_true,Fintype.sum_prod_type]
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    rw [←Finset.sum_filter]
    rw [Finset.filter_ne']
  rw [he]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro b _
    apply Finset.sum_le_sum
    intro a _
    exact blockInformation_le_reveal p s b a
  · exact Finset.sum_le_sum fun t _ => middleInformation_le_reveal p s t

theorem representative_selected_identity (p : Law (((B × A) ⊕ T) → β)) :
    (Fintype.card A:ℝ)*(∑ s : B → A,∑ b,(blockInformation p s b (s b):ℝ))=
      ∑ s : B → A,∑ b,∑ a,(blockInformation p s b a:ℝ) := by
  apply RepresentativeAverage.selected_sum (fun s b a => (blockInformation p s b a:ℝ))
  intro s b a i
  exact congrArg NNReal.toReal (blockInformation_own_independent p s b a i)

theorem representative_all_le_twice_cost (p : Law (((B × A) ⊕ T) → β))
    (hsize : 2≤Fintype.card A) :
    (∑ s : B → A,((∑ b,∑ a,(blockInformation p s b a:ℝ))+
      ∑ t,(middleInformation p s t:ℝ))) ≤
      2*(∑ s : B → A,revealCost p (representativeSet s)) := by
  have hb := RepresentativeAverage.all_sum_le_twice_unselected
    (fun s b a => (blockInformation p s b a:ℝ))
    (fun _ _ _ => NNReal.coe_nonneg _) (by
      intro s b a i
      exact congrArg NNReal.toReal (blockInformation_own_independent p s b a i)) hsize
  have hm : 0≤∑ s : B → A,∑ t,(middleInformation p s t:ℝ) := by
    exact Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun t _ => NNReal.coe_nonneg _
  have hc := Finset.sum_le_sum (fun s (_ : s∈(Finset.univ : Finset (B → A))) =>
    representative_unselected_le_cost p s)
  simp only [Finset.sum_add_distrib] at hc ⊢
  linarith

end SharpRamseyFive.FiniteEntropy

end OAI
