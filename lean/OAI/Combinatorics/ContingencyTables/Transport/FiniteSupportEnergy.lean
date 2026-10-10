import OAI.Combinatorics.ContingencyTables.Transport.FiniteSymmetricEnergy

namespace OAI

/-! # Restricting a finite weighted graph to its positive states -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical

variable {X Y : Type*} [Fintype X]

omit [Fintype X] in
lemma pairTerm_eq_zero_left (f H : Y → ℝ) (hf : ∀ y,0 ≤ f y) (a b : Y)
    (ha : f a=0) : pairTerm f H (a,b)=0 := by
  simp only [pairTerm,ha,min_eq_left (hf b),zero_mul]

omit [Fintype X] in
lemma pairTerm_eq_zero_right (f H : Y → ℝ) (hf : ∀ y,0 ≤ f y) (a b : Y)
    (hb : f b=0) : pairTerm f H (a,b)=0 := by
  simp only [pairTerm,hb,min_eq_right (hf a),zero_mul]

/-- Only endpoints with nonzero weight need to occur in the embedding.
The ambient graph may still contain zero-weight vertices. -/
theorem symmetricEnergy_restrict (E : Finset (Y×Y)) (f H : Y → ℝ)
    (hf : ∀ y,0 ≤ f y) (i : X → Y) (hi : Function.Injective i)
    (hsupport : ∀ p ∈ E,(f p.1≠0 → ∃ x,i x=p.1) ∧ (f p.2≠0 → ∃ x,i x=p.2)) :
    symmetricEnergy E f H=
      (∑ x,∑ y,if (i x,i y) ∈ E then
        min (f (i x)) (f (i y))*(H (i x)-H (i y))^2 else 0)/2 := by
  let j : X×X → Y×Y := fun p => (i p.1,i p.2)
  let S := (Finset.univ : Finset (X×X)).filter (fun p => j p ∈ E)
  have hj : Function.Injective j := by
    intro a b h
    exact Prod.ext (hi (congrArg Prod.fst h)) (hi (congrArg Prod.snd h))
  have hsub : S.image j ⊆ E := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_filter.mp hq).2
  have hz (p : Y×Y) (hp : p ∈ E) (hn : p ∉ S.image j) : pairTerm f H p=0 := by
    by_cases h₁ : f p.1=0
    · exact pairTerm_eq_zero_left f H hf p.1 p.2 h₁
    by_cases h₂ : f p.2=0
    · exact pairTerm_eq_zero_right f H hf p.1 p.2 h₂
    obtain ⟨x,hx⟩ := (hsupport p hp).1 h₁
    obtain ⟨y,hy⟩ := (hsupport p hp).2 h₂
    have he : j (x,y)=p := Prod.ext hx hy
    exact False.elim (hn (Finset.mem_image.mpr ⟨(x,y),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [he]; exact hp⟩,he⟩))
  unfold symmetricEnergy
  rw [← Finset.sum_subset hsub hz,Finset.sum_image (fun a _ b _ h => hj h)]
  dsimp only [S]
  rw [Finset.sum_filter,Fintype.sum_prod_type]
  rfl

theorem symmetricEnergy_restrict_observable (E : Finset (Y×Y)) (f H : Y → ℝ)
    (hf : ∀ y,0 ≤ f y) (i : X → Y) (hi : Function.Injective i)
    (hsupport : ∀ p ∈ E,(f p.1≠0 → ∃ x,i x=p.1) ∧ (f p.2≠0 → ∃ x,i x=p.2))
    (h : X → ℝ) (hh : ∀ x,H (i x)=h x) :
    symmetricEnergy E f H=
      (∑ x,∑ y,if (i x,i y) ∈ E then
        min (f (i x)) (f (i y))*(h x-h y)^2 else 0)/2 := by
  rw [symmetricEnergy_restrict E f H hf i hi hsupport]
  simp_rw [hh]

end ContingencyTables.IntegerWeightedTransport

end OAI
