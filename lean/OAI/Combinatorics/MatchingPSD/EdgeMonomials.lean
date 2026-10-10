import OAI.Combinatorics.MatchingPSD.ScalarSmoothing

namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
namespace Pairing
variable {V : Type u_1}

noncomputable def edgeMonomial (l : List (V × V)) : Pairing V → ℝ :=
  (l.map edgeCoord).prod

def ContainsList (M : Pairing V) (l : List (V × V)) : Prop :=
  ∀ e ∈ l, M.1 e.1 = e.2

noncomputable def edgeSupport (l : List (V × V)) : Finset V :=
  l.toFinset.image Prod.fst ∪ l.toFinset.image Prod.snd

lemma mem_edgeSupport (l : List (V × V)) (v : V) :
    v ∈ edgeSupport l ↔ ∃ e ∈ l, v = e.1 ∨ v = e.2 := by
  simp only [edgeSupport, Finset.mem_union, Finset.mem_image, List.mem_toFinset]
  constructor
  · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
    · exact ⟨e, he, Or.inl rfl⟩
    · exact ⟨e, he, Or.inr rfl⟩
  · rintro ⟨e, he, h | h⟩
    · exact Or.inl ⟨e, he, h.symm⟩
    · exact Or.inr ⟨e, he, h.symm⟩

lemma edgeMonomial_eq_indicator (l : List (V × V)) (M : Pairing V) :
    edgeMonomial l M = if ContainsList M l then 1 else 0 := by
  induction l with
  | nil => simp [edgeMonomial, ContainsList]
  | cons e l ih =>
    simp only [edgeMonomial, List.map_cons, List.prod_cons, Pi.mul_apply] at ih ⊢
    rw [ih]
    simp only [ContainsList, List.mem_cons, forall_eq_or_imp, edgeCoord]
    split_ifs <;> simp_all

lemma edgeMonomial_cons (e : V × V) (l : List (V × V)) :
    edgeMonomial (e::l) = edgeCoord e * edgeMonomial l := by
  simp [edgeMonomial]

lemma contains_partner_support {M : Pairing V} {l : List (V × V)}
    (hm : ContainsList M l) {v : V} (hv : v ∈ edgeSupport l) :
    M.1 v ∈ edgeSupport l := by
  obtain ⟨e, he, rfl | rfl⟩ := (mem_edgeSupport l v).mp hv
  · rw [hm e he]
    exact (mem_edgeSupport l e.2).mpr ⟨e, he, Or.inr rfl⟩
  · rw [(partner_eq_iff M e.1 e.2).mp (hm e he)]
    exact (mem_edgeSupport l e.1).mpr ⟨e, he, Or.inl rfl⟩

lemma contains_agree_support {M N : Pairing V} {l : List (V × V)}
    (hm : ContainsList M l) (hn : ContainsList N l) {v : V}
    (hv : v ∈ edgeSupport l) : M.1 v = N.1 v := by
  obtain ⟨e, he, rfl | rfl⟩ := (mem_edgeSupport l v).mp hv
  · rw [hm e he, hn e he]
  · rw [(partner_eq_iff M e.1 e.2).mp (hm e he),
      (partner_eq_iff N e.1 e.2).mp (hn e he)]

lemma redundant_edgeMonomial {M : Pairing V} {e : V × V} {l : List (V × V)}
    (he : M.1 e.1 = e.2) (hm : ContainsList M l)
    (hv : e.1 ∈ edgeSupport l ∨ e.2 ∈ edgeSupport l) :
    edgeMonomial (e::l) = edgeMonomial l := by
  funext N
  simp only [edgeMonomial_eq_indicator]
  congr 1
  simp only [ContainsList, List.mem_cons, forall_eq_or_imp]
  apply propext
  refine and_iff_right_of_imp ?_
  intro hn
  change ContainsList N l at hn
  rcases hv with hv | hv
  · exact (contains_agree_support hn hm hv).trans he
  · apply (partner_eq_iff N e.1 e.2).mpr
    exact (contains_agree_support hn hm hv).trans ((partner_eq_iff M e.1 e.2).mp he)

lemma edgeMonomial_zero_of_unsatisfiable (l : List (V × V))
    (h : ¬ ∃ M : Pairing V, ContainsList M l) : edgeMonomial l = 0 := by
  funext M
  rw [edgeMonomial_eq_indicator, ite_eq_right (fun hm => h ⟨M, hm⟩)]
  rfl

lemma edgeMonomial_act_fix (l : List (V × V)) (p : Equiv.Perm V)
    (hp : ∀ v ∈ edgeSupport l, p v = v) : act p (edgeMonomial l) = edgeMonomial l := by
  funext M
  simp only [act_apply, edgeMonomial_eq_indicator]
  congr 1
  apply propext
  apply forall₂_congr
  intro e he
  have h₁ := hp e.1 ((mem_edgeSupport l e.1).mpr ⟨e, he, Or.inl rfl⟩)
  have h₂ := hp e.2 ((mem_edgeSupport l e.2).mpr ⟨e, he, Or.inr rfl⟩)
  simp only [relabel_apply, inv_inv]
  rw [h₁, Equiv.Perm.inv_def, p.symm_apply_eq, h₂]

end Pairing

section ColorAverage
variable {V : Type u_2} {C : Type u_3} [Fintype V]

def colorStabilizer (z : V → C) : Subgroup (Equiv.Perm V) where
  carrier := {p | ∀ v, z (p v) = z v}
  one_mem' := fun _ => rfl
  mul_mem' := by intro p q hp hq v; exact (hp (q v)).trans (hq v)
  inv_mem' := by intro p hp v; simpa using (hp (p⁻¹ v)).symm

noncomputable def colorAverage (z : V → C) : Module.End ℝ (Pairing V → ℝ) :=
  (Fintype.card (colorStabilizer z) : ℝ)⁻¹ •
    ∑ p : colorStabilizer z, (Pairing.act p.1).toLinearMap

lemma colorAverage_apply (z : V → C) (f : Pairing V → ℝ) (M : Pairing V) :
    colorAverage z f M =
      (∑ p : colorStabilizer z, Pairing.act p.1 f M) / Fintype.card (colorStabilizer z) := by
  simp [colorAverage, div_eq_mul_inv, mul_comm]

lemma colorAverage_act (z : V → C) (q : colorStabilizer z) (f : Pairing V → ℝ) :
    colorAverage z (Pairing.act q.1 f) = colorAverage z f := by
  funext M
  simp only [colorAverage_apply, ← Pairing.act_mul]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight q) (fun p : colorStabilizer z => Pairing.act p.1 f M)

lemma colorAverage_one (z : V → C) : colorAverage z (1 : Pairing V → ℝ) = 1 := by
  funext M
  simp [colorAverage_apply, Pairing.act_apply, Fintype.card_ne_zero]

lemma colorAverage_mul_invariant (z : V → C) (f g : Pairing V → ℝ)
    (hf : ∀ p : colorStabilizer z, Pairing.act p.1 f = f) :
    colorAverage z (f*g) = f * colorAverage z g := by
  funext M
  simp only [colorAverage_apply, Pi.mul_apply, Pairing.act_apply]
  have h (p : colorStabilizer z) : f (Pairing.relabel p.1⁻¹ M) = f M := congrFun (hf p) M
  simp_rw [h, ← Finset.mul_sum, mul_div_assoc]

end ColorAverage
end MatchingSmoothing

end OAI
