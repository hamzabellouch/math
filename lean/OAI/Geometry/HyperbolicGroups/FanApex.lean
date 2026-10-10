import Mathlib
import OAI.Geometry.HyperbolicGroups.LinkApex

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.FanLink
open State

inductive Mark (F : Type*)
  | absent | triangle | top (f : F)
  deriving DecidableEq

namespace Mark
variable {F O : Type*}
def plain : Mark F → State
  | absent => .absent
  | triangle => .triangle
  | top _ => .dominant

def color [DecidableEq O] (occ : F → O) (a : O) : Mark F → State
  | absent => .absent
  | triangle => .triangle
  | top f => if occ f = a then .dominant else .other

lemma color_active [DecidableEq O] (occ : F → O) (a : O) (m : Mark F) :
    (m.color occ a).active = m.plain.active := by
  cases m with
  | absent => rfl
  | triangle => rfl
  | top f => by_cases h : occ f = a <;> simp [color,plain,State.active,h]
lemma color_f [DecidableEq O] (occ : F → O) (a : O) (m : Mark F) :
    (m.color occ a).f = m.plain.f := by
  cases m with
  | absent => rfl
  | triangle => rfl
  | top f => by_cases h : occ f = a <;> simp [color,plain,State.f,h]
lemma color_turn [DecidableEq O] (occ : F → O) (a : O) (m : Mark F) :
    (m.color occ a).turn = m.plain.turn := by
  cases m with
  | absent => rfl
  | triangle => rfl
  | top f => by_cases h : occ f = a <;> simp [color,plain,State.turn,h]
end Mark

/-- Combinatorial data at ONE fan occurrence in a fragment of a normalized
picture. `S` indexes all selected top faces whose occurrence has this fan slot,
including top faces that do not actually turn at this fan. The injectivity
condition is that a simple macro polygon turns at a fan at most once. -/
structure FanData (r S o : ℕ) where
  n : Fin r → ℕ
  next : (z : Fin r) → Equiv.Perm (Fin (n z))
  cyclic : ∀ z, IsCyclic (next z)
  mark : (z : Fin r) → Fin (n z) → Mark (Fin S)
  line : (z : Fin r) → Fin (n z) → Bool
  occurrence : Fin S → Fin o
  represented : ∀ z, ∃ i, mark z i ≠ .absent
  card_le : ∀ z, n z ≤ 5
  no_fixed : ∀ z i, next z i ≠ i
  bipartite : ∀ z i, mark z i = .triangle → line z i ≠ line z (next z i)
  no_backtrack : ∀ z i, mark z i = .triangle → mark z (next z i) = .triangle →
    next z (next z i) ≠ i
  no_same_side : ∀ z i f g, mark z i = .top f → mark z (next z i) = .top g →
    occurrence f ≠ occurrence g
  unique_turn : ∀ (p q : Σ z, Fin (n z)) f,
    mark p.1 p.2 = .top f → mark q.1 q.2 = .top f → p = q

namespace FanData
variable {r S o : ℕ} (L : FanData r S o)

def state (z : Fin r) := Mark.plain ∘ L.mark z
def colored (a : Fin o) (z : Fin r) := Mark.color L.occurrence a ∘ L.mark z

def triangles : ℕ := ∑ z, Q (L.state z)
def turns : ℕ := ∑ z, T (L.state z)
def payments : ℕ := ∑ z, P (L.next z) (L.state z) (L.line z)
def boundary : ℕ := ∑ z, B (L.next z) (L.state z)
def isPartial (z : Fin r) : Prop := ∃ i, L.mark z i = .absent
instance partialDecidable (z : Fin r) : Decidable (L.isPartial z) := inferInstanceAs (Decidable (∃ i, L.mark z i = .absent))
def partialCount : ℕ := ∑ z, if L.isPartial z then 1 else 0

def multiplicity (a : Fin o) : ℕ := Fintype.card {f : Fin S // L.occurrence f = a}
def maxMultiplicity : ℕ := Finset.univ.sup L.multiplicity
def weight : ℕ := max r L.maxMultiplicity

lemma count_le (R : Fin S → Prop) [DecidablePred R] :
    (∑ z, ∑ i, match L.mark z i with
      | .top f => if R f then (1:ℕ) else 0
      | _ => 0) ≤ Fintype.card {f : Fin S // R f} := by
  classical
  let Idx := {p : Σ z, Fin (L.n z) // ∃ f, L.mark p.1 p.2 = .top f ∧ R f}
  let g : Idx → {f : Fin S // R f} := fun p =>
    ⟨p.property.choose,p.property.choose_spec.2⟩
  have hg : Function.Injective g := by
    intro p q hpq
    apply Subtype.ext
    apply L.unique_turn p.val q.val p.property.choose p.property.choose_spec.1
    have hval := congrArg Subtype.val hpq
    change p.property.choose = q.property.choose at hval
    rw [hval]
    exact q.property.choose_spec.1
  have h := Fintype.card_le_of_injective g hg
  have hcard : Fintype.card Idx = (∑ z, ∑ i, match L.mark z i with
      | .top f => if R f then (1:ℕ) else 0
      | _ => 0) := by
    rw [show Fintype.card Idx = _ from Fintype.card_subtype _]
    have hh := Finset.sum_boole (R := ℕ)
      (fun p : Σ z, Fin (L.n z) => ∃ f, L.mark p.1 p.2 = .top f ∧ R f) Finset.univ
    simp only [Nat.cast_id] at hh
    rw [← hh,Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro i _
    cases L.mark z i <;> simp
  rwa [hcard] at h

lemma turns_le : L.turns ≤ S := by
  have h := L.count_le (fun _ => True)
  simp only [Fintype.card_subtype_true,Fintype.card_fin,ite_true] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro i _
  cases he : L.mark z i <;> simp [state,Mark.plain,State.turn,he]

lemma color_counts (a : Fin o) :
    (∑ z, D (L.colored a z)) + (∑ z, N (L.colored a z)) = L.turns := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  rw [← T_eq]
  apply Finset.sum_congr rfl
  intro i _
  exact Mark.color_turn _ _ _

lemma other_count_le (a : Fin o) : (∑ z, N (L.colored a z)) ≤ S - L.multiplicity a := by
  have h := L.count_le (fun f => L.occurrence f ≠ a)
  rw [Fintype.card_subtype_compl,Fintype.card_fin] at h
  convert h using 1
  · apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro i _
    cases he : L.mark z i with
    | absent => simp [colored,Mark.color,State.n,he]
    | triangle => simp [colored,Mark.color,State.n,he]
    | top f => by_cases hf : L.occurrence f = a <;> simp [colored,Mark.color,State.n,he,hf]
  · rfl

lemma multiplicity_le (a : Fin o) : L.multiplicity a ≤ S := by
  simpa [multiplicity] using (Fintype.card_le_of_injective
    (Subtype.val : {f : Fin S // L.occurrence f = a} → Fin S) Subtype.val_injective)

lemma color_Q (a : Fin o) (z : Fin r) : Q (L.colored a z) = Q (L.state z) := by
  apply Finset.sum_congr rfl
  intro i _
  exact Mark.color_f _ _ _
lemma color_P (a : Fin o) (z : Fin r) :
    P (L.next z) (L.colored a z) (L.line z) = P (L.next z) (L.state z) (L.line z) := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [colored,state,Function.comp_apply,Mark.color_turn]
lemma color_B (a : Fin o) (z : Fin r) :
    B (L.next z) (L.colored a z) = B (L.next z) (L.state z) := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [State.boundary,colored,state,Function.comp_apply,Mark.color_active]
  rfl

lemma state_full (z : Fin r) (h : ¬ L.isPartial z) : ∀ i, (L.state z i).active = true := by
  intro i
  have hi : L.mark z i ≠ .absent := fun hi => h ⟨i,hi⟩
  cases he : L.mark z i <;> simp_all [state,Mark.plain,State.active]

lemma boundary_le (z : Fin r) :
    B (L.next z) (L.state z) ≤ 4 * (if L.isPartial z then 1 else 0) := by
  split_ifs with hp
  · simpa using boundary_le_four (L.next z) (L.state z) (by simpa using L.card_le z)
  · rw [boundary_full _ _ (L.state_full z hp)]

lemma partial_le_boundary : 2 * L.partialCount ≤ L.boundary := by
  have h : ∀ z, 2 * (if L.isPartial z then 1 else 0) ≤ B (L.next z) (L.state z) := by
    intro z
    split_ifs with hp
    · obtain ⟨j,hj⟩ := hp
      obtain ⟨i,hi⟩ := L.represented z
      apply partial_boundary (L.next z) (L.cyclic z) (L.state z)
      · refine ⟨i,?_⟩
        cases he : L.mark z i <;> simp_all [state,Mark.plain,State.active]
      · exact ⟨j,by simp [state,hj,Mark.plain,State.active]⟩
    · simp
  simpa only [partialCount,boundary,Finset.mul_sum] using Finset.sum_le_sum (s := Finset.univ) (fun z _ => h z)

lemma one_instance_bound (z : Fin r) :
    (4:ℝ) - 2 * T (L.state z) ≤ (Q (L.state z):ℝ) + P (L.next z) (L.state z) (L.line z) +
      4 * (if L.isPartial z then 1 else 0) := by
  by_cases hp : L.isPartial z
  · simp only [hp,ite_true,mul_one]
    have ht : (0:ℝ) ≤ T (L.state z) := Nat.cast_nonneg _
    have hq : (0:ℝ) ≤ Q (L.state z) := Nat.cast_nonneg _
    have hp : (0:ℝ) ≤ P (L.next z) (L.state z) (L.line z) := Nat.cast_nonneg _
    linarith
  · simp only [hp,ite_false,mul_zero,add_zero]
    obtain ⟨i,_⟩ := L.represented z
    let : Nonempty (Fin (L.n z)) := ⟨i⟩
    apply full_instance_bound (L.next z) (L.state z) (L.line z) (L.state_full z hp) (L.no_fixed z)
    · intro i hi
      apply L.bipartite z i
      cases he : L.mark z i <;> simp_all [state,Mark.plain]
    · intro i hi hj
      apply L.no_backtrack z i
      · cases he : L.mark z i <;> simp_all [state,Mark.plain]
      · cases he : L.mark z (L.next z i) <;> simp_all [state,Mark.plain]

lemma r_case_bound :
    (4:ℝ) * r - 2 * L.turns ≤ (L.triangles:ℝ) + L.payments + 4 * L.partialCount := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun z _ => L.one_instance_bound z)
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
  have hj : (∑ z : Fin r, if L.isPartial z then (1:ℝ) else 0) = (L.partialCount : ℝ) := by
    simp [partialCount]
  simp only [hj] at h
  simpa [turns,triangles,payments,Nat.cast_sum,mul_comm] using h

lemma dominant_bound (a : Fin o) :
    2 * (∑ z, D (L.colored a z)) ≤ 2 * (∑ z, N (L.colored a z)) +
      L.triangles + L.payments + 4 * L.partialCount := by
  have h : ∀ z, 2 * D (L.colored a z) ≤ 2 * N (L.colored a z) + Q (L.state z) +
      P (L.next z) (L.state z) (L.line z) + 4 * (if L.isPartial z then 1 else 0) := by
    intro z
    have hc : ∀ i, ¬ (L.colored a z i = dominant ∧ L.colored a z (L.next z i) = dominant) := by
      intro i ⟨hi,hj⟩
      obtain ⟨f,hf,hfa⟩ : ∃ f, L.mark z i = .top f ∧ L.occurrence f = a := by
        cases he : L.mark z i <;> simp_all [colored,Mark.color]
      obtain ⟨g,hg,hga⟩ : ∃ g, L.mark z (L.next z i) = .top g ∧ L.occurrence g = a := by
        cases he : L.mark z (L.next z i) <;> simp_all [colored,Mark.color]
      exact L.no_same_side z i f g hf hg (hfa.trans hga.symm)
    have hb : ∀ i, L.colored a z i = triangle → L.line z i ≠ L.line z (L.next z i) := by
      intro i hi
      apply L.bipartite z i
      cases he : L.mark z i with
      | absent => simp_all [colored,Mark.color]
      | triangle => rfl
      | top f => by_cases hf : L.occurrence f = a <;> simp_all [colored,Mark.color]
    have hh := dominant_endpoint_bound (L.next z) (L.colored a z) (L.line z) hc hb
    rw [L.color_Q a z,L.color_P a z,L.color_B a z] at hh
    exact hh.trans (Nat.add_le_add_left (L.boundary_le z) _)
  simpa only [triangles,payments,partialCount,Finset.sum_add_distrib,← Finset.mul_sum]
    using Finset.sum_le_sum (s := Finset.univ) (fun z _ => h z)

/-- Full source per-fan apex inequality, including omission of the fan by some
selected top faces and shared dominant occurrences. It follows from the actual
cyclic-link/side conditions and the simple-polygon injection above. -/
theorem apex_bound :
    (L.turns:ℝ) + 2 * ((L.weight:ℝ) - S) ≤
      ((L.triangles:ℝ) + L.payments) / 2 + 2 * L.partialCount := by
  by_cases hm : L.maxMultiplicity ≤ r
  · have hw : L.weight = r := max_eq_left hm
    rw [hw]
    have ht : (L.turns:ℝ) ≤ S := by exact_mod_cast L.turns_le
    have hh := L.r_case_bound
    linarith
  · have hm' : r < L.maxMultiplicity := lt_of_not_ge hm
    have ho : 0 < o := by
      by_contra! ho
      have ho' : o = 0 := Nat.eq_zero_of_le_zero ho
      subst o
      simp [maxMultiplicity] at hm'
    have hne : (Finset.univ : Finset (Fin o)).Nonempty := ⟨⟨0,ho⟩,Finset.mem_univ _⟩
    obtain ⟨a,_,ha⟩ := Finset.exists_mem_eq_sup Finset.univ hne L.multiplicity
    have hw : L.weight = L.multiplicity a := (max_eq_right (le_of_lt hm')).trans ha
    rw [hw]
    have hn := L.other_count_le a
    have hmS := L.multiplicity_le a
    have hn' : ((∑ z, N (L.colored a z)):ℝ) ≤ (S:ℝ) - L.multiplicity a := by
      have hh : (((∑ z, N (L.colored a z)) + L.multiplicity a : ℕ):ℝ) ≤ S := by
        exact_mod_cast (show (∑ z, N (L.colored a z)) + L.multiplicity a ≤ S by omega)
      push_cast at hh
      linarith
    have hc : ((∑ z, D (L.colored a z)):ℝ) + (∑ z, N (L.colored a z)) = L.turns := by
      exact_mod_cast L.color_counts a
    have hd : 2 * ((∑ z, D (L.colored a z)):ℝ) ≤ 2 * ((∑ z, N (L.colored a z)):ℝ) +
        L.triangles + L.payments + 4 * L.partialCount := by exact_mod_cast L.dominant_bound a
    push_cast at hn' hc hd ⊢
    linarith

lemma triangles_le : L.triangles ≤ 5 * L.weight := by
  have h : ∀ z, Q (L.state z) ≤ 5 := by
    intro z
    calc
      _ ≤ ∑ _ : Fin (L.n z), 1 := by
        apply Finset.sum_le_sum
        intro i _
        cases L.state z i <;> decide
      _ = L.n z := by simp
      _ ≤ 5 := L.card_le z
  have hh : L.triangles ≤ 5*r := by
    simpa [triangles,mul_comm] using Finset.sum_le_sum (s := Finset.univ) (fun z _ => h z)
  exact hh.trans (Nat.mul_le_mul_left 5 (le_max_left _ _))

end FanData
end HyperbolicObstruction.FanLink
end
end

section

end
end

end OAI
