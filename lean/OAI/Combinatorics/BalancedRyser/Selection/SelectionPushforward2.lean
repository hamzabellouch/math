import OAI.Combinatorics.BalancedRyser.Selection.SelectionPushforward

namespace OAI

namespace Balanced.FinitePushforward

open Finset

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

omit [Fintype B] in
theorem pushWeight_nonneg (f : A → B) (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (b : B) :
    0 ≤ pushWeight f w b := by
  apply sum_nonneg
  intro a _
  split_ifs
  · exact hw a
  · exact le_rfl

theorem sum_pushWeight (f : A → B) (w : A → ℝ) :
    ∑ b, pushWeight f w b = ∑ a, w a := by
  unfold pushWeight
  rw [sum_comm]
  simp

theorem eventMass_pushWeight (f : A → B) (w : A → ℝ)
    (P : B → Prop) [DecidablePred P] :
    (∑ b, if P b then pushWeight f w b else 0) =
      ∑ a, if P (f a) then w a else 0 := by
  classical
  unfold pushWeight
  calc
    (∑ b, if P b then ∑ a, if f a = b then w a else 0 else 0) =
        ∑ b, ∑ a, if P b then (if f a = b then w a else 0) else 0 := by
      apply sum_congr rfl
      intro b _
      split_ifs <;> simp
    _ = ∑ a, ∑ b, if P b then (if f a = b then w a else 0) else 0 := sum_comm
    _ = ∑ a, if P (f a) then w a else 0 := by
      apply sum_congr rfl
      intro a _
      rw [sum_eq_single (f a)]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · simp

omit [Fintype B] in

theorem exists_positive_preimage (f : A → B) (w : A → ℝ)
    (hw : ∀ a, 0 ≤ w a) (b : B) (hb : 0 < pushWeight f w b) :
    ∃ a, f a = b ∧ 0 < w a := by
  classical
  have hn : ∀ a ∈ (univ : Finset A), 0 ≤ (if f a = b then w a else 0) := by
    intro a _
    split_ifs
    · exact hw a
    · exact le_rfl
  obtain ⟨a, _, ha⟩ := (sum_pos_iff_of_nonneg hn).mp hb
  by_cases he : f a = b
  · exact ⟨a, he, by simpa [he] using ha⟩
  · simp [he] at ha

omit [Fintype B] in
theorem pushWeight_support (f : A → B) (w : A → ℝ)
    (hw : ∀ a, 0 ≤ w a) (P : B → Prop)
    (hsupport : ∀ a, 0 < w a → P (f a)) (b : B)
    (hb : 0 < pushWeight f w b) : P b := by
  obtain ⟨a, rfl, ha⟩ := exists_positive_preimage f w hw b hb
  exact hsupport a ha

theorem exists_supported_decoder {I V L : Type*} [Nonempty V]
    (allowed : I → V → Prop) (label : I → V → L)
    (hinj : ∀ i, Set.InjOn (label i) {v | allowed i v}) :
    ∃ decode : I → L → V, ∀ i v, allowed i v → decode i (label i v) = v := by
  classical
  let decode : I → L → V := fun i l =>
    if h : ∃ v, allowed i v ∧ label i v = l then Classical.choose h
    else Classical.choice (inferInstance : Nonempty V)
  refine ⟨decode, ?_⟩
  intro i v hv
  have hex : ∃ u, allowed i u ∧ label i u = label i v := ⟨v, hv, rfl⟩
  dsimp [decode]
  rw [dite_eq_left hex]
  exact hinj i (Classical.choose_spec hex).1 hv (Classical.choose_spec hex).2

theorem cylinderMass_pushWeight_le {I V L : Type*}
    [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype L] [DecidableEq L]
    (w : (I → V) → ℝ) (hw : ∀ t, 0 ≤ w t)
    (allowed : I → V → Prop) (label : I → V → L)
    (hsupport : ∀ t, 0 < w t → ∀ i, allowed i (t i))
    (hinj : ∀ i, Set.InjOn (label i) {v | allowed i v})
    (b : Finset I → ℝ)
    (hbound : ∀ J a, cylinderMass w J a ≤ b J)
    (J : Finset I) (prescribed : I → L) :
    cylinderMass (pushWeight (mapChoices label) w) J prescribed ≤ b J := by
  classical
  obtain ⟨decode, hdecode⟩ := exists_supported_decoder allowed label hinj
  let a : I → V := fun i => decode i (prescribed i)
  have himp : ∀ t, 0 < w t →
      (∀ i ∈ J, label i (t i) = prescribed i) → ∀ i ∈ J, t i = a i := by
    intro t ht hp i hi
    dsimp [a]
    rw [← hp i hi]
    exact (hdecode i (t i) (hsupport t ht i)).symm
  unfold cylinderMass
  rw [eventMass_pushWeight]
  have hpoint : ∀ t,
      (if ∀ i ∈ J, mapChoices label t i = prescribed i then w t else 0) ≤
        (if ∀ i ∈ J, t i = a i then w t else 0) := by
    intro t
    by_cases hz : w t = 0
    · simp [hz]
    have ht : 0 < w t := lt_of_le_of_ne (hw t) (Ne.symm hz)
    by_cases hp : ∀ i ∈ J, mapChoices label t i = prescribed i
    · have ha : ∀ i ∈ J, t i = a i := himp t ht hp
      rw [ite_eq_left hp, ite_eq_left ha]
    · simp only [ite_eq_right hp]
      split_ifs
      · exact hw t
      · exact le_rfl
  exact (sum_le_sum fun t _ => hpoint t).trans (hbound J a)

end Balanced.FinitePushforward

namespace Balanced.Selection

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I V L : Type*} [Fintype I] [Fintype V] [Fintype L]
    {G : Input I V}

theorem labelWeight_nonneg (law : OutputLaw G) (label : I → V → L) (s : I → L) :
    0 ≤ law.labelWeight label s :=
  FinitePushforward.pushWeight_nonneg _ _ law.nonnegative s

theorem sum_labelWeight (law : OutputLaw G) (label : I → V → L) :
    ∑ s, law.labelWeight label s = successMass law :=
  FinitePushforward.sum_pushWeight _ _

theorem sum_labelWeight_le_one (law : OutputLaw G) (label : I → V → L) :
    ∑ s, law.labelWeight label s ≤ 1 := by
  rw [sum_labelWeight]
  exact law.mass_le_one

theorem labelWeight_cylinder_le [Nonempty V] (law : OutputLaw G) (label : I → V → L)
    (hinj : ∀ i, Set.InjOn (label i) {v | G.slot v = i})
    (b : Finset I → ℝ)
    (hbound : ∀ J a, cylinderMass law J a ≤ b J)
    (J : Finset I) (prescribed : I → L) :
    FinitePushforward.cylinderMass (law.labelWeight label) J prescribed ≤ b J := by
  apply FinitePushforward.cylinderMass_pushWeight_le law.weight law.nonnegative
    (fun i v => G.slot v = i) label
    (fun t ht => (law.supported t ht).1) hinj b
  intro J a
  simpa only [cylinderMass, FinitePushforward.cylinderMass, Finset.sum_filter] using hbound J a

end
end Balanced.Selection

end OAI
