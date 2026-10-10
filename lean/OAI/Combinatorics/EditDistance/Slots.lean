import OAI.Combinatorics.EditDistance.Metric

namespace OAI

/-!
# Position-tagged concatenation and repeated slots
-/

namespace EditSlots
open scoped BigOperators

variable {I A : Type*} [DecidableEq I]

def project (i : I) (x : I × A) : Option A := if i = x.1 then some x.2 else none

lemma project_map (i j : I) (x : List A) :
    (x.map (Prod.mk j)).filterMap (project i) = if i = j then x else [] := by
  by_cases h : i = j <;> simp [List.filterMap_map, project, h, Function.comp_def]

def tagged (l : List I) (P : I → List A) : List (I × A) :=
  l.flatMap (fun i => (P i).map (Prod.mk i))

lemma project_tagged (l : List I) (hl : l.Nodup) (P : I → List A) (i : I) :
    (tagged l P).filterMap (project i) = if i ∈ l then P i else [] := by
  induction l with
  | nil => simp [tagged]
  | cons j l ih =>
    obtain ⟨hjl, hl⟩ := List.nodup_cons.mp hl
    simp only [tagged, List.flatMap_cons, List.filterMap_append, project_map]
    change (if i = j then P j else []) ++ (tagged l P).filterMap (project i) = _
    rw [ih hl]
    by_cases h : i = j
    · subst i
      simp [hjl]
    · simp [h]

lemma project_length_partition [Fintype I] (z : List (I × A)) :
    ∑ i, (z.filterMap (project i)).length = z.length := by
  induction z with
  | nil => simp
  | cons a z ih =>
    have hh (i : I) : ((a :: z).filterMap (project i)).length =
        (z.filterMap (project i)).length + if i = a.1 then 1 else 0 := by
      by_cases h : i = a.1 <;> simp [project, h]
    simp_rw [hh]
    rw [Finset.sum_add_distrib, ih]
    simp

omit [DecidableEq I] in
lemma tagged_length (l : List I) (P : I → List A) :
    (tagged l P).length = (l.map (fun i => (P i).length)).sum := by
  induction l with
  | nil => simp [tagged]
  | cons a l ih => simp_all [tagged]

theorem sum_indel_le_tagged [Fintype I] (l : List I) (hl : l.Nodup)
    (hfull : ∀ i : I, i ∈ l) (P Q : I → List A) :
    (∑ i, (EditDistortion.indel (P i) (Q i) : ℝ)) ≤
      (EditDistortion.indel (tagged l P) (tagged l Q) : ℝ) := by
  classical
  obtain ⟨z, hzP, hzQ, hz⟩ := EditDistortion.indel_matching (tagged l P) (tagged l Q)
  have hsubP : ∀ i, (z.filterMap (project i)).Sublist (P i) := by
    intro i
    simpa only [project_tagged l hl P i, ite_eq_left (hfull i)] using hzP.filterMap (project i)
  have hsubQ : ∀ i, (z.filterMap (project i)).Sublist (Q i) := by
    intro i
    simpa only [project_tagged l hl Q i, ite_eq_left (hfull i)] using hzQ.filterMap (project i)
  have hp (i : I) : (EditDistortion.indel (P i) (Q i) : ℝ) ≤
      ((P i).length : ℝ) + (Q i).length - 2 * (z.filterMap (project i)).length := by
    have hh := EditDistortion.indel_le_matching_loss (hsubP i) (hsubQ i)
    have h₁ := (hsubP i).length_le
    have h₂ := (hsubQ i).length_le
    have hh' : (EditDistortion.indel (P i) (Q i) : ℝ) ≤
        (((P i).length + (Q i).length - 2 * (z.filterMap (project i)).length : ℕ) : ℝ) := by
      exact_mod_cast hh
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hh'
    exact hh'
  have hlen (R : I → List A) : (tagged l R).length = ∑ i, (R i).length := by
    have hp := project_length_partition (tagged l R)
    simpa only [project_tagged l hl R, ite_eq_left (hfull _)] using hp.symm
  have hpart : (∑ i, ((z.filterMap (project i)).length : ℝ)) = z.length := by
    exact_mod_cast project_length_partition z
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hpart] at hsum
  have hz₁ := hzP.length_le
  have hz₂ := hzQ.length_le
  rw [hz, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    hlen P, hlen Q, Nat.cast_sum, Nat.cast_sum]
  exact hsum

end EditSlots

namespace EditSlots
open scoped BigOperators

lemma cost_tagged_le {I A : Type*} (l : List I) (P Q : I → List A) (s : Bool) :
    EditDistortion.cost s (tagged l P) (tagged l Q) ≤
      (l.map (fun i => EditDistortion.cost s (P i) (Q i))).sum := by
  induction l with
  | nil => exact le_of_eq (EditDistortion.cost_refl [])
  | cons i l ih =>
      have ha := EditDistortion.cost_append_le (s := s)
        ((P i).map (Prod.mk i)) ((Q i).map (Prod.mk i)) (tagged l P) (tagged l Q)
      have hm := EditDistortion.cost_map_le (s := s) (Prod.mk i) (P i) (Q i)
      exact ha.trans (by simpa only [List.map_cons, List.sum_cons] using Nat.add_le_add hm ih)

def fixedFn {A : Type*} {n : ℕ} (l : List A) (h : l.length = n) : Fin n → A :=
  fun i => l.get (Fin.cast h.symm i)

@[simp] lemma ofFn_fixedFn {A : Type*} {n : ℕ} (l : List A) (h : l.length = n) :
    List.ofFn (fixedFn l h) = l := by
  subst n
  exact List.ofFn_get l

section Repeated
variable {J : Type*} [Fintype J] [DecidableEq J] (i : J)

abbrev Slots := Fin (Fintype.card J) ⊕ {j : J // j ≠ i}

def component : Slots i → J
  | Sum.inl _ => i
  | Sum.inr j => j.val

lemma slots_card : Fintype.card (Slots i) = 2 * Fintype.card J - 1 := by
  have hb : 0 < Fintype.card J := Fintype.card_pos_iff.mpr ⟨i⟩
  simp only [Slots, Fintype.card_sum, Fintype.card_fin, Fintype.card_subtype_compl,
    Fintype.card_unique]
  omega

noncomputable def enumeration : List (Slots i) :=
  List.ofFn (Fintype.equivFin (Slots i)).symm

lemma enumeration_nodup : (enumeration i).Nodup :=
  List.nodup_ofFn_ofInjective (Fintype.equivFin (Slots i)).symm.injective

lemma enumeration_full (r : Slots i) : r ∈ enumeration i := by
  simp only [enumeration, List.mem_ofFn]
  exact ⟨(Fintype.equivFin (Slots i)) r, (Fintype.equivFin (Slots i)).symm_apply_apply r⟩

lemma sum_slots (f : J → ℝ) :
    (∑ r : Slots i, f (component i r)) =
      (Fintype.card J : ℝ) * f i + ∑ j : {j : J // j ≠ i}, f j := by
  simp [Fintype.sum_sum_type, component]

def multiplicity (j : J) : ℕ := if j = i then Fintype.card J else 1

lemma sum_slots_delta (j : J) (a : ℝ) :
    (∑ r : Slots i, if component i r = j then a else 0) = multiplicity i j * a := by
  rw [sum_slots i (fun k => if k = j then a else 0)]
  by_cases h : j = i
  · subst j
    have hz : (∑ x : {j : J // j ≠ i}, if x.val = i then a else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      simp [x.property]
    simp [hz, multiplicity]
  · have hs : (∑ x : {j : J // j ≠ i}, if x.val = j then a else 0) = a := by
      rw [Finset.sum_eq_single ⟨j,h⟩]
      · simp
      · intro x _ hx
        have hx' : x.val ≠ j := fun he => hx (Subtype.ext he)
        simp [hx']
      · simp
    simp [hs, Ne.symm h, multiplicity, h]

lemma sum_multiplicity : (∑ j : J, (multiplicity i j : ℝ)) = 2 * Fintype.card J - 1 := by
  have he (j : J) : (multiplicity i j : ℝ) =
      1 + if j = i then (Fintype.card J : ℝ) - 1 else 0 := by
    by_cases h : j = i <;> simp [multiplicity, h]
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

end Repeated
end EditSlots

end OAI
