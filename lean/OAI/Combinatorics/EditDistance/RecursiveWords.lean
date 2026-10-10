import OAI.Combinatorics.EditDistance.RecursiveControl
import OAI.Combinatorics.EditDistance.RowConstruction
import OAI.Combinatorics.EditDistance.PrimePeriods

namespace OAI

/-!
# Recursive payloads, markers, symbol codes, and word separation
-/

namespace EditFamily
open scoped BigOperators
open EditDistortion EditAverage EditFourier EditSlots

lemma torsionHom_intCast {G : Type*} [AddCommGroup G] (p : ℕ) (v : G) (hv : p • v = 0)
    (a : ℤ) : torsionHom p v hv (a : ZMod p) = a • v := by
  simp [torsionHom]

lemma Family.far_int {p m A : ℕ} {α Q : ℝ} (F : Family p m A α Q)
    (hp : 0 < p) (z : F.State) (a : ℤ) (ha : ¬ (p : ℤ) ∣ a) :
    (m : ℝ) * α ≤ (indel (List.ofFn (F.word z)) (List.ofFn (F.word (z + a • F.v))) : ℝ) := by
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  let x : ZMod p := a
  have hx : x ≠ 0 := fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)
  have hv : x.val • F.v = a • F.v := by
    rw [← torsionHom_apply p F.v F.annihilate x]
    exact torsionHom_intCast p F.v F.annihilate a
  rw [← hv]
  exact F.far z x.val (Nat.pos_of_ne_zero (fun h => hx ((ZMod.val_eq_zero x).mp h))) (ZMod.val_lt x)

section Words
variable {J : Type} [Fintype J] [DecidableEq J] (i : J)
variable {p : J → ℕ} {m A : ℕ} {α Q : ℝ}
variable (F : ∀ j, Family (p j) m A α Q)

noncomputable def payloadList (z : ProductState F) (row : ℕ) : List (Slots i × Fin A) :=
  tagged (enumeration i) (fun r => List.ofFn ((F (component i r)).word
    (z (component i r) + row • (F (component i r)).v)))

lemma payload_length (z : ProductState F) (row : ℕ) :
    (payloadList i F z row).length = (2 * Fintype.card J - 1) * m := by
  rw [payloadList, tagged_length, enumeration, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply, List.length_ofFn, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, slots_card, Nat.cast_id]

noncomputable def payloadFn (z : ProductState F) (row : ℕ) :
    Fin ((2 * Fintype.card J - 1) * m) → (Slots i × Fin A) :=
  fixedFn (payloadList i F z row) (payload_length i F z row)

@[simp] lemma ofFn_payloadFn (z : ProductState F) (row : ℕ) :
    List.ofFn (payloadFn i F z row) = payloadList i F z row := ofFn_fixedFn _ _

noncomputable def rawWord (L : ℕ) (z : ProductState F) : List (Option (Slots i × Fin A)) :=
  EditRows.rowWord (fun row : Fin L => payloadFn i F z row.val)

@[simp] lemma rawWord_length (L : ℕ) (z : ProductState F) :
    (rawWord i F L z).length = 2 * ((2 * Fintype.card J - 1) * m) * L :=
  EditRows.rowWord_length _

omit [Fintype J] in
lemma shift_state (z : ProductState F) (u row row' : ℕ) (j : J) :
    (z + u • lift F i (F i).v) j + row' • (F j).v =
      (z j + row • (F j).v) +
        ((row' : ℤ) - (row : ℤ) + if j = i then (u : ℤ) else 0) • (F j).v := by
  by_cases hj : j = i
  · subst j
    simp only [Pi.add_apply, Pi.smul_apply, lift, Pi.single_eq_same]
    simp [add_zsmul, sub_zsmul]
    abel
  · simp only [Pi.add_apply, Pi.smul_apply, lift, Pi.single_eq_of_ne hj, smul_zero,
      ite_eq_right hj, add_zero, sub_zsmul, natCast_zsmul]
    abel

noncomputable def componentDistance (z z' : ProductState F) (row row' : ℕ) (j : J) : ℝ :=
  indel (List.ofFn ((F j).word (z j + row • (F j).v)))
    (List.ofFn ((F j).word (z' j + row' • (F j).v)))

omit [Fintype J] [DecidableEq J] in
lemma componentDistance_nonneg (z z' : ProductState F) (row row' : ℕ) (j : J) :
    0 ≤ componentDistance F z z' row row' j := Nat.cast_nonneg _

lemma payload_distance_ge_sum (z z' : ProductState F) (row row' : ℕ) :
    (∑ r : Slots i, componentDistance F z z' row row' (component i r)) ≤
      (indel (payloadList i F z row) (payloadList i F z' row') : ℝ) := by
  exact sum_indel_le_tagged (enumeration i) (enumeration_nodup i) (enumeration_full i) _ _

omit [Fintype J] in
lemma componentDistance_far (hp : ∀ j, (p j).Prime)
    (z : ProductState F) (u row row' : ℕ) (j : J)
    (ha : ¬ (p j : ℤ) ∣ ((row' : ℤ) - (row : ℤ) + if j = i then (u : ℤ) else 0)) :
    (m : ℝ) * α ≤ componentDistance F z (z + u • lift F i (F i).v) row row' j := by
  unfold componentDistance
  rw [shift_state]
  exact (F j).far_int (hp j).pos _ _ ha

lemma payload_separation
    (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    (P : ℕ) (hP : 1 ≤ P) (hpP : ∀ j, P ≤ p j) (hα : 0 ≤ α)
    (z : ProductState F) (u : ℕ) (hu0 : 0 < u) (hu : u < p i)
    (row row' : ℕ) (hr : row < P ^ (Fintype.card J / 2))
    (hr' : row' < P ^ (Fintype.card J / 2)) :
    α * Fintype.card J * m / 3 ≤
      (indel (payloadList i F z row)
        (payloadList i F (z + u • lift F i (F i).v) row') : ℝ) := by
  let D := componentDistance F z (z + u • lift F i (F i).v) row row'
  have hDn (j : J) : 0 ≤ D j := componentDistance_nonneg F _ _ _ _ j
  have hsum := payload_distance_ge_sum i F z (z + u • lift F i (F i).v) row row'
  rw [sum_slots] at hsum
  change (Fintype.card J : ℝ) * D i + ∑ j : {j : J // j ≠ i}, D j ≤ _ at hsum
  have hma : 0 ≤ (m : ℝ) * α := mul_nonneg (Nat.cast_nonneg _) hα
  have hrest : 0 ≤ ∑ j : {j : J // j ≠ i}, D j := Finset.sum_nonneg (fun j _ => hDn j)
  by_cases hphase : ¬(p i : ℤ) ∣ ((row' : ℤ) - row + u)
  · have hf : (m : ℝ) * α ≤ D i := by
      exact componentDistance_far i F hp z u row row' i (by simpa using hphase)
    have hmul := mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg (Fintype.card J) : (0 : ℝ) ≤ _)
    have hbma : 0 ≤ (Fintype.card J : ℝ) * ((m : ℝ) * α) := mul_nonneg (Nat.cast_nonneg _) hma
    nlinarith
  · push Not at hphase
    let q : ℤ := (row' : ℤ) - row
    have hq : q ≠ 0 := by
      intro hq
      have hd : (p i : ℤ) ∣ (u : ℤ) := by simpa [q, hq] using hphase
      have hd' : p i ∣ u := by exact_mod_cast hd
      exact Nat.not_dvd_of_pos_of_lt hu0 hu hd'
    have hqr : q.natAbs < P ^ (Fintype.card J / 2) := by
      apply Int.ofNat_lt.mp
      rw [Int.natCast_natAbs]
      apply abs_lt.mpr
      dsimp [q]
      have hrZ : (row : ℤ) < (P : ℤ) ^ (Fintype.card J / 2) := by exact_mod_cast hr
      have hrZ' : (row' : ℤ) < (P : ℤ) ^ (Fintype.card J / 2) := by exact_mod_cast hr'
      constructor <;> omega
    let S := Finset.univ.filter (fun j => j ≠ i ∧ ¬(p j : ℤ) ∣ q)
    have hc : Fintype.card J - Fintype.card J / 2 ≤ S.card :=
      EditPhase.many_nonzero_phases p hp hinj hP hpP hq hqr i
    have hbc : (Fintype.card J : ℝ) / 3 ≤ (S.card : ℝ) := by
      have hn : Fintype.card J ≤ 3 * (Fintype.card J - Fintype.card J / 2) := by omega
      have hn' : (Fintype.card J : ℝ) ≤ 3 * ((Fintype.card J - Fintype.card J / 2 : ℕ) : ℝ) := by
        exact_mod_cast hn
      have hc' : ((Fintype.card J - Fintype.card J / 2 : ℕ) : ℝ) ≤ (S.card : ℝ) := by
        exact_mod_cast hc
      linarith
    have hS : (S.card : ℝ) * ((m : ℝ) * α) ≤ ∑ j ∈ S, D j := by
      calc
        _ = ∑ _j ∈ S, (m : ℝ) * α := by simp
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro j hj
          obtain ⟨hji, hdiv⟩ := (Finset.mem_filter.mp hj).2
          exact componentDistance_far i F hp z u row row' j (by simpa [hji, q] using hdiv)
    have hsub : S ⊆ Finset.univ.erase i := by
      intro j hj
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact (Finset.mem_filter.mp hj).2.1
    have hSrest : ∑ j ∈ S, D j ≤ ∑ j : {j : J // j ≠ i}, D j := by
      rw [← Finset.sum_subtype (Finset.univ.erase i) (by simp) D]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hDn j)
    have hbound := mul_le_mul_of_nonneg_right hbc hma
    have hdi : 0 ≤ (Fintype.card J : ℝ) * D i := mul_nonneg (Nat.cast_nonneg _) (hDn i)
    nlinarith

theorem rawWord_far
    (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    (P : ℕ) (hP : 1 ≤ P) (hpP : ∀ j, P ≤ p j) (hm : 0 < m)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (z : ProductState F) (u : ℕ) (hu0 : 0 < u) (hu : u < p i) :
    (2 * ((2 * Fintype.card J - 1) * m) * P ^ (Fintype.card J / 2) : ℕ) * (α / 24) ≤
      (indel (rawWord i F (P ^ (Fintype.card J / 2)) z)
        (rawWord i F (P ^ (Fintype.card J / 2)) (z + u • lift F i (F i).v)) : ℝ) := by
  have hb : 1 ≤ Fintype.card J := Fintype.card_pos_iff.mpr ⟨i⟩
  have hB : 0 < (2 * Fintype.card J - 1) * m := Nat.mul_pos (by omega) hm
  have hbR : (1 : ℝ) ≤ Fintype.card J := by exact_mod_cast hb
  have hcast : ((2 * Fintype.card J - 1 : ℕ) : ℝ) = 2 * (Fintype.card J : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  have htB : α * Fintype.card J * m / 6 ≤ (((2 * Fintype.card J - 1) * m : ℕ) : ℝ) := by
    rw [Nat.cast_mul, hcast]
    have ha := mul_le_mul_of_nonneg_right hα1 (Nat.cast_nonneg (Fintype.card J) : (0 : ℝ) ≤ _)
    have ha' := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg m : (0 : ℝ) ≤ _)
    nlinarith [Nat.cast_nonneg m (α := ℝ)]
  have h := EditRows.indel_row_separation
    (fun r : Fin (P ^ (Fintype.card J / 2)) => payloadFn i F z r.val)
    (fun r : Fin (P ^ (Fintype.card J / 2)) => payloadFn i F (z + u • lift F i (F i).v) r.val)
    hB htB (by
      intro r r'
      rw [ofFn_payloadFn, ofFn_payloadFn]
      convert payload_separation i F hp hinj P hP hpP hα0 z u hu0 hu r r' r.isLt r'.isLt using 1
      ring)
  change (P ^ (Fintype.card J / 2) : ℕ) * (α * Fintype.card J * m / 6) ≤ _ at h
  apply le_trans _ h
  simp only [Nat.cast_mul, Nat.cast_ofNat, hcast]
  have ha : 0 ≤ α * m * (P ^ (Fintype.card J / 2) : ℕ) := by positivity
  nlinarith

lemma payload_distance_le_sum (z z' : ProductState F) (row : ℕ) :
    (indel (payloadList i F z row) (payloadList i F z' row) : ℝ) ≤
      ∑ r : Slots i, componentDistance F z z' row row (component i r) := by
  have h := cost_tagged_le (enumeration i)
    (fun r => List.ofFn ((F (component i r)).word (z (component i r) + row • (F (component i r)).v)))
    (fun r => List.ofFn ((F (component i r)).word (z' (component i r) + row • (F (component i r)).v))) false
  change indel (payloadList i F z row) (payloadList i F z' row) ≤ _ at h
  rw [enumeration, List.map_ofFn, List.sum_ofFn] at h
  have h' := Nat.cast_le (α := ℝ).mpr h
  rw [Nat.cast_sum] at h'
  change (indel (payloadList i F z row) (payloadList i F z' row) : ℝ) ≤
    ∑ x : Fin (Fintype.card (Slots i)), componentDistance F z z' row row
      (component i ((Fintype.equivFin (Slots i)).symm x)) at h'
  rw [(Fintype.equivFin (Slots i)).symm.sum_comp
    (fun r => componentDistance F z z' row row (component i r))] at h'
  exact h'

omit [Fintype J] in
lemma componentDistance_lift (j : J) (e : (F j).State) (r : ℝ)
    (her : (e,r) ∈ (F j).steps) (z : ProductState F) (row : ℕ) (k : J) :
    componentDistance F z (z + lift F j e) row row k ≤ if k = j then m * r else 0 := by
  by_cases hk : k = j
  · subst k
    have he : (z + lift F j e) j + row • (F j).v = (z j + row • (F j).v) + e := by
      simp [lift, add_right_comm]
    unfold componentDistance
    rw [he, ite_eq_left rfl]
    exact (F j).cheap e r her (z j + row • (F j).v)
  · have he : (z + lift F j e) k + row • (F k).v = z k + row • (F k).v := by
      simp [lift, hk]
    simp only [componentDistance, he, ite_eq_right hk]
    change (cost false _ _ : ℝ) ≤ 0
    simp only [cost_refl, Nat.cast_zero, le_refl]

lemma payload_cheap_lift (j : J) (e : (F j).State) (r : ℝ)
    (her : (e,r) ∈ (F j).steps) (z : ProductState F) (row : ℕ) :
    (indel (payloadList i F z row) (payloadList i F (z + lift F j e) row) : ℝ) ≤
      multiplicity i j * m * r := by
  calc
    _ ≤ ∑ s : Slots i, componentDistance F z (z + lift F j e) row row (component i s) :=
      payload_distance_le_sum i F z (z + lift F j e) row
    _ ≤ ∑ s : Slots i, if component i s = j then (m : ℝ) * r else 0 := by
      apply Finset.sum_le_sum
      intro s _
      exact componentDistance_lift F j e r her z row (component i s)
    _ = _ := by rw [sum_slots_delta]; ring

lemma rawWord_cheap_lift (hm : 0 < m) (L : ℕ)
    (j : J) (e : (F j).State) (r : ℝ) (her : (e,r) ∈ (F j).steps) (z : ProductState F) :
    (indel (rawWord i F L z) (rawWord i F L (z + lift F j e)) : ℝ) ≤
      (2 * ((2 * Fintype.card J - 1) * m) * L : ℕ) * (weight i j * r) := by
  have hb : 1 ≤ Fintype.card J := Fintype.card_pos_iff.mpr ⟨i⟩
  have hB : 0 < (2 * Fintype.card J - 1) * m := Nat.mul_pos (by omega) hm
  have hbR : (1 : ℝ) ≤ Fintype.card J := by exact_mod_cast hb
  have hcast : ((2 * Fintype.card J - 1 : ℕ) : ℝ) = 2 * (Fintype.card J : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  have h := EditRows.indel_rowWord_le hB
    (fun row : Fin L => payloadFn i F z row.val)
    (fun row : Fin L => payloadFn i F (z + lift F j e) row.val)
  have h' := Nat.cast_le (α := ℝ).mpr h
  change (indel (rawWord i F L z) (rawWord i F L (z + lift F j e)) : ℝ) ≤ _ at h'
  rw [Nat.cast_sum] at h'
  simp only [ofFn_payloadFn] at h'
  calc
    _ ≤ ∑ row : Fin L, (indel (payloadList i F z row.val)
        (payloadList i F (z + lift F j e) row.val) : ℝ) := h'
    _ ≤ ∑ _row : Fin L, (multiplicity i j : ℝ) * m * r :=
      Finset.sum_le_sum (fun row _ => payload_cheap_lift i F j e r her z row.val)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        weight, Nat.cast_mul, Nat.cast_ofNat, hcast]
      field_simp [show (2 * (Fintype.card J : ℝ) - 1) ≠ 0 by linarith]

lemma payload_allPhase (z : ProductState F) (row : ℕ) :
    payloadList i F (z + allPhase F) row = payloadList i F z (row+1) := by
  unfold payloadList
  congr 1
  funext s
  congr 2
  simp only [Pi.add_apply, allPhase, add_nsmul, one_nsmul]
  abel

lemma rawWord_cheap_phase (hm : 0 < m) (L : ℕ) (hL : 0 < L) (z : ProductState F) :
    (indel (rawWord i F L z) (rawWord i F L (z + allPhase F)) : ℝ) ≤
      (2 * ((2 * Fintype.card J - 1) * m) * L : ℕ) * (2 / (L : ℝ)) := by
  have hb : 1 ≤ Fintype.card J := Fintype.card_pos_iff.mpr ⟨i⟩
  have hB : 0 < (2 * Fintype.card J - 1) * m := Nat.mul_pos (by omega) hm
  have h := EditRows.indel_row_shift hL hB
    (fun row : Fin L => payloadFn i F z row.val)
    (fun row : Fin L => payloadFn i F (z + allPhase F) row.val) (by
      intro a b hab
      apply List.ofFn_injective
      rw [ofFn_payloadFn, ofFn_payloadFn, payload_allPhase, hab])
  have h' := Nat.cast_le (α := ℝ).mpr h
  change (indel (rawWord i F L z) (rawWord i F L (z + allPhase F)) : ℝ) ≤ _ at h'
  convert h' using 1
  push_cast
  field_simp
  ring

noncomputable def symbolCode : Option (Slots i × Fin A) ≃
    Fin (1 + (2 * Fintype.card J - 1) * A) :=
  (Fintype.equivFin _).trans (finCongr (by
    rw [Fintype.card_option, Fintype.card_prod, slots_card, Fintype.card_fin]
    omega))

noncomputable def nextWord (L : ℕ) (z : ProductState F) :
    Fin (2 * ((2 * Fintype.card J - 1) * m) * L) →
      Fin (1 + (2 * Fintype.card J - 1) * A) :=
  fixedFn ((rawWord i F L z).map (symbolCode (A := A) i)) (by simp)

@[simp] lemma ofFn_nextWord (L : ℕ) (z : ProductState F) :
    List.ofFn (nextWord i F L z) = (rawWord i F L z).map (symbolCode (A := A) i) :=
  ofFn_fixedFn _ _

lemma nextWord_distance (L : ℕ) (z z' : ProductState F) :
    indel (List.ofFn (nextWord i F L z)) (List.ofFn (nextWord i F L z')) =
      indel (rawWord i F L z) (rawWord i F L z') := by
  rw [ofFn_nextWord, ofFn_nextWord]
  exact cost_map_eq_of_leftInverse (s := false) (symbolCode (A := A) i)
    (symbolCode (A := A) i).symm (symbolCode (A := A) i).left_inv _ _

noncomputable def nextSteps (L : ℕ) : List (ProductState F × ℝ) :=
  (allPhase F, 2 / (L : ℝ)) :: (Finset.univ.toList.flatMap (fun j =>
    (F j).steps.map (fun er => (lift F j er.1, weight i j * er.2))))

lemma mem_nextSteps (L : ℕ) (e : ProductState F) (r : ℝ) :
    (e,r) ∈ nextSteps i F L ↔
      (e = allPhase F ∧ r = 2 / (L : ℝ)) ∨
      ∃ (j : J) (e' : (F j).State) (r' : ℝ), (e',r') ∈ (F j).steps ∧
        e = lift F j e' ∧ r = weight i j * r' := by
  simp only [nextSteps, List.mem_cons, Prod.mk.injEq, List.mem_flatMap,
    Finset.mem_toList, Finset.mem_univ, true_and, List.mem_map]
  constructor
  · rintro (h | ⟨j, ⟨e',r'⟩, hmem, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j,e',r',hmem,h.1.symm,h.2.symm⟩
  · rintro (h | ⟨j,e',r',hmem,he,hr⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j,(e',r'),hmem,he.symm,hr.symm⟩

noncomputable def successor
    (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    (P : ℕ) (hP : 1 ≤ P) (hpLow : ∀ j, P ≤ p j) (hpHigh : ∀ j, p j ≤ 2 * P)
    (hm : 0 < m) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hQ : 0 ≤ Q)
    (h : ℕ) (hh : 0 < h) :
    Family (p i) (2 * ((2 * Fintype.card J - 1) * m) * P ^ (Fintype.card J / 2))
      (1 + (2 * Fintype.card J - 1) * A) (α / 24)
      (2 * (2 * (P : ℝ)) ^ (2 * h) / (P ^ (Fintype.card J / 2) : ℕ) + Q / h) := by
  classical
  let L := P ^ (Fintype.card J / 2)
  have hL : 0 < L := pow_pos (by omega) _
  refine { State := ProductState F
           group := inferInstance
           finite := inferInstance
           v := lift F i (F i).v
           annihilate := ?_
           word := nextWord i F L
           steps := nextSteps i F L
           positive := ?_
           cheap := ?_
           far := ?_
           control := ?_ }
  · rw [← lift_nsmul, (F i).annihilate]
    simp [lift]
  · intro e r her
    rcases (mem_nextSteps i F L e r).mp her with ⟨rfl,rfl⟩ | ⟨j,e',r',hmem,rfl,rfl⟩
    · exact div_pos (by norm_num) (by exact_mod_cast hL)
    · exact mul_pos (weight_pos i j) ((F j).positive e' r' hmem)
  · intro e r her z
    rw [nextWord_distance]
    rcases (mem_nextSteps i F L e r).mp her with ⟨rfl,rfl⟩ | ⟨j,e',r',hmem,rfl,rfl⟩
    · exact rawWord_cheap_phase i F hm L hL z
    · exact rawWord_cheap_lift i F hm L j e' r' hmem z
  · intro z u hu0 hu
    rw [nextWord_distance]
    exact rawWord_far i F hp hinj P hP hpLow hm hα0 hα1 z u hu0 hu
  · intro H hb u _hu0 hu
    apply successor_control i F hp hinj P (by exact_mod_cast (show 1 ≤ 2 * P by omega))
      (fun j => by exact_mod_cast hpHigh j) h hh L hQ H
    · exact hb _ _ ((mem_nextSteps i F L _ _).mpr (Or.inl ⟨rfl,rfl⟩))
    · intro j e r hmem
      exact hb _ _ ((mem_nextSteps i F L _ _).mpr (Or.inr ⟨j,e,r,hmem,rfl,rfl⟩))
    · exact hu

end Words
end EditFamily

end OAI
