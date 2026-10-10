import OAI.Computability.StarHeight.Actions

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uΩ uι

namespace FiniteAvoidance

variable {Ω : Type uΩ} {ι : Type uι} [Fintype Ω]

noncomputable def mass (w : Ω → ℝ) (A : Set Ω) : ℝ := by
  classical
  exact ∑ x : Ω, if x ∈ A then w x else 0

lemma mass_nonneg {w : Ω → ℝ} (hw : ∀ x, 0 ≤ w x) (A : Set Ω) :
    0 ≤ mass w A := by
  classical
  exact Finset.sum_nonneg fun x _ => by
    by_cases hx : x ∈ A <;> simp [hx, hw x]

lemma mass_mono {w : Ω → ℝ} (hw : ∀ x, 0 ≤ w x) {A C : Set Ω}
    (hAC : A ⊆ C) : mass w A ≤ mass w C := by
  classical
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : x ∈ A
  · simp [hx, hAC hx]
  · by_cases hc : x ∈ C <;> simp [hx, hc, hw x]

@[simp] lemma mass_empty (w : Ω → ℝ) : mass w ∅ = 0 := by
  classical
  simp [mass]

lemma mass_diff (w : Ω → ℝ) (A C : Set Ω) :
    mass w (A \ C) = mass w A - mass w (C ∩ A) := by
  classical
  simp only [mass, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ A <;> by_cases hc : x ∈ C <;> simp [hx, hc]

def avoids (B : ι → Set Ω) (J : Finset ι) : Set Ω :=
  {x | ∀ i ∈ J, x ∉ B i}

omit [Fintype Ω] in
@[simp] lemma avoids_empty (B : ι → Set Ω) : avoids B ∅ = Set.univ := by
  ext x
  simp [avoids]

omit [Fintype Ω] in
lemma avoids_antitone (B : ι → Set Ω) {J K : Finset ι} (hJK : J ⊆ K) :
    avoids B K ⊆ avoids B J := by
  intro x hx i hi
  exact hx i (hJK hi)

omit [Fintype Ω] in
lemma avoids_insert [DecidableEq ι] (B : ι → Set Ω) (J : Finset ι) (i : ι) :
    avoids B (insert i J) = avoids B J \ B i := by
  ext x
  simp only [avoids, Set.mem_ofPred_eq, Finset.mem_insert, forall_eq_or_imp,
    Set.mem_sdiff]
  exact and_comm

lemma mass_avoids_insert [DecidableEq ι] (w : Ω → ℝ) (B : ι → Set Ω)
    (J : Finset ι) (i : ι) :
    mass w (avoids B (insert i J)) =
      mass w (avoids B J) - mass w (B i ∩ avoids B J) := by
  rw [avoids_insert, mass_diff]

lemma avoid_union_lower [DecidableEq ι] (w : Ω → ℝ) (B : ι → Set Ω)
    (s : ℝ) (hs : s ≤ 1) (J K : Finset ι) (hd : Disjoint J K)
    (hb : ∀ U : Finset ι, U ⊆ K → U.card < K.card →
      ∀ i, i ∉ J ∪ U → mass w (B i ∩ avoids B (J ∪ U)) ≤
        s * mass w (avoids B (J ∪ U))) :
    (1 - s) ^ K.card * mass w (avoids B J) ≤ mass w (avoids B (J ∪ K)) := by
  induction K using Finset.induction_on with
  | empty => simp
  | @insert i K hi ih =>
      have hdK : Disjoint J K := hd.mono_right (Finset.subset_insert _ _)
      have hiJ : i ∉ J := by
        intro hm
        exact Finset.disjoint_left.mp hd hm (Finset.mem_insert_self _ _)
      have hbK : ∀ U : Finset ι, U ⊆ K → U.card < K.card →
          ∀ j, j ∉ J ∪ U → mass w (B j ∩ avoids B (J ∪ U)) ≤
            s * mass w (avoids B (J ∪ U)) := by
        intro U hU hcard j hj
        apply hb U (hU.trans (Finset.subset_insert _ _))
        · simpa [Finset.card_insert_of_notMem hi] using hcard.trans_le (Nat.le_succ _)
        · exact hj
      have hstep := hb K (Finset.subset_insert _ _) (by simp [hi]) i
        (by simp [hiJ, hi])
      have hrec := ih hdK hbK
      rw [Finset.card_insert_of_notMem hi, pow_succ,
        mul_comm ((1 - s) ^ K.card) (1 - s), mul_assoc]
      calc
        (1 - s) * ((1 - s) ^ K.card * mass w (avoids B J))
            ≤ (1 - s) * mass w (avoids B (J ∪ K)) :=
              mul_le_mul_of_nonneg_left hrec (sub_nonneg.mpr hs)
        _ ≤ mass w (avoids B (J ∪ insert i K)) := by
          rw [Finset.union_insert, mass_avoids_insert]
          linarith

theorem local_lemma [DecidableEq ι] (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (htotal : 0 < mass w Set.univ) (B : ι → Set Ω)
    (neighbors : ι → Finset ι) (D : ℕ) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hdegree : ∀ i, (neighbors i).card ≤ D)
    (hbad : ∀ i, mass w (B i) ≤ s * (1 - s) ^ D * mass w Set.univ)
    (hind : ∀ i (J : Finset ι), i ∉ J → Disjoint J (neighbors i) →
      mass w (B i ∩ avoids B J) * mass w Set.univ =
        mass w (B i) * mass w (avoids B J))
    (J : Finset ι) : 0 < mass w (avoids B J) := by
  have hconditional : ∀ n : ℕ, ∀ K : Finset ι, K.card = n →
      0 < mass w (avoids B K) ∧ ∀ i, i ∉ K →
        mass w (B i ∩ avoids B K) ≤ s * mass w (avoids B K) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro K hK
      have hpos : 0 < mass w (avoids B K) := by
        by_cases he : K = ∅
        · simpa [he] using htotal
        · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr he
          have hsmall : (K.erase i).card < n := by
            rw [← hK]
            exact Finset.card_erase_lt_of_mem hi
          have hprev := ih (K.erase i).card hsmall (K.erase i) rfl
          have hb := hprev.2 i (Finset.notMem_erase i K)
          have hins : insert i (K.erase i) = K := Finset.insert_erase hi
          rw [← hins, mass_avoids_insert]
          have hp : 0 < (1 - s) * mass w (avoids B (K.erase i)) :=
            mul_pos (sub_pos.mpr hs1) hprev.1
          linarith
      refine ⟨hpos, ?_⟩
      intro i hi
      let N := K ∩ neighbors i
      let F := K \ neighbors i
      have hFN : Disjoint F N := by
        exact Finset.disjoint_sdiff_inter _ _
      have hUF : F ∪ N = K := by
        exact Finset.sdiff_union_inter _ _
      have hFsub : F ⊆ K := Finset.sdiff_subset
      have hFdisj : Disjoint F (neighbors i) := by
        apply Finset.disjoint_left.mpr
        intro x hx hnx
        exact (Finset.mem_sdiff.mp hx).2 hnx
      have hiF : i ∉ F := fun h => hi (hFsub h)
      have hInd := hind i F hiF hFdisj
      have hBF : mass w (B i ∩ avoids B F) ≤
          s * (1 - s) ^ D * mass w (avoids B F) := by
        apply (mul_le_mul_iff_left₀ htotal).mp
        rw [hInd]
        calc
          mass w (B i) * mass w (avoids B F)
              ≤ (s * (1 - s) ^ D * mass w Set.univ) * mass w (avoids B F) :=
                mul_le_mul_of_nonneg_right (hbad i) (mass_nonneg hw _)
          _ = (s * (1 - s) ^ D * mass w (avoids B F)) * mass w Set.univ := by ring
      have hchain : (1 - s) ^ N.card * mass w (avoids B F) ≤
          mass w (avoids B K) := by
        rw [← hUF]
        apply avoid_union_lower w B s hs1.le F N hFN
        intro U hU hcard j hj
        have hdu : Disjoint F U := hFN.mono_right hU
        have hsmall : (F ∪ U).card < n := by
          rw [Finset.card_union_of_disjoint hdu, ← hK, ← hUF,
            Finset.card_union_of_disjoint hFN]
          exact Nat.add_lt_add_left hcard _
        exact (ih (F ∪ U).card hsmall (F ∪ U) rfl).2 j hj
      have hNcard : N.card ≤ D :=
        (Finset.card_le_card (Finset.inter_subset_right)).trans (hdegree i)
      have hpow : (1 - s) ^ D ≤ (1 - s) ^ N.card :=
        pow_le_pow_of_le_one (sub_nonneg.mpr hs1.le)
          (by linarith) hNcard
      calc
        mass w (B i ∩ avoids B K) ≤ mass w (B i ∩ avoids B F) :=
          mass_mono hw (Set.inter_subset_inter_right _ (avoids_antitone B hFsub))
        _ ≤ s * (1 - s) ^ D * mass w (avoids B F) := hBF
        _ ≤ s * ((1 - s) ^ N.card * mass w (avoids B F)) := by
          have hh := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow hs0.le) (mass_nonneg hw (avoids B F))
          simpa only [mul_assoc] using hh
        _ ≤ s * mass w (avoids B K) := mul_le_mul_of_nonneg_left hchain hs0.le
  exact (hconditional J.card J rfl).1

lemma mass_one_eq_card (A : Set Ω) :
    mass (fun _ : Ω => (1 : ℝ)) A = Nat.card A := by
  classical
  simp [mass, Nat.card_eq_fintype_card, Fintype.card_subtype]

@[simp] lemma mass_one_univ :
    mass (fun _ : Ω => (1 : ℝ)) Set.univ = Fintype.card Ω := by
  classical
  simp [mass]

noncomputable def probability (E : Set Ω) : ℝ :=
  mass (fun _ => (1 : ℝ)) E / Fintype.card Ω

@[simp] lemma probability_univ [Nonempty Ω] :
    probability (Set.univ : Set Ω) = 1 := by
  simp [probability, ne_of_gt Fintype.card_pos]

lemma probability_compl [Nonempty Ω] (E : Set Ω) :
    probability Eᶜ = 1 - probability E := by
  have hd := mass_diff (fun _ : Ω => (1 : ℝ)) Set.univ E
  simp only [← Set.compl_eq_univ_sdiff, Set.inter_univ, mass_one_univ] at hd
  unfold probability
  rw [hd, sub_div, div_self (by exact_mod_cast ne_of_gt Fintype.card_pos)]

lemma probability_eq_of_equiv (E F : Set Ω) (e : E ≃ F) :
    probability E = probability F := by
  unfold probability
  rw [mass_one_eq_card, mass_one_eq_card, Nat.card_congr e]

lemma probability_inter_of_independent [Nonempty Ω] (E F : Set Ω)
    (hind : mass (fun _ : Ω => (1 : ℝ)) (E ∩ F) *
        mass (fun _ : Ω => (1 : ℝ)) Set.univ =
      mass (fun _ : Ω => (1 : ℝ)) E * mass (fun _ : Ω => (1 : ℝ)) F) :
    probability (E ∩ F) = probability E * probability F := by
  have hp : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt Fintype.card_pos
  simp only [mass_one_univ] at hind
  unfold probability
  field_simp
  exact hind

lemma nonempty_of_mass_pos {w : Ω → ℝ} {E : Set Ω} (h : 0 < mass w E) :
    E.Nonempty := by
  by_contra hn
  have he := Set.not_nonempty_iff_eq_empty.mp hn
  simp [he] at h

lemma local_parameter (D : ℕ) (p : ℝ)
    (hp : 4 * ((D : ℝ) + 1) * p ≤ 1) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ p ≤ s * (1 - s) ^ D := by
  let s : ℝ := (2 * ((D : ℝ) + 1))⁻¹
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hden : 0 < 2 * ((D : ℝ) + 1) := by positivity
  have hs0 : 0 < s := inv_pos.mpr hden
  have heq : s * (2 * ((D : ℝ) + 1)) = 1 := inv_mul_cancel₀ hden.ne'
  have hsD : 0 ≤ s * D := mul_nonneg hs0.le hD
  have hshalf : s ≤ 1 / 2 := by nlinarith
  have hs1 : s < 1 := by linarith
  have hbern : 1 - (D : ℝ) * s ≤ (1 - s) ^ D := by
    simpa only [sub_eq_add_neg, mul_neg] using
      (one_add_mul_le_pow (a := -s) (by linarith) D)
  have hhalf : (1 : ℝ) / 2 ≤ (1 - s) ^ D := by nlinarith
  have hp' : p ≤ s / 2 := by
    apply (mul_le_mul_iff_right₀ (show 0 < 4 * ((D : ℝ) + 1) by positivity)).mp
    nlinarith [heq]
  refine ⟨s, hs0, hs1, hp'.trans ?_⟩
  nlinarith

end FiniteAvoidance

end GeneralizedStarHeight

end OAI
