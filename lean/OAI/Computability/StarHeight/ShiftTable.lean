import OAI.Computability.StarHeight.Avoidance

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uC uS uι uι2 uι3 uι4 uA uI
universe uS2 uS3 uS4 uS5 uI2 uA2 uA3 uK
universe uS6

namespace FiniteProduct

variable {C : Type uC} {S : Type uS}

def DependsOn (E : Set (C → S)) (s : Set C) : Prop :=
  ∀ β γ, Set.EqOn β γ s → (β ∈ E ↔ γ ∈ E)

lemma DependsOn.mono {E : Set (C → S)} {s t : Set C}
    (h : DependsOn E s) (hst : s ⊆ t) : DependsOn E t := by
  intro β γ he
  exact h β γ (he.mono hst)

noncomputable def splice (s : Set C) (β γ : C → S) : C → S := by
  classical
  exact fun c => if c ∈ s then β c else γ c

lemma splice_eqOn_left (s : Set C) (β γ : C → S) :
    Set.EqOn (splice s β γ) β s := by
  classical
  intro c hc
  simp [splice, hc]

lemma splice_eqOn_right (s : Set C) (β γ : C → S) :
    Set.EqOn (splice s β γ) γ sᶜ := by
  classical
  intro c hc
  simp only [Set.mem_compl_iff] at hc
  simp [splice, hc]

lemma splice_splice (s : Set C) (β γ : C → S) :
    splice s (splice s β γ) (splice s γ β) = β := by
  classical
  funext c
  by_cases hc : c ∈ s <;> simp [splice, hc]

noncomputable def cylinderEquiv (E F : Set (C → S)) (s : Set C)
    (hE : DependsOn E s) (hF : DependsOn F sᶜ) :
    ↥(E ∩ F) × (C → S) ≃ E × F where
  toFun p :=
    (⟨splice s p.1.1 p.2,
      (hE _ _ (splice_eqOn_left _ _ _)).mpr p.1.2.1⟩,
     ⟨splice s p.2 p.1.1,
      (hF _ _ (splice_eqOn_right _ _ _)).mpr p.1.2.2⟩)
  invFun p :=
    (⟨splice s p.1.1 p.2.1,
      ⟨(hE _ _ (splice_eqOn_left _ _ _)).mpr p.1.2,
       (hF _ _ (splice_eqOn_right _ _ _)).mpr p.2.2⟩⟩,
     splice s p.2.1 p.1.1)
  left_inv p := by
    apply Prod.ext
    · exact Subtype.ext (splice_splice _ _ _)
    · exact splice_splice _ _ _
  right_inv p := by
    apply Prod.ext <;> exact Subtype.ext (splice_splice _ _ _)

lemma independent_of_disjoint_support [Fintype C] [Fintype S] [DecidableEq C]
    (E F : Set (C → S)) (s t : Set C)
    (hE : DependsOn E s) (hF : DependsOn F t) (hst : Disjoint s t) :
    FiniteAvoidance.mass (fun _ => (1 : ℝ)) (E ∩ F) *
        FiniteAvoidance.mass (fun _ : C → S => (1 : ℝ)) Set.univ =
      FiniteAvoidance.mass (fun _ => (1 : ℝ)) E *
        FiniteAvoidance.mass (fun _ => (1 : ℝ)) F := by
  classical
  have htc : t ⊆ sᶜ := by
    intro c hc hs
    exact Set.disjoint_left.mp hst hs hc
  have hcard := Fintype.card_congr (cylinderEquiv E F s hE (hF.mono htc))
  simp only [Fintype.card_prod] at hcard
  simpa only [FiniteAvoidance.mass_one_eq_card, Nat.card_eq_fintype_card,
    Fintype.card_setUniv, Nat.cast_mul] using congrArg (fun n : ℕ => (n : ℝ)) hcard

lemma DependsOn.compl {E : Set (C → S)} {s : Set C}
    (h : DependsOn E s) : DependsOn Eᶜ s := by
  intro β γ he
  exact not_congr (h β γ he)

lemma DependsOn.inter {E F : Set (C → S)} {s t : Set C}
    (hE : DependsOn E s) (hF : DependsOn F t) : DependsOn (E ∩ F) (s ∪ t) := by
  intro β γ he
  exact and_congr (hE β γ (he.mono Set.subset_union_left))
    (hF β γ (he.mono Set.subset_union_right))

lemma probability_inter [Fintype C] [Fintype S] [DecidableEq C] [Nonempty S]
    (E F : Set (C → S)) (s t : Set C)
    (hE : DependsOn E s) (hF : DependsOn F t) (hst : Disjoint s t) :
    FiniteAvoidance.probability (E ∩ F) =
      FiniteAvoidance.probability E * FiniteAvoidance.probability F :=
  FiniteAvoidance.probability_inter_of_independent _ _
    (independent_of_disjoint_support E F s t hE hF hst)

noncomputable def agreementEquiv (s : Set C) (d : C → S) :
    {β : C → S // Set.EqOn β d s} ≃ (↥(sᶜ) → S) := by
  classical
  exact {
  toFun β c := β.1 c
  invFun γ := ⟨fun c => if h : c ∈ s then d c else γ ⟨c, h⟩, by
    intro c hc
    simp [hc]⟩
  left_inv β := by
    apply Subtype.ext
    funext c
    dsimp
    split_ifs with hc
    · exact (β.2 hc).symm
    · rfl
  right_inv γ := by
    funext c
    have hc : (c : C) ∉ s := c.2
    simp [hc]
  }

lemma probability_agreement [Fintype C] [Fintype S] [DecidableEq C] [Nonempty S]
    (s : Set C) (d : C → S) :
    FiniteAvoidance.probability {β : C → S | Set.EqOn β d s} =
      ((Fintype.card S : ℝ) ^ Nat.card s)⁻¹ := by
  classical
  have hsplit := Fintype.card_congr (Equiv.piEquivPiSubtypeProd (· ∈ s) (fun _ => S))
  simp only [Fintype.card_prod, Fintype.card_fun] at hsplit
  have hc := Nat.card_congr (agreementEquiv s d)
  unfold FiniteAvoidance.probability
  rw [FiniteAvoidance.mass_one_eq_card]
  change (Nat.card {β : C → S // Set.EqOn β d s} : ℝ) /
    Fintype.card (C → S) = _
  rw [hc]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Nat.cast_pow]
  have hsplit' := congrArg (fun n : ℕ => (n : ℝ)) hsplit
  simp only [Nat.cast_mul, Nat.cast_pow] at hsplit'
  rw [hsplit']
  have hq : (Fintype.card S : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt Fintype.card_pos
  field_simp
  congr 1

lemma agreement_dependsOn (s : Set C) (d : C → S) :
    DependsOn {β : C → S | Set.EqOn β d s} s := by
  intro β γ he
  exact ⟨fun hb c hc => (he hc).symm.trans (hb hc),
    fun hg c hc => (he hc).trans (hg hc)⟩

def allEvents {ι : Type uι} (E : ι → Set (C → S)) (J : Finset ι) : Set (C → S) :=
  {β | ∀ i ∈ J, β ∈ E i}

def supportUnion {ι : Type uι2} (s : ι → Set C) (J : Finset ι) : Set C :=
  {c | ∃ i ∈ J, c ∈ s i}

lemma allEvents_dependsOn {ι : Type uι3} (E : ι → Set (C → S))
    (s : ι → Set C) (hE : ∀ i, DependsOn (E i) (s i)) (J : Finset ι) :
    DependsOn (allEvents E J) (supportUnion s J) := by
  intro β γ he
  have hi (i) (hi : i ∈ J) : β ∈ E i ↔ γ ∈ E i := by
    have hs : s i ⊆ supportUnion s J := fun _ hc => ⟨i, hi, hc⟩
    exact hE i β γ (he.mono hs)
  exact ⟨fun hb i hm => (hi i hm).mp (hb i hm),
    fun hg i hm => (hi i hm).mpr (hg i hm)⟩

lemma probability_allEvents {ι : Type uι4} [Fintype C] [Fintype S]
    [DecidableEq C] [Nonempty S]
    (E : ι → Set (C → S)) (s : ι → Set C)
    (hE : ∀ i, DependsOn (E i) (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (J : Finset ι) :
    FiniteAvoidance.probability (allEvents E J) =
      ∏ i ∈ J, FiniteAvoidance.probability (E i) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [allEvents]
  | @insert i J hi ih =>
      have heq : allEvents E (insert i J) = E i ∩ allEvents E J := by
        ext β
        simp [allEvents]
      have hdisj : Disjoint (s i) (supportUnion s J) := by
        apply Set.disjoint_left.mpr
        rintro c hc ⟨j, hj, hcj⟩
        have hij : i ≠ j := fun he => hi (he ▸ hj)
        exact Set.disjoint_left.mp (hd hij) hc hcj
      rw [heq, probability_inter _ _ _ _ (hE i)
        (allEvents_dependsOn E s hE J) hdisj, ih, Finset.prod_insert hi]

section Centering

variable [AddCommGroup S] [DecidableEq C]

def centeredEquiv (a : C) : (C → S) ≃ (C → S) where
  toFun β c := if c = a then β c else β c - β a
  invFun γ c := if c = a then γ c else γ c + γ a
  left_inv β := by
    funext c
    by_cases hc : c = a <;> simp [hc]
  right_inv γ := by
    funext c
    by_cases hc : c = a <;> simp [hc]

def translationEquiv (g : C → S) : (C → S) ≃ (C → S) where
  toFun β c := g c + β c
  invFun γ c := γ c - g c
  left_inv β := by
    funext c
    simp
  right_inv γ := by
    funext c
    simp

end Centering

end FiniteProduct

namespace ShiftCombinatorics

variable {A : Type uA} {I : Type uI} [DecidableEq I]

def offLine (a : I → A) (i : I) : Set (I → A) :=
  Set.range (fun b : {b : A // b ≠ a i} => Function.update a i b.1)

lemma update_ne_center (a : I → A) (i : I) {b : A} (hb : b ≠ a i) :
    Function.update a i b ≠ a := by
  intro he
  exact hb (by simpa using congrFun he i)

lemma offLine_pairwise (a : I → A) :
    Pairwise (fun i j : I => Disjoint (offLine a i) (offLine a j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro c ⟨b, rfl⟩ ⟨d, hd⟩
  have he := congrFun hd i
  simp only [Function.update_self, Function.update_of_ne hij] at he
  exact b.2 he.symm

lemma card_offLine [Fintype A] (a : I → A) (i : I) :
    Nat.card (offLine a i) = Fintype.card A - 1 := by
  classical
  have hinj : Function.Injective
      (fun b : {b : A // b ≠ a i} => Function.update a i b.1) := by
    intro b d he
    apply Subtype.ext
    simpa using congrFun he i
  unfold offLine
  rw [Nat.card_congr (Equiv.ofInjective _ hinj).symm,
    Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]

lemma centered_line_iff {S : Type uS2} [AddCommGroup S] [DecidableEq (I → A)]
    (a : I → A) (γ : (I → A) → S) (i : I) :
    Set.EqOn (FiniteProduct.centeredEquiv a γ) (fun _ => 0) (offLine a i) ↔
      ∀ b : A, γ (Function.update a i b) = γ a := by
  classical
  constructor
  · intro h b
    by_cases hb : b = a i
    · simp [hb]
    · have hc := h (show Function.update a i b ∈ offLine a i from
        ⟨⟨b, hb⟩, rfl⟩)
      simpa [FiniteProduct.centeredEquiv, update_ne_center a i hb, sub_eq_zero] using hc
  · intro h c hc
    obtain ⟨b, rfl⟩ := hc
    simpa [FiniteProduct.centeredEquiv, update_ne_center a i b.2, sub_eq_zero] using h b

def starSupport (a : I → A) : Set (I → A) :=
  {c | c = a ∨ ∃ i b, c = Function.update a i b}

def badEvent {S : Type uS3} [AddCommGroup S] (g : (I → A) → S) (a : I → A) :
    Set ((I → A) → S) :=
  {β | ¬∃ i : I, ∀ b : A,
    g (Function.update a i b) + β (Function.update a i b) = g a + β a}

lemma badEvent_dependsOn {S : Type uS4} [AddCommGroup S]
    (g : (I → A) → S) (a : I → A) :
    FiniteProduct.DependsOn (badEvent g a) (starSupport a) := by
  intro β γ he
  apply not_congr
  apply exists_congr
  intro i
  apply forall_congr'
  intro b
  rw [he (show Function.update a i b ∈ starSupport a from Or.inr ⟨i, b, rfl⟩),
    he (show a ∈ starSupport a from Or.inl rfl)]

lemma probability_badEvent {S : Type uS5} [AddCommGroup S]
    [Fintype I] [Fintype A] [DecidableEq A] [Fintype S]
    (g : (I → A) → S) (a : I → A) :
    FiniteAvoidance.probability (badEvent g a) =
      (1 - ((Fintype.card S : ℝ) ^ (Fintype.card A - 1))⁻¹) ^ Fintype.card I := by
  classical
  let E (i : I) : Set ((I → A) → S) :=
    {γ | Set.EqOn γ (fun _ => 0) (offLine a i)}ᶜ
  let e := (FiniteProduct.translationEquiv g).trans (FiniteProduct.centeredEquiv a)
  have he (β : (I → A) → S) :
      β ∈ badEvent g a ↔ e β ∈ FiniteProduct.allEvents E Finset.univ := by
    change (¬∃ i, ∀ b, g (Function.update a i b) + β (Function.update a i b) =
      g a + β a) ↔ ∀ i ∈ Finset.univ, ¬Set.EqOn (e β) (fun _ => 0) (offLine a i)
    simp only [not_exists, Finset.mem_univ, forall_const]
    apply forall_congr'
    intro i
    exact not_congr (centered_line_iff a (FiniteProduct.translationEquiv g β) i).symm
  rw [FiniteAvoidance.probability_eq_of_equiv _ _ (e.subtypeEquiv he)]
  rw [FiniteProduct.probability_allEvents E (offLine a)
    (fun i => (FiniteProduct.agreement_dependsOn _ _).compl) (offLine_pairwise a)]
  have hE (i : I) : FiniteAvoidance.probability (E i) =
      1 - ((Fintype.card S : ℝ) ^ (Fintype.card A - 1))⁻¹ := by
    rw [FiniteAvoidance.probability_compl, FiniteProduct.probability_agreement,
      card_offLine]
  simp only [hE, Finset.prod_const, Finset.card_univ]

abbrev CenterCode (I : Type uI2) (A : Type uA2) := Unit ⊕ ((I × A) ⊕ ((I × A) × (I × A)))

def centerOfCode (a : I → A) : CenterCode I A → (I → A)
  | .inl _ => a
  | .inr (.inl (i, b)) => Function.update a i b
  | .inr (.inr ((i, b), (j, d))) => Function.update (Function.update a i b) j d

noncomputable def nearCenters [Fintype I] [Fintype A] (a : I → A) : Finset (I → A) := by
  classical
  exact Finset.univ.image (centerOfCode a)

lemma mem_nearCenters [Fintype I] [Fintype A] (a : I → A) (k : CenterCode I A) :
    centerOfCode a k ∈ nearCenters a := by
  classical
  exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩

lemma card_nearCenters [Fintype I] [Fintype A] (a : I → A) :
    (nearCenters a).card ≤ 1 + Fintype.card I * Fintype.card A +
      (Fintype.card I) ^ 2 * (Fintype.card A) ^ 2 := by
  classical
  calc
    (nearCenters a).card ≤ Fintype.card (CenterCode I A) :=
      (Finset.card_image_le).trans_eq (Finset.card_univ)
    _ = _ := by
      simp only [CenterCode, Fintype.card_sum, Fintype.card_prod, Fintype.card_unit]
      ring

lemma restore_center (d c : I → A) (j : I) (b : A)
    (h : c = Function.update d j b) : d = Function.update c j (d j) := by
  rw [h]
  simp

lemma mem_nearCenters_of_shared [Fintype I] [Fintype A]
    {a d c : I → A} (ha : c ∈ starSupport a) (hd : c ∈ starSupport d) :
    d ∈ nearCenters a := by
  rcases ha with ha | ⟨i, b, ha⟩
  · rcases hd with hd | ⟨j, b, hj⟩
    · have he : d = a := hd.symm.trans ha
      rw [he]
      exact mem_nearCenters a (.inl ())
    · have he := restore_center d a j b (ha.symm.trans hj)
      rw [he]
      exact mem_nearCenters a (.inr (.inl (j, d j)))
  · rcases hd with hd | ⟨j, e, hj⟩
    · have he : d = Function.update a i b := hd.symm.trans ha
      rw [he]
      exact mem_nearCenters a (.inr (.inl (i, b)))
    · have he := restore_center d (Function.update a i b) j e (ha.symm.trans hj)
      rw [he]
      exact mem_nearCenters a (.inr (.inr ((i, b), (j, d j))))

end ShiftCombinatorics

section ShiftTable

variable {A : Type uA3} {K : Type uK} {S : Type uS6} [Field K] [AddCommGroup S] [Module K S]

def ShiftTableProperty (l : ℕ) (f : (Fin l → A) → (S →ₗ[K] S))
    (β : (Fin l → A) → S) : Prop :=
  ∀ (a : Fin l → A) (x : S), ∃ i : Fin l, ∀ b : A,
    f (Function.update a i b) x + β (Function.update a i b) = f a x + β a

theorem exists_shift_table_length (a q r : ℝ) (hr : 0 ≤ r) (hr' : r < 1) :
    ∃ l : ℕ, 1 ≤ l ∧
      4 * (q * (1 + l * a + (l : ℝ) ^ 2 * a ^ 2) + 1) * r ^ l ≤ 1 := by
  have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one hr hr'
  have h1 := tendsto_pow_const_mul_const_pow_of_lt_one 1 hr hr'
  have h2 := tendsto_pow_const_mul_const_pow_of_lt_one 2 hr hr'
  have ht : Filter.Tendsto
      (fun l : ℕ => 4 * (q * (1 + l * a + (l : ℝ) ^ 2 * a ^ 2) + 1) * r ^ l)
      Filter.atTop (nhds 0) := by
    have ht' := ((h0.const_mul (4 * q + 4)).add
      (h1.const_mul (4 * q * a))).add (h2.const_mul (4 * q * a ^ 2))
    convert ht' using 1
    · ext l
      simp only [pow_one]
      ring
    · simp only [mul_zero, add_zero]
  have he : ∀ᶠ l : ℕ in Filter.atTop,
      1 ≤ l ∧ 4 * (q * (1 + l * a + (l : ℝ) ^ 2 * a ^ 2) + 1) * r ^ l < 1 :=
    (Filter.eventually_ge_atTop 1).and (ht.eventually (gt_mem_nhds zero_lt_one))
  obtain ⟨l, hl, hb⟩ := he.exists
  exact ⟨l, hl, hb.le⟩

theorem shift_table_at_length [Fintype A] [Fintype S] [DecidableEq A]
    (l : ℕ)
    (hnum : 4 * ((Fintype.card S : ℝ) *
      (1 + l * (Fintype.card A : ℝ) + (l : ℝ) ^ 2 * (Fintype.card A : ℝ) ^ 2) + 1) *
      (1 - ((Fintype.card S : ℝ) ^ (Fintype.card A - 1))⁻¹) ^ l ≤ 1)
    (f : (Fin l → A) → (S →ₗ[K] S)) :
    ∃ β : (Fin l → A) → S, ShiftTableProperty l f β := by
  classical
  let C := Fin l → A
  let Ω := C → S
  let B (j : S × C) : Set Ω := ShiftCombinatorics.badEvent (fun c => f c j.1) j.2
  let N (j : S × C) : Finset (S × C) :=
    Finset.univ ×ˢ ShiftCombinatorics.nearCenters j.2
  let D := Fintype.card S * (1 + l * Fintype.card A + l ^ 2 * (Fintype.card A) ^ 2)
  let p : ℝ := (1 - ((Fintype.card S : ℝ) ^ (Fintype.card A - 1))⁻¹) ^ l
  have hp : 4 * ((D : ℝ) + 1) * p ≤ 1 := by
    simpa only [D, p, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow] using hnum
  obtain ⟨s, hs0, hs1, hps⟩ := FiniteAvoidance.local_parameter D p hp
  have htotal : 0 < FiniteAvoidance.mass (fun _ : Ω => (1 : ℝ)) Set.univ := by
    rw [FiniteAvoidance.mass_one_univ]
    exact_mod_cast Fintype.card_pos
  have hdegree (j : S × C) : (N j).card ≤ D := by
    rw [Finset.card_product, Finset.card_univ]
    exact Nat.mul_le_mul_left _ (by
      simpa only [Fintype.card_fin] using ShiftCombinatorics.card_nearCenters j.2)
  have hbad (j : S × C) : FiniteAvoidance.mass (fun _ : Ω => (1 : ℝ)) (B j) ≤
      s * (1 - s) ^ D * FiniteAvoidance.mass (fun _ : Ω => (1 : ℝ)) Set.univ := by
    have he : FiniteAvoidance.probability (B j) = p := by
      simpa only [Fintype.card_fin] using
        ShiftCombinatorics.probability_badEvent (fun c => f c j.1) j.2
    have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt Fintype.card_pos
    have he' := (div_eq_iff hc).mp he
    rw [FiniteAvoidance.mass_one_univ, he']
    exact mul_le_mul_of_nonneg_right hps (by positivity)
  have hind (j : S × C) (J : Finset (S × C)) (_hj : j ∉ J) (hJ : Disjoint J (N j)) :
      FiniteAvoidance.mass (fun _ : Ω => (1 : ℝ)) (B j ∩ FiniteAvoidance.avoids B J) *
          FiniteAvoidance.mass (fun _ : Ω => (1 : ℝ)) Set.univ =
        FiniteAvoidance.mass (fun _ : Ω => (1 : ℝ)) (B j) *
          FiniteAvoidance.mass (fun _ : Ω => (1 : ℝ)) (FiniteAvoidance.avoids B J) := by
    apply FiniteProduct.independent_of_disjoint_support _ _
      (ShiftCombinatorics.starSupport j.2)
      (FiniteProduct.supportUnion (fun k : S × C => ShiftCombinatorics.starSupport k.2) J)
    · exact ShiftCombinatorics.badEvent_dependsOn _ _
    · exact FiniteProduct.allEvents_dependsOn (fun k => (B k)ᶜ) _
        (fun k => (ShiftCombinatorics.badEvent_dependsOn _ _).compl) J
    · apply Set.disjoint_left.mpr
      rintro c hc ⟨k, hk, hck⟩
      apply Finset.disjoint_left.mp hJ hk
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
        ShiftCombinatorics.mem_nearCenters_of_shared hc hck⟩
  have hav := FiniteAvoidance.local_lemma (fun _ : Ω => (1 : ℝ))
    (fun _ => zero_le_one) htotal B N D s hs0 hs1 hdegree hbad hind Finset.univ
  obtain ⟨β, hβ⟩ := FiniteAvoidance.nonempty_of_mass_pos hav
  refine ⟨β, ?_⟩
  intro a x
  exact not_not.mp (hβ (x, a) (Finset.mem_univ _))

theorem exists_shift_table [Fintype A] [Nonempty A] [Fintype S] :
    ∃ l : ℕ, 1 ≤ l ∧ ∀ f : (Fin l → A) → (S →ₗ[K] S),
      ∃ β : (Fin l → A) → S, ShiftTableProperty l f β := by
  classical
  let r : ℝ := 1 - ((Fintype.card S : ℝ) ^ (Fintype.card A - 1))⁻¹
  have hq : (1 : ℝ) ≤ Fintype.card S := by
    exact_mod_cast Fintype.card_pos
  have hpow : (1 : ℝ) ≤ (Fintype.card S : ℝ) ^ (Fintype.card A - 1) := one_le_pow₀ hq
  have hr0 : 0 ≤ r := sub_nonneg.mpr (inv_le_one_of_one_le₀ hpow)
  have hr1 : r < 1 := by
    have hi := inv_pos.mpr (lt_of_lt_of_le zero_lt_one hpow)
    dsimp [r]
    linarith
  obtain ⟨l, hl, hnum⟩ := exists_shift_table_length (Fintype.card A) (Fintype.card S) r hr0 hr1
  exact ⟨l, hl, fun f => shift_table_at_length l hnum f⟩

end ShiftTable

end GeneralizedStarHeight

end OAI
