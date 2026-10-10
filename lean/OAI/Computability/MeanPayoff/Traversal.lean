import OAI.Computability.MeanPayoff.Volume

namespace OAI

section

namespace MeanPayoff
namespace RandomTree

theorem traverse_relation_error {α β : Type} (f : α → RandomTree β)
    (R : α → β → Prop) (as : List α) {ε : ℚ} (hε : 0 ≤ ε)
    (hf : ∀ a ∈ as, (f a).probability (fun b => ¬R a b) ≤ ε) :
    (traverse f as).probability (fun bs => ¬List.Forall₂ R as bs) ≤ (as.length : ℚ) * ε := by
  classical
  induction as with
  | nil => simp [traverse]
  | cons a as ih =>
    rw [traverse]
    have ht := ih (fun x hx => hf x (List.mem_cons_of_mem a hx))
    apply le_trans (bind_error (f a) (fun b => (traverse f as).map (b :: ·))
      (R a) (fun bs => ¬List.Forall₂ R (a :: as) bs)
      (ρ := ε) (ε := (as.length : ℚ) * ε)
      (mul_nonneg (Nat.cast_nonneg _) hε) (hf a (List.mem_cons_self ..)) ?_) ?_
    · intro b hb
      exact map_error (traverse f as) (b :: ·) (List.Forall₂ R as)
        (fun bs => ¬List.Forall₂ R (a :: as) bs) ht
        (fun bs hbs => not_not_intro (List.Forall₂.cons hb hbs))
    · simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring_nf
      rfl

end RandomTree

theorem forall₂_member_left {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β}
    (h : List.Forall₂ R as bs) {a : α} (ha : a ∈ as) : ∃ b ∈ bs, R a b := by
  induction h with
  | nil => simp at ha
  | @cons x b as bs hr ht ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨b, List.mem_cons_self .., hr⟩
    · obtain ⟨c, hc, hr⟩ := ih ha
      exact ⟨c, List.mem_cons_of_mem b hc, hr⟩

theorem forall₂_right_all {α β : Type} {R : α → β → Prop} {Q : β → Prop}
    {as : List α} {bs : List β} (h : List.Forall₂ R as bs)
    (hq : ∀ a b, R a b → Q b) : ∀ b ∈ bs, Q b := by
  induction h with
  | nil => simp
  | @cons a b as bs hr ht ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hq a c hr
    · exact ih c hc

namespace SolveBox

theorem fold_min_lower {n Bmax : ℕ} (I : SolveBox n Bmax) (rs : List (BoxVector I))
    (p : BoxVector I) {y : Vec (Fin n)} (hp : y ≤ p.val)
    (hr : ∀ r ∈ rs, y ≤ r.val) : y ≤ (rs.foldl I.minVector p).val := by
  induction rs generalizing p with
  | nil => exact hp
  | cons r rs ih =>
    apply ih (I.minVector p r)
    · intro i
      exact le_min (hp i) (hr r (List.mem_cons_self ..) i)
    · exact fun s hs => hr s (List.mem_cons_of_mem r hs)

theorem fold_max_upper {n Bmax : ℕ} (I : SolveBox n Bmax) (rs : List (BoxVector I))
    (p : BoxVector I) {z : Vec (Fin n)} (hp : p.val ≤ z)
    (hr : ∀ r ∈ rs, r.val ≤ z) : (rs.foldl I.maxVector p).val ≤ z := by
  induction rs generalizing p with
  | nil => exact hp
  | cons r rs ih =>
    apply ih (I.maxVector p r)
    · intro i
      exact max_le (hp i) (hr r (List.mem_cons_self ..) i)
    · exact fun s hs => hr s (List.mem_cons_of_mem r hs)

theorem fold_max_seed {n Bmax : ℕ} (I : SolveBox n Bmax) (rs : List (BoxVector I))
    (p : BoxVector I) : p.val ≤ (rs.foldl I.maxVector p).val := by
  induction rs generalizing p with
  | nil => exact le_refl _
  | cons r rs ih =>
    intro i
    exact (le_max_left (p.val i) (r.val i)).trans (ih _ i)

theorem fold_min_seed {n Bmax : ℕ} (I : SolveBox n Bmax) (rs : List (BoxVector I))
    (p : BoxVector I) : (rs.foldl I.minVector p).val ≤ p.val := by
  induction rs generalizing p with
  | nil => exact le_refl _
  | cons r rs ih => exact (ih _).trans (fun i => min_le_left (p.val i) (r.val i))

theorem fold_max_member {n Bmax : ℕ} (I : SolveBox n Bmax) (rs : List (BoxVector I))
    (p : BoxVector I) {r : BoxVector I} (hr : r ∈ rs) : r.val ≤ (rs.foldl I.maxVector p).val := by
  induction rs generalizing p with
  | nil => simp at hr
  | cons s rs ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · intro i
      exact (le_max_right (p.val i) (r.val i)).trans (I.fold_max_seed rs _ i)
    · exact ih _ hr

theorem fold_min_member {n Bmax : ℕ} (I : SolveBox n Bmax) (rs : List (BoxVector I))
    (p : BoxVector I) {r : BoxVector I} (hr : r ∈ rs) : (rs.foldl I.minVector p).val ≤ r.val := by
  induction rs generalizing p with
  | nil => simp at hr
  | cons s rs ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (I.fold_min_seed rs _).trans (fun i => min_le_right (p.val i) (r.val i))
    · exact ih _ hr

theorem volume_le {n Bmax : ℕ} (I : SolveBox n Bmax) : volume I.b I.a ≤ n * Bmax := by
  calc
    _ ≤ ∑ _i : Fin n, Bmax := Finset.sum_le_sum (fun i _ => by
      apply (Int.toNat_le).mpr
      exact (I.width_bound i).trans (by exact_mod_cast I.bounded))
    _ = _ := by simp

end SolveBox


def HighAccuracy (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax)
    (t : RandomTree (BoxVector I)) (δ : ℚ) : Prop :=
  ∀ y, AdmissibleSub (operator G) I.a I.b y P → t.probability (fun p => ¬y ≤ p.val) ≤ δ

def LowAccuracy (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax)
    (t : RandomTree (BoxVector I)) (δ : ℚ) : Prop :=
  ∀ z, AdmissibleSuper (operator G) I.a I.b z P → t.probability (fun p => ¬p.val ≤ z) ≤ δ

theorem RandomTree.imp_error {α : Type} (t : RandomTree α) (Q : Prop) (R : α → Prop)
    {ε : ℚ} (hε : 0 ≤ ε) (h : Q → t.probability (fun a => ¬R a) ≤ ε) :
    t.probability (fun a => ¬(Q → R a)) ≤ ε := by
  classical
  by_cases hQ : Q
  · simpa only [hQ, true_implies] using h hQ
  · have hz : t.All (fun a => Q → R a) := RandomTree.all_of_forall t (fun _ q => (hQ q).elim)
    rw [RandomTree.failure_zero t hz]
    exact hε

theorem finishChoice_high (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hl : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width) (O : Orientation P)
    (up : RandomTree (BoxVector (I.capHigh I.C I.C_positive (I.C_smaller hB).le)))
    (lo : RandomTree (BoxVector (I.capLow I.C I.C_positive (I.C_smaller hB).le)))
    {δ : ℚ} (hδ : 0 ≤ δ)
    (hup : HighAccuracy G P _ up δ) (hlo : HighAccuracy G P _ lo δ)
    (y : Vec (Fin G.n)) (hy : AdmissibleSub (operator G) I.a I.b y P)
    (ho : (I.C : ℤ) < deviation G y I.a → HighAlternative I P y O) :
    (finishChoice G P hR lower I hB O up lo).probability (fun p : BoxVector I => ¬y ≤ p.val) ≤
      (O.exceptions.length : ℚ) * epsilon G.n Bmax + δ := by
  classical
  have he := epsilon_nonneg G.n Bmax
  unfold finishChoice
  split_ifs with hY
  · let K := I.capHigh I.C I.C_positive (I.C_smaller hB).le
    let u : Vec (Fin G.n) := fun i => max (y i) (K.a i)
    have hua : AdmissibleSub (operator G) K.a K.b u P :=
      hy.raise_floor (operator_laws G) (fun i => le_max_left _ _) K.ordered
    let f := fun H : SmallSet P => I.repeated
      (lower (P.reweightM H.val) (P.reweightM_rank G.positive hR H.property) I) (globalJ G.n Bmax)
    have ht : (RandomTree.traverse f O.exceptions).probability
        (fun rs => ¬List.Forall₂ (fun (_ : SmallSet P) (r : BoxVector I) => y ≤ r.val) O.exceptions rs) ≤
        (O.exceptions.length : ℚ) * epsilon G.n Bmax := by
      apply RandomTree.traverse_relation_error f _ _ he
      intro H _
      exact hl.ask_high G _ _ I hy
    apply RandomTree.bind_error (RandomTree.traverse f O.exceptions) _
      (List.Forall₂ (fun (_ : SmallSet P) (r : BoxVector I) => y ≤ r.val) O.exceptions)
      (fun p : BoxVector I => ¬y ≤ p.val) hδ ht
    intro rs hrs
    apply RandomTree.map_error up _ (fun p => u ≤ p.val) _ (hup u hua)
    intro p hp hf
    apply hf
    apply I.fold_min_lower
    · exact fun i => (le_max_left (y i) (K.a i)).trans (hp i)
    · exact forall₂_right_all hrs (fun _ _ hr => hr)
  · let K := I.capLow I.C I.C_positive (I.C_smaller hB).le
    let f := fun H : SmallSet P => I.repeated
      (lower (P.reweightK H.val) (P.reweightK_rank G.positive hR H.property) I) (globalJ G.n Bmax)
    by_cases hyK : y ≤ K.b
    · apply le_trans (RandomTree.bind_probability_le (RandomTree.traverse f O.exceptions) _
        (fun p : BoxVector I => ¬y ≤ p.val) (ε := δ) ?_) ?_
      · intro rs
        apply RandomTree.map_error lo _ (fun p => y ≤ p.val) _ (hlo y (hy.restrict_ceiling hyK))
        intro p hp hf
        exact hf (hp.trans (I.fold_max_seed rs _))
      · exact le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) he)
    · have hd : (I.C : ℤ) < deviation G y I.a := by
        by_contra hn
        apply hyK
        intro i
        change y i ≤ min (I.b i) (I.a i + I.C)
        have hh := le_deviation G y I.a i
        have hb : y i ≤ I.b i := hy.1.1.2 i
        omega
      have hw : ∃ H ∈ O.exceptions, (4 / 5) * P.k < mass P.alpha (lowerActive I.a y ∩ H.val) := by
        rcases ho hd with hy | hw
        · exact (hY hy).elim
        · exact hw
      let R := fun (H : SmallSet P) (r : BoxVector I) =>
        (4 / 5) * P.k < mass P.alpha (lowerActive I.a y ∩ H.val) → y ≤ r.val
      have ht : (RandomTree.traverse f O.exceptions).probability
          (fun rs => ¬List.Forall₂ R O.exceptions rs) ≤
          (O.exceptions.length : ℚ) * epsilon G.n Bmax := by
        apply RandomTree.traverse_relation_error f R _ he
        intro H _
        apply RandomTree.imp_error _ _ _ he
        intro hH
        exact hl.ask_high G _ _ I (reweight_admissible_sub hy hH)
      apply RandomTree.bind_error (RandomTree.traverse f O.exceptions) _
        (List.Forall₂ R O.exceptions) (fun p : BoxVector I => ¬y ≤ p.val) hδ ht
      intro rs hrs
      obtain ⟨H, hH, hm⟩ := hw
      obtain ⟨r, hr, hRr⟩ := forall₂_member_left hrs hH
      have hok : (lo.map (fun p => rs.foldl I.maxVector
          (I.includeCapLow I.C I.C_positive (I.C_smaller hB).le p))).All (fun p => y ≤ p.val) := by
        rw [RandomTree.map, RandomTree.all_bind]
        apply RandomTree.all_of_forall
        intro p
        exact (hRr hm).trans (I.fold_max_member rs _ hr)
      rw [RandomTree.failure_zero _ hok]
      exact hδ



theorem finishChoice_low (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hl : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width) (O : Orientation P)
    (up : RandomTree (BoxVector (I.capHigh I.C I.C_positive (I.C_smaller hB).le)))
    (lo : RandomTree (BoxVector (I.capLow I.C I.C_positive (I.C_smaller hB).le)))
    {δ : ℚ} (hδ : 0 ≤ δ)
    (hup : LowAccuracy G P _ up δ) (hlo : LowAccuracy G P _ lo δ)
    (z : Vec (Fin G.n)) (hz : AdmissibleSuper (operator G) I.a I.b z P)
    (ho : (I.C : ℤ) < deviation G I.b z → LowAlternative I P z O) :
    (finishChoice G P hR lower I hB O up lo).probability (fun p : BoxVector I => ¬p.val ≤ z) ≤
      (O.exceptions.length : ℚ) * epsilon G.n Bmax + δ := by
  classical
  have he := epsilon_nonneg G.n Bmax
  unfold finishChoice
  split_ifs with hY
  · let K := I.capHigh I.C I.C_positive (I.C_smaller hB).le
    let f := fun H : SmallSet P => I.repeated
      (lower (P.reweightM H.val) (P.reweightM_rank G.positive hR H.property) I) (globalJ G.n Bmax)
    by_cases hzK : K.a ≤ z
    · apply le_trans (RandomTree.bind_probability_le (RandomTree.traverse f O.exceptions) _
        (fun p : BoxVector I => ¬p.val ≤ z) (ε := δ) ?_) ?_
      · intro rs
        apply RandomTree.map_error up _ (fun p => p.val ≤ z) _ (hup z (hz.restrict_floor hzK))
        intro p hp hf
        exact hf ((I.fold_min_seed rs _).trans hp)
      · exact le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) he)
    · have hd : (I.C : ℤ) < deviation G I.b z := by
        by_contra hn
        apply hzK
        intro i
        change max (I.a i) (I.b i - I.C) ≤ z i
        have hh := le_deviation G I.b z i
        have ha : I.a i ≤ z i := hz.1.1.1 i
        omega
      have hw : ∃ H ∈ O.exceptions, (4 / 5) * P.m < mass P.beta (upperActive I.b z ∩ H.val) := by
        rcases ho hd with hs | hw
        · simp [hY] at hs
        · exact hw
      let R := fun (H : SmallSet P) (r : BoxVector I) =>
        (4 / 5) * P.m < mass P.beta (upperActive I.b z ∩ H.val) → r.val ≤ z
      have ht : (RandomTree.traverse f O.exceptions).probability
          (fun rs => ¬List.Forall₂ R O.exceptions rs) ≤
          (O.exceptions.length : ℚ) * epsilon G.n Bmax := by
        apply RandomTree.traverse_relation_error f R _ he
        intro H _
        apply RandomTree.imp_error _ _ _ he
        intro hH
        exact hl.ask_low G _ _ I (reweight_admissible_super hz hH)
      apply RandomTree.bind_error (RandomTree.traverse f O.exceptions) _
        (List.Forall₂ R O.exceptions) (fun p : BoxVector I => ¬p.val ≤ z) hδ ht
      intro rs hrs
      obtain ⟨H, hH, hm⟩ := hw
      obtain ⟨r, hr, hRr⟩ := forall₂_member_left hrs hH
      have hok : (up.map (fun p => rs.foldl I.minVector
          (I.includeCapHigh I.C I.C_positive (I.C_smaller hB).le p))).All (fun p => p.val ≤ z) := by
        rw [RandomTree.map, RandomTree.all_bind]
        apply RandomTree.all_of_forall
        intro p
        exact (I.fold_min_member rs _ hr).trans (hRr hm)
      rw [RandomTree.failure_zero _ hok]
      exact hδ
  · let K := I.capLow I.C I.C_positive (I.C_smaller hB).le
    let u : Vec (Fin G.n) := fun i => min (z i) (K.b i)
    have hua : AdmissibleSuper (operator G) K.a K.b u P :=
      hz.lower_ceiling (operator_laws G) K.ordered (fun i => min_le_left _ _)
    let f := fun H : SmallSet P => I.repeated
      (lower (P.reweightK H.val) (P.reweightK_rank G.positive hR H.property) I) (globalJ G.n Bmax)
    have ht : (RandomTree.traverse f O.exceptions).probability
        (fun rs => ¬List.Forall₂ (fun (_ : SmallSet P) (r : BoxVector I) => r.val ≤ z) O.exceptions rs) ≤
        (O.exceptions.length : ℚ) * epsilon G.n Bmax := by
      apply RandomTree.traverse_relation_error f _ _ he
      intro H _
      exact hl.ask_low G _ _ I hz
    apply RandomTree.bind_error (RandomTree.traverse f O.exceptions) _
      (List.Forall₂ (fun (_ : SmallSet P) (r : BoxVector I) => r.val ≤ z) O.exceptions)
      (fun p : BoxVector I => ¬p.val ≤ z) hδ ht
    intro rs hrs
    apply RandomTree.map_error lo _ (fun p => p.val ≤ u) _ (hlo u hua)
    intro p hp hf
    apply hf
    apply I.fold_max_upper
    · exact fun i => (hp i).trans (min_le_left (z i) (K.b i))
    · exact forall₂_right_all hrs (fun _ _ hr => hr)

end MeanPayoff
end

end OAI
