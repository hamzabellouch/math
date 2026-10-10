import OAI.Combinatorics.ParityLifts.TagSizes

namespace OAI

namespace ParityWL

open scoped BigOperators

section Detection

open scoped Classical

lemma sum_eq_of_color_histograms {U V D : Type} [Fintype U] [Fintype V]
    (f : U → D) (g : V → D) (a : U → ℕ) (b : V → ℕ)
    (h : Finset.univ.val.map f = Finset.univ.val.map g)
    (hab : ∀ x y, f x = g y → a x = b y) : ∑ x, a x = ∑ y, b y := by
  have hr := Multiset.rel_map.mp (Multiset.rel_eq.mpr h)
  have hs := hr.mono (fun x _ y _ hxy => hab x y hxy)
  have he : Finset.univ.val.map a = Finset.univ.val.map b :=
    Multiset.rel_eq.mp (Multiset.rel_map.mpr hs)
  exact congrArg Multiset.sum he

variable {V W : Type} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)

omit [Fintype V] [Fintype W] in
lemma atomic_eq_adj {k : ℕ} {x : Fin k → V} {y : Fin k → W}
    (h : atomicType G x = atomicType H y) (i j : Fin k) :
    G.Adj (x i) (x j) ↔ H.Adj (y i) (y j) := by
  have he := congrArg (fun a : AtomicType k => (a i j).2) h
  simpa only [atomicType, decide_eq_decide] using he

lemma joint_eq_old {k r : ℕ} {x : Fin k → V} {y : Fin k → W}
    (h : jointColor G k (r + 1) x = jointColor H k (r + 1) y) :
    jointColor G k r x = jointColor H k r y := congrArg Prod.fst h

lemma separate_eq_old {k r : ℕ} {x : Fin k → V} {y : Fin k → W}
    (h : separateColor G k (r + 1) x = separateColor H k (r + 1) y) :
    separateColor G k r x = separateColor H k r y := congrArg Prod.fst h

noncomputable def tripleCount (a b c : V) : ℕ :=
  Fintype.card {v : V // G.Adj v a ∧ G.Adj v b ∧ G.Adj v c}

lemma tripleCount_sum (a b c : V) :
    tripleCount G a b c = ∑ v : V, if G.Adj v a ∧ G.Adj v b ∧ G.Adj v c then 1 else 0 := by
  rw [tripleCount, Fintype.card_subtype, Finset.card_filter]

lemma coordinate_outside {k : ℕ} (hk : 4 ≤ k) (a b c : Fin k) :
    ∃ i : Fin k, i ≠ a ∧ i ≠ b ∧ i ≠ c := by
  have hc : ({a, b, c} : Finset (Fin k)).card ≤ 3 := by
    exact (Finset.card_insert_le _ _).trans (by
      have hh := Finset.card_insert_le b ({c} : Finset (Fin k))
      simp only [Finset.card_singleton] at hh
      omega)
  have hlt : ({a, b, c} : Finset (Fin k)).card < Fintype.card (Fin k) := by
    simpa only [Fintype.card_fin] using hc.trans_lt (by omega)
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (hlt.trans_eq (Finset.card_univ.symm))
  refine ⟨i, ?_⟩
  simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hi

lemma coordinate_other {k : ℕ} (hk : 2 ≤ k) (a : Fin k) :
    ∃ i : Fin k, i ≠ a := by
  have hlt : ({a} : Finset (Fin k)).card < Fintype.card (Fin k) := by simp; omega
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (hlt.trans_eq (Finset.card_univ.symm))
  exact ⟨i, by simpa only [Finset.mem_singleton] using hi⟩

lemma tripleCount_eq_separate_one {k : ℕ} (hk : 4 ≤ k)
    {x : Fin k → V} {y : Fin k → W}
    (h : separateColor G k 1 x = separateColor H k 1 y) (a b c : Fin k) :
    tripleCount G (x a) (x b) (x c) = tripleCount H (y a) (y b) (y c) := by
  obtain ⟨i, hia, hib, hic⟩ := coordinate_outside hk a b c
  rw [tripleCount_sum, tripleCount_sum]
  apply sum_eq_of_color_histograms
    (fun v => atomicType G (Function.update x i v))
    (fun w => atomicType H (Function.update y i w)) _ _
    (congrArg (fun z => z.2 i) h)
  intro v w he
  have hadj (p : Fin k) (hp : p ≠ i) : G.Adj v (x p) ↔ H.Adj w (y p) := by
    simpa only [Function.update_self, Function.update_of_ne hp] using atomic_eq_adj G H he i p
  simp only [hadj a hia.symm, hadj b hib.symm, hadj c hic.symm]

lemma tripleCount_eq_joint_one {k : ℕ} (hk : 2 ≤ k)
    {x : Fin k → V} {y : Fin k → W}
    (h : jointColor G k 1 x = jointColor H k 1 y) (a b c : Fin k) :
    tripleCount G (x a) (x b) (x c) = tripleCount H (y a) (y b) (y c) := by
  rw [tripleCount_sum, tripleCount_sum]
  apply sum_eq_of_color_histograms
    (fun v => fun i => atomicType G (Function.update x i v))
    (fun w => fun i => atomicType H (Function.update y i w)) _ _
    (congrArg Prod.snd h)
  intro v w he
  have hadj (p : Fin k) : G.Adj v (x p) ↔ H.Adj w (y p) := by
    obtain ⟨i, hi⟩ := coordinate_other hk p
    simpa only [Function.update_self, Function.update_of_ne hi.symm] using
      atomic_eq_adj G H (congrFun he i) i p
  simp only [hadj a, hadj b, hadj c]

def MainClique {t : ℕ} (z : Fin t → V) : Prop :=
  ∀ i j, i ≠ j → G.Adj (z i) (z j)

noncomputable def templateExtensions {t : ℕ} (z : Fin t → V) : ℕ :=
  if MainClique G z then
    ∏ h : Helper t, tripleCount G (z h.1.1.1.1) (z h.1.1.1.2) (z h.1.2) else 0

noncomputable def templateHomsEquiv (t : ℕ) :
    ((template t) →g G) ≃
      ((z : {z : Fin t → V // MainClique G z}) ×
        ((h : Helper t) → {v : V // G.Adj v (z.1 h.1.1.1.1) ∧
          G.Adj v (z.1 h.1.1.1.2) ∧ G.Adj v (z.1 h.1.2)})) where
  toFun f := ⟨⟨fun i => f (.inl i), fun i j hij => f.map_adj hij⟩,
    fun h => ⟨f (.inr h), f.map_adj (Or.inl rfl), f.map_adj (Or.inr (Or.inl rfl)),
      f.map_adj (Or.inr (Or.inr rfl))⟩⟩
  invFun f :=
    { toFun := fun v => match v with | .inl i => f.1.1 i | .inr h => (f.2 h).1
      map_rel' := by
        intro a b hab
        cases a with
        | inl i =>
          cases b with
          | inl j => exact f.1.2 i j hab
          | inr h =>
            rcases hab with hi | hi | hi <;> subst i
            · exact (f.2 h).2.1.symm
            · exact (f.2 h).2.2.1.symm
            · exact (f.2 h).2.2.2.symm
        | inr h =>
          cases b with
          | inl i =>
            rcases hab with hi | hi | hi <;> subst i
            · exact (f.2 h).2.1
            · exact (f.2 h).2.2.1
            · exact (f.2 h).2.2.2
          | inr h' => exact hab.elim }
  left_inv f := by apply RelHom.ext; intro v; cases v <;> rfl
  right_inv f := by rcases f with ⟨⟨z, hz⟩, f⟩; rfl

lemma homCount_card_equiv {U X : Type} [Fintype U] [Fintype X]
    (F : SimpleGraph U) (e : (F →g G) ≃ X) : homCount F G = Fintype.card X := by
  classical
  exact Fintype.card_congr e

lemma homCount_template (t : ℕ) :
    homCount (template t) G = ∑ z : Fin t → V, templateExtensions G z := by
  rw [homCount_card_equiv G (template t) (templateHomsEquiv G t), Fintype.card_sigma]
  simp only [Fintype.card_pi]
  exact sum_subtype_indicator (MainClique G)
    (fun z => ∏ h : Helper t, tripleCount G (z h.1.1.1.1) (z h.1.1.1.2) (z h.1.2))

lemma templateExtensions_eq_separate_one {k : ℕ} (hk : 4 ≤ k)
    {x : Fin k → V} {y : Fin k → W}
    (h : separateColor G k 1 x = separateColor H k 1 y) :
    templateExtensions G x = templateExtensions H y := by
  have hc : MainClique G x ↔ MainClique H y := by
    unfold MainClique
    exact forall_congr' (fun i => forall_congr' (fun j =>
      imp_congr_right (fun _ => atomic_eq_adj G H (separate_eq_old G H h) i j)))
  simp only [templateExtensions, hc]
  split_ifs
  · apply Finset.prod_congr rfl
    intro p _
    exact tripleCount_eq_separate_one G H hk h _ _ _
  · rfl

lemma homCount_template_eq_separate_one {k : ℕ} (hk : 4 ≤ k)
    (h : sameHistogram G H .separate k 1) :
    homCount (template k) G = homCount (template k) H := by
  rw [homCount_template, homCount_template]
  exact sum_eq_of_color_histograms _ _ _ _ h
    (fun _ _ hxy => templateExtensions_eq_separate_one G H hk hxy)

def extendTuple {k : ℕ} (x : Fin k → V) (v : V) : Fin (k + 1) → V :=
  Fin.lastCases v x

def faceIndex {k : ℕ} (i : Fin k) : Fin (k + 1) → Fin k := Fin.lastCases i id

omit [Fintype V] in
lemma extend_face {k : ℕ} (x : Fin k → V) (v : V) (i : Fin k)
    (a : Fin (k + 1)) (ha : a ≠ i.castSucc) :
    Function.update x i v (faceIndex i a) = extendTuple x v a := by
  revert ha
  refine Fin.lastCases ?_ (fun j => ?_) a
  · intro _; simp [faceIndex, extendTuple]
  · intro ha
    have hji : j ≠ i := by intro h; apply ha; exact congrArg Fin.castSucc h
    simp [faceIndex, extendTuple, Function.update_of_ne hji]

lemma face_avoiding {k : ℕ} (hk : 4 ≤ k) (a b c : Fin (k + 1)) :
    ∃ i : Fin k, a ≠ i.castSucc ∧ b ≠ i.castSucc ∧ c ≠ i.castSucc := by
  let f : Fin (k + 1) → Fin k := Fin.lastCases ⟨0, by omega⟩ id
  obtain ⟨i, hia, hib, hic⟩ := coordinate_outside hk (f a) (f b) (f c)
  refine ⟨i, ?_, ?_, ?_⟩
  · intro h; apply hia; rw [h]; simp [f]
  · intro h; apply hib; rw [h]; simp [f]
  · intro h; apply hic; rw [h]; simp [f]

lemma extend_adj_eq {k : ℕ} (hk : 4 ≤ k) {x : Fin k → V} {y : Fin k → W}
    {v : V} {w : W}
    (h : (fun i => jointColor G k 1 (Function.update x i v)) =
      (fun i => jointColor H k 1 (Function.update y i w))) (a b : Fin (k + 1)) :
    G.Adj (extendTuple x v a) (extendTuple x v b) ↔
      H.Adj (extendTuple y w a) (extendTuple y w b) := by
  obtain ⟨i, ha, hb, _⟩ := face_avoiding hk a b b
  rw [← extend_face x v i a ha, ← extend_face x v i b hb,
    ← extend_face y w i a ha, ← extend_face y w i b hb]
  exact atomic_eq_adj G H (joint_eq_old G H (congrFun h i)) _ _

lemma extend_triple_eq {k : ℕ} (hk : 4 ≤ k) {x : Fin k → V} {y : Fin k → W}
    {v : V} {w : W}
    (h : (fun i => jointColor G k 1 (Function.update x i v)) =
      (fun i => jointColor H k 1 (Function.update y i w))) (a b c : Fin (k + 1)) :
    tripleCount G (extendTuple x v a) (extendTuple x v b) (extendTuple x v c) =
      tripleCount H (extendTuple y w a) (extendTuple y w b) (extendTuple y w c) := by
  obtain ⟨i, ha, hb, hc⟩ := face_avoiding hk a b c
  rw [← extend_face x v i a ha, ← extend_face x v i b hb, ← extend_face x v i c hc,
    ← extend_face y w i a ha, ← extend_face y w i b hb, ← extend_face y w i c hc]
  exact tripleCount_eq_joint_one G H (by omega) (congrFun h i) _ _ _

lemma extensions_eq_joint_vector {k : ℕ} (hk : 4 ≤ k)
    {x : Fin k → V} {y : Fin k → W} {v : V} {w : W}
    (h : (fun i => jointColor G k 1 (Function.update x i v)) =
      (fun i => jointColor H k 1 (Function.update y i w))) :
    templateExtensions G (extendTuple x v) = templateExtensions H (extendTuple y w) := by
  have hc : MainClique G (extendTuple x v) ↔ MainClique H (extendTuple y w) := by
    unfold MainClique
    exact forall_congr' (fun i => forall_congr' (fun j =>
      imp_congr_right (fun _ => extend_adj_eq G H hk h i j)))
  simp only [templateExtensions, hc]
  split_ifs
  · apply Finset.prod_congr rfl
    intro p _
    exact extend_triple_eq G H hk h _ _ _
  · rfl

noncomputable def jointTemplateValue {k : ℕ} (x : Fin k → V) : ℕ :=
  ∑ v : V, templateExtensions G (extendTuple x v)

lemma jointTemplateValue_eq {k : ℕ} (hk : 4 ≤ k) {x : Fin k → V} {y : Fin k → W}
    (h : jointColor G k 2 x = jointColor H k 2 y) :
    jointTemplateValue G x = jointTemplateValue H y := by
  exact sum_eq_of_color_histograms _ _ _ _ (congrArg Prod.snd h)
    (fun v w he => extensions_eq_joint_vector G H hk he)

def extendTupleEquiv (k : ℕ) : ((Fin k → V) × V) ≃ (Fin (k + 1) → V) where
  toFun q := extendTuple q.1 q.2
  invFun z := (fun i => z i.castSucc, z (Fin.last k))
  left_inv q := by rcases q with ⟨x, v⟩; simp [extendTuple]
  right_inv z := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [extendTuple]

lemma homCount_template_joint (k : ℕ) :
    homCount (template (k + 1)) G = ∑ x : Fin k → V, jointTemplateValue G x := by
  rw [homCount_template]
  symm
  change (∑ x : Fin k → V, ∑ v : V, templateExtensions G (extendTuple x v)) = _
  calc
    _ = ∑ q : (Fin k → V) × V, templateExtensions G (extendTuple q.1 q.2) :=
      (Fintype.sum_prod_type _).symm
    _ = _ := Fintype.sum_equiv (extendTupleEquiv k) _ _ (fun _ => rfl)

lemma homCount_template_eq_joint_two {k : ℕ} (hk : 4 ≤ k)
    (h : sameHistogram G H .joint k 2) :
    homCount (template (k + 1)) G = homCount (template (k + 1)) H := by
  rw [homCount_template_joint, homCount_template_joint]
  exact sum_eq_of_color_histograms _ _ _ _ h
    (fun _ _ hxy => jointTemplateValue_eq G H hk hxy)

lemma tripleCount_inl (a b c : V) :
    tripleCount (G.sum H) (.inl a) (.inl b) (.inl c) = tripleCount G a b c := by
  rw [tripleCount_sum, tripleCount_sum, Fintype.sum_sum_type]
  simp only [SimpleGraph.sum_adj, false_and, ite_false, Finset.sum_const_zero, add_zero]

lemma tripleCount_inr (a b c : W) :
    tripleCount (G.sum H) (.inr a) (.inr b) (.inr c) = tripleCount H a b c := by
  rw [tripleCount_sum, tripleCount_sum, Fintype.sum_sum_type]
  simp only [SimpleGraph.sum_adj, false_and, ite_false, Finset.sum_const_zero, zero_add]

lemma templateExtensions_inl {t : ℕ} (z : Fin t → V) :
    templateExtensions (G.sum H) (Sum.inl ∘ z) = templateExtensions G z := by
  have hc : MainClique (G.sum H) (Sum.inl ∘ z) ↔ MainClique G z := Iff.rfl
  by_cases h : MainClique G z
  · simp only [templateExtensions, ite_eq_left h, ite_eq_left (hc.mpr h), Function.comp_apply]
    exact Finset.prod_congr rfl (fun p _ => tripleCount_inl G H _ _ _)
  · simp only [templateExtensions, ite_eq_right h, ite_eq_right (mt hc.mp h)]

lemma templateExtensions_inr {t : ℕ} (z : Fin t → W) :
    templateExtensions (G.sum H) (Sum.inr ∘ z) = templateExtensions H z := by
  have hc : MainClique (G.sum H) (Sum.inr ∘ z) ↔ MainClique H z := Iff.rfl
  by_cases h : MainClique H z
  · simp only [templateExtensions, ite_eq_left h, ite_eq_left (hc.mpr h), Function.comp_apply]
    exact Finset.prod_congr rfl (fun p _ => tripleCount_inr G H _ _ _)
  · simp only [templateExtensions, ite_eq_right h, ite_eq_right (mt hc.mp h)]

lemma homCount_template_eq_pure_separate_one {k : ℕ} (hk : 4 ≤ k)
    (h : samePureHistogram G H .separate k 1) :
    homCount (template k) G = homCount (template k) H := by
  rw [homCount_template, homCount_template]
  apply sum_eq_of_color_histograms _ _ _ _ h
  intro x y he
  rw [← templateExtensions_inl G H, ← templateExtensions_inr G H]
  exact templateExtensions_eq_separate_one (G.sum H) (G.sum H) hk he

omit [Fintype V] in
lemma extendTuple_map {X : Type} {k : ℕ} (f : V → X) (x : Fin k → V) (v : V) :
    extendTuple (f ∘ x) (f v) = f ∘ extendTuple x v := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [extendTuple]

lemma jointTemplateValue_inl {k : ℕ} (hk : 1 ≤ k) (x : Fin k → V) :
    jointTemplateValue (G.sum H) (Sum.inl ∘ x) = jointTemplateValue G x := by
  unfold jointTemplateValue
  rw [Fintype.sum_sum_type]
  have hz (w : W) : templateExtensions (G.sum H) (extendTuple (Sum.inl ∘ x) (.inr w)) = 0 := by
    have hnc : ¬ MainClique (G.sum H) (extendTuple (Sum.inl ∘ x) (.inr w)) := by
      intro hc
      have hh := hc (⟨0, by omega⟩ : Fin k).castSucc (Fin.last k) (Fin.castSucc_ne_last _)
      simp only [extendTuple, Fin.lastCases_castSucc, Fin.lastCases_last,
        Function.comp_apply, SimpleGraph.sum_adj] at hh
    simp only [templateExtensions, ite_eq_right hnc]
  simp only [extendTuple_map, templateExtensions_inl, hz, Finset.sum_const_zero, add_zero]

lemma jointTemplateValue_inr {k : ℕ} (hk : 1 ≤ k) (x : Fin k → W) :
    jointTemplateValue (G.sum H) (Sum.inr ∘ x) = jointTemplateValue H x := by
  unfold jointTemplateValue
  rw [Fintype.sum_sum_type]
  have hz (v : V) : templateExtensions (G.sum H) (extendTuple (Sum.inr ∘ x) (.inl v)) = 0 := by
    have hnc : ¬ MainClique (G.sum H) (extendTuple (Sum.inr ∘ x) (.inl v)) := by
      intro hc
      have hh := hc (⟨0, by omega⟩ : Fin k).castSucc (Fin.last k) (Fin.castSucc_ne_last _)
      simp only [extendTuple, Fin.lastCases_castSucc, Fin.lastCases_last,
        Function.comp_apply, SimpleGraph.sum_adj] at hh
    simp only [templateExtensions, ite_eq_right hnc]
  simp only [extendTuple_map, templateExtensions_inr, hz, Finset.sum_const_zero, zero_add]

lemma homCount_template_eq_pure_joint_two {k : ℕ} (hk : 4 ≤ k)
    (h : samePureHistogram G H .joint k 2) :
    homCount (template (k + 1)) G = homCount (template (k + 1)) H := by
  rw [homCount_template_joint, homCount_template_joint]
  apply sum_eq_of_color_histograms _ _ _ _ h
  intro x y he
  rw [← jointTemplateValue_inl G H (by omega), ← jointTemplateValue_inr G H (by omega)]
  exact jointTemplateValue_eq (G.sum H) (G.sum H) hk he

end Detection

/-- The "compatible choice" direction, including the claimed short round and
both implementations. This uses the actual uncolored graphs. -/
theorem successful_detected (k : ℕ) (hk : 4 ≤ k) (c : Convention)
    (C : ChoiceSystem (bagParameter c k)) (hs : C.Successful) :
    ¬ sameHistogram (zeroLift C) (starLift C) c k (detectionRound c) ∧
    ¬ samePureHistogram (zeroLift C) (starLift C) c k (detectionRound c) := by
  have hg := successful_template_count_gap (C := C) (show 0 < bagParameter c k by
    cases c <;> simp only [bagParameter] <;> omega) hs
  cases c
  · constructor
    · intro h
      exact (ne_of_lt hg) (homCount_template_eq_joint_two _ _ hk h).symm
    · intro h
      exact (ne_of_lt hg) (homCount_template_eq_pure_joint_two _ _ hk h).symm
  · constructor
    · intro h
      exact (ne_of_lt hg) (homCount_template_eq_separate_one _ _ hk h).symm
    · intro h
      exact (ne_of_lt hg) (homCount_template_eq_pure_separate_one _ _ hk h).symm

theorem equivalent_no_choice (k : ℕ) (hk : 4 ≤ k) (c : Convention)
    (C : ChoiceSystem (bagParameter c k))
    (h : WLEquivalent (zeroLift C) (starLift C) c k) : ¬ C.Successful := by
  intro hs
  exact (successful_detected k hk c C hs).1 (h (detectionRound c))

theorem pure_equivalent_no_choice (k : ℕ) (hk : 4 ≤ k) (c : Convention)
    (C : ChoiceSystem (bagParameter c k))
    (h : PureWLEquivalent (zeroLift C) (starLift C) c k) : ¬ C.Successful := by
  intro hs
  exact (successful_detected k hk c C hs).2 (h (detectionRound c))

end ParityWL

end OAI
