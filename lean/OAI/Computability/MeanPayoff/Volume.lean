import OAI.Computability.MeanPayoff.Tightening

namespace OAI

section

namespace MeanPayoff

theorem orientationTail_length (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (I : SolveBox G.n Bmax) (qs : List (BoxVector I))
    (child : BoxVector I → RandomTree (Orientation P)) (M : ℕ)
    (hm : ∀ q, (child q).All (fun O => O.exceptions.length ≤ M)) :
    (orientationTail G P I qs child).All (fun O => O.exceptions.length ≤ M + 2) := by
  unfold orientationTail
  dsimp only
  split_ifs
  · change 1 ≤ M + 2
    omega
  · change 1 ≤ M + 2
    omega
  · rw [RandomTree.all_bind]
    apply RandomTree.all_of_forall
    intro j
    rw [RandomTree.map, RandomTree.all_bind]
    apply RandomTree.all_mono _ (hm _)
    intro O hO
    change (O.exceptions ++ [_, _]).length ≤ M + 2
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem orient_length (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax) :
    (orient G P hR lower I).All (fun O => O.exceptions.length ≤ 2 * Nat.clog 2 I.width + 1) := by
  by_cases hsmall : I.width ≤ 128 * globalS Bmax
  · rw [orient, dite_eq_left hsmall]
    change (orientBase G P I).exceptions.length ≤ _
    unfold orientBase
    dsimp only
    split_ifs <;> change 1 ≤ _ <;> omega
  · have hB : 128 * globalS Bmax < I.width := Nat.lt_of_not_ge hsmall
    rw [orient, dite_eq_right hsmall]
    dsimp only
    rw [RandomTree.all_bind]
    with_reducible
      refine RandomTree.all_of_forall (centerSteps P hR lower I hB (globalS Bmax) I.midpoint) ?_
    intro qs
    have hr := (I.radius_bounds hB).2.2.2
    have hs := globalS_large Bmax
    have hc := clog_double_decrease (by omega : 1 < I.width) (by omega : 2 * (2 * I.E) ≤ I.width)
    apply RandomTree.all_mono _ (orientationTail_length G P I qs _ (2 * Nat.clog 2 (2 * I.E) + 1)
      (fun q => orient_length G P hR lower (I.wideCentered hB q.val)))
    intro O hO
    omega
termination_by I.width
decreasing_by exact I.E_smaller

theorem flatten_length_bound {α : Type} (ls : List (List α)) (M : ℕ)
    (h : ∀ l ∈ ls, l.length ≤ M) : ls.flatten.length ≤ ls.length * M := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
    have hl := h l (List.mem_cons_self ..)
    have ht := ih (fun t ht => h t (List.mem_cons_of_mem _ ht))
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    nlinarith only [hl, ht]

def globalListBound (n Bmax : ℕ) : ℕ := globalJ n Bmax * (2 * globalG Bmax + 3)

theorem orientPlus_length (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax) :
    (orientPlus (orient G P hR lower I) (globalJ G.n Bmax)).All
      (fun O => O.exceptions.length ≤ globalListBound G.n Bmax) := by
  rw [orientPlus, RandomTree.map, RandomTree.all_bind]
  have hall := RandomTree.trials_all _ (orient_length G P hR lower I) (globalJ G.n Bmax)
  have hh := RandomTree.all_and _ (RandomTree.trials_length _ _) hall
  apply RandomTree.all_mono _ hh
  intro os hos
  change (os.map Orientation.exceptions).flatten.length ≤ _
  have hf := flatten_length_bound (os.map Orientation.exceptions) (2 * Nat.clog 2 I.width + 1)
    (by
      intro l hl
      obtain ⟨O, hO, rfl⟩ := List.mem_map.mp hl
      exact hos.2 O hO)
  simp only [List.length_map, hos.1] at hf
  have hc := Nat.clog_mono_right 2 (I.bounded.trans (Nat.le_succ Bmax))
  change Nat.clog 2 I.width ≤ Nat.clog 2 (Bmax + 1) at hc
  have hcg : 2 * Nat.clog 2 I.width + 1 ≤ 2 * globalG Bmax + 3 := by unfold globalG; omega
  exact hf.trans (Nat.mul_le_mul_left _ hcg)


open scoped Classical

theorem LowerComparisons.ask_high (G : Game) {Bmax : ℕ} {P : Budgets G.n}
    {lower : LowerSolver (Bmax := Bmax) P} (hl : LowerComparisons G P lower)
    (Q : Budgets G.n) (hQ : parameterRank Q.parameter < parameterRank P.parameter)
    (I : SolveBox G.n Bmax) {y : Vec (Fin G.n)}
    (hy : AdmissibleSub (operator G) I.a I.b y Q) :
    (I.repeated (lower Q hQ I) (globalJ G.n Bmax)).probability (fun p => ¬y ≤ p.val) ≤
      epsilon G.n Bmax :=
  I.repeated_lower _ ((hl Q hQ).1 I y hy) (globalJ_positive _ _)

theorem LowerComparisons.ask_low (G : Game) {Bmax : ℕ} {P : Budgets G.n}
    {lower : LowerSolver (Bmax := Bmax) P} (hl : LowerComparisons G P lower)
    (Q : Budgets G.n) (hQ : parameterRank Q.parameter < parameterRank P.parameter)
    (I : SolveBox G.n Bmax) {z : Vec (Fin G.n)}
    (hz : AdmissibleSuper (operator G) I.a I.b z Q) :
    (I.repeated (lower Q hQ I) (globalJ G.n Bmax)).probability (fun p => ¬p.val ≤ z) ≤
      epsilon G.n Bmax :=
  I.repeated_upper _ ((hl Q hQ).2 I z hz) (globalJ_positive _ _)

def TightHigh (G : Game) {Bmax : ℕ} (P : Budgets G.n) {I : SolveBox G.n Bmax}
    (y : Vec (Fin G.n)) (T : InnerBox I) : Prop :=
  ∃ u, y ≤ u ∧ AdmissibleSub (operator G) T.box.a T.box.b u P ∧
    ((T.box.C : ℤ) < deviation G u T.box.a → (4 / 5) * P.k < mass P.alpha (highCore T.box u))

def TightLow (G : Game) {Bmax : ℕ} (P : Budgets G.n) {I : SolveBox G.n Bmax}
    (z : Vec (Fin G.n)) (T : InnerBox I) : Prop :=
  ∃ u, u ≤ z ∧ AdmissibleSuper (operator G) T.box.a T.box.b u P ∧
    ((T.box.C : ℤ) < deviation G T.box.b u → (4 / 5) * P.m < mass P.beta (lowCore T.box u))

def TightHighRequest (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax)
    (y : Vec (Fin G.n)) (r : BoxVector I) : Prop :=
  (I.C : ℤ) < deviation G y I.a → mass P.alpha (highCore I y) ≤ (4 / 5) * P.k →
    tightSub G I y ≤ r.val

def TightLowRequest (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax)
    (z : Vec (Fin G.n)) (r : BoxVector I) : Prop :=
  (I.C : ℤ) < deviation G I.b z → mass P.beta (lowCore I z) ≤ (4 / 5) * P.m →
    r.val ≤ tightSuper G I z

theorem tightRequest_high (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hl : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) {y : Vec (Fin G.n)}
    (hy : AdmissibleSub (operator G) I.a I.b y P) :
    (I.repeated (lower P.reduceK (P.reduceK_rank hR) I) (globalJ G.n Bmax)).probability
      (fun r => ¬TightHighRequest G P I y r) ≤ epsilon G.n Bmax := by
  by_cases hd : (I.C : ℤ) < deviation G y I.a
  · by_cases hc : mass P.alpha (highCore I y) ≤ (4 / 5) * P.k
    · have hu : AdmissibleSub (operator G) I.a I.b (tightSub G I y) P.reduceK :=
        ⟨tightSub_solution G I hy.1 hd,
          (mass_mono (fun i => (P.alpha_pos i).le) (tightSub_core G I y hd)).trans hc⟩
      apply le_trans _ (hl.ask_high G P.reduceK (P.reduceK_rank hR) I hu)
      exact RandomTree.probability_mono _ (fun r hf hr => hf (fun _ _ => hr))
    · rw [RandomTree.failure_zero (P := TightHighRequest G P I y) _ (RandomTree.all_of_forall _ (fun _ _ hh => (hc hh).elim))]
      exact epsilon_nonneg _ _
  · rw [RandomTree.failure_zero (P := TightHighRequest G P I y) _ (RandomTree.all_of_forall _ (fun _ hh => (hd hh).elim))]
    exact epsilon_nonneg _ _

theorem tightRequest_low (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hl : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) {z : Vec (Fin G.n)}
    (hz : AdmissibleSuper (operator G) I.a I.b z P) :
    (I.repeated (lower P.reduceM (P.reduceM_rank hR) I) (globalJ G.n Bmax)).probability
      (fun r => ¬TightLowRequest G P I z r) ≤ epsilon G.n Bmax := by
  by_cases hd : (I.C : ℤ) < deviation G I.b z
  · by_cases hc : mass P.beta (lowCore I z) ≤ (4 / 5) * P.m
    · have hu : AdmissibleSuper (operator G) I.a I.b (tightSuper G I z) P.reduceM :=
        ⟨tightSuper_solution G I hz.1 hd,
          (mass_mono (fun i => (P.beta_pos i).le) (tightSuper_core G I z hd)).trans hc⟩
      apply le_trans _ (hl.ask_low G P.reduceM (P.reduceM_rank hR) I hu)
      exact RandomTree.probability_mono _ (fun r hf hr => hf (fun _ _ => hr))
    · rw [RandomTree.failure_zero (P := TightLowRequest G P I z) _ (RandomTree.all_of_forall _ (fun _ _ hh => (hc hh).elim))]
      exact epsilon_nonneg _ _
  · rw [RandomTree.failure_zero (P := TightLowRequest G P I z) _ (RandomTree.all_of_forall _ (fun _ hh => (hd hh).elim))]
    exact epsilon_nonneg _ _

theorem floor_update_volume {n Bmax : ℕ} (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (r : BoxVector I)
    (h : ∃ i, (I.delta : ℤ) ≤ r.val i - I.a i) :
    volume (I.withFloor r).b (I.withFloor r).a < volume I.b I.a := by
  apply volume_decreases r.property.1 r.property.2
  obtain ⟨i, hi⟩ := h
  have hd := I.delta_positive hB
  intro heq
  have he := congrFun heq i
  omega

theorem ceiling_update_volume {n Bmax : ℕ} (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (r : BoxVector I)
    (h : ∃ i, (I.delta : ℤ) ≤ I.b i - r.val i) :
    volume (I.withCeiling r).b (I.withCeiling r).a < volume I.b I.a := by
  apply volume_ceiling_decreases r.property.1 r.property.2
  obtain ⟨i, hi⟩ := h
  have hd := I.delta_positive hB
  intro heq
  have he := congrFun heq i
  omega

theorem volume_error_step {v w : ℕ} (h : w < v) {ε : ℚ} (hε : 0 ≤ ε) :
    (2 * (w : ℚ) + 2) * ε ≤ 2 * (v : ℚ) * ε := by
  apply mul_le_mul_of_nonneg_right _ hε
  have hh : (w : ℚ) + 1 ≤ v := by exact_mod_cast h
  linarith only [hh]

theorem tighten_high (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hl : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width)
    (y : Vec (Fin G.n)) (hy : AdmissibleSub (operator G) I.a I.b y P) :
    (tighten P hR lower I hB).probability (fun T => ¬TightHigh G P y T) ≤
      (2 * (volume I.b I.a : ℚ) + 2) * epsilon G.n Bmax := by
  rw [tighten]
  have he := epsilon_nonneg G.n Bmax
  have htail : 0 ≤ (2 * (volume I.b I.a : ℚ) + 1) * epsilon G.n Bmax :=
    mul_nonneg (by positivity) he
  apply le_trans (RandomTree.bind_error _ _ (TightHighRequest G P I y) _
    (ρ := epsilon G.n Bmax) (ε := (2 * (volume I.b I.a : ℚ) + 1) * epsilon G.n Bmax)
    htail (tightRequest_high G P hR lower hl I hy) ?_) (by ring_nf; rfl)
  intro r₁ hr₁
  dsimp only
  split_ifs with h₁
  · let K := I.withFloor r₁
    let u : Vec (Fin G.n) := fun i => max (y i) (r₁.val i)
    have hu : AdmissibleSub (operator G) K.a K.b u P :=
      hy.raise_floor (operator_laws G) r₁.property.1 r₁.property.2
    have hv := floor_update_volume I hB r₁ h₁
    have hp := tighten_high G P hR lower hl K hB u hu
    have hbound := (volume_error_step hv he).trans
      (show 2 * (volume I.b I.a : ℚ) * epsilon G.n Bmax ≤
        (2 * (volume I.b I.a : ℚ) + 1) * epsilon G.n Bmax by nlinarith only [he])
    apply le_trans _ (hp.trans hbound)
    rw [RandomTree.probability_map]
    apply RandomTree.probability_mono
    intro T hf hg
    obtain ⟨v, huv, hv, hc⟩ := hg
    apply hf
    exact ⟨v, (fun i => (le_max_left _ _).trans (huv i)), hv, hc⟩
  · have hyM : AdmissibleSub (operator G) I.a I.b y P.reduceM := hy
    apply le_trans (RandomTree.bind_error _ _ (fun r₂ : BoxVector I => y ≤ r₂.val) _
      (ρ := epsilon G.n Bmax) (ε := 2 * (volume I.b I.a : ℚ) * epsilon G.n Bmax)
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) he)
      (hl.ask_high G P.reduceM (P.reduceM_rank hR) I hyM) ?_) (by ring_nf; rfl)
    intro r₂ hr₂
    split_ifs with h₂
    · let K := I.withCeiling r₂
      have hu : AdmissibleSub (operator G) K.a K.b y P := hy.restrict_ceiling hr₂
      have hp := tighten_high G P hR lower hl K hB y hu
      apply le_trans _ (hp.trans (volume_error_step (ceiling_update_volume I hB r₂ h₂) he))
      rw [RandomTree.probability_map]
      exact RandomTree.probability_mono _ (fun T hf hg => hf hg)
    · have hok : TightHigh G P y (⟨I, rfl, le_refl _, le_refl _⟩ : InnerBox I) := by
        refine ⟨y, le_refl _, hy, ?_⟩
        intro hd
        by_contra hc
        exact h₁ (tightSub_forces_update G I y r₁ (hr₁ hd (le_of_not_gt hc)))
      rw [RandomTree.probability_leaf, ite_eq_right (not_not_intro hok)]
      exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) he
termination_by volume I.b I.a
decreasing_by
  · exact floor_update_volume I hB r₁ h₁
  · exact ceiling_update_volume I hB r₂ h₂

end MeanPayoff

namespace MeanPayoff
open scoped Classical

theorem tighten_low (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hl : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width)
    (z : Vec (Fin G.n)) (hz : AdmissibleSuper (operator G) I.a I.b z P) :
    (tighten P hR lower I hB).probability (fun T => ¬TightLow G P z T) ≤
      (2 * (volume I.b I.a : ℚ) + 2) * epsilon G.n Bmax := by
  rw [tighten]
  have he := epsilon_nonneg G.n Bmax
  have htail : 0 ≤ (2 * (volume I.b I.a : ℚ) + 1) * epsilon G.n Bmax :=
    mul_nonneg (by positivity) he
  have hzK : AdmissibleSuper (operator G) I.a I.b z P.reduceK := hz
  apply le_trans (RandomTree.bind_error _ _ (fun r₁ : BoxVector I => r₁.val ≤ z) _
    (ρ := epsilon G.n Bmax) (ε := (2 * (volume I.b I.a : ℚ) + 1) * epsilon G.n Bmax)
    htail (hl.ask_low G P.reduceK (P.reduceK_rank hR) I hzK) ?_) (by ring_nf; rfl)
  intro r₁ hr₁
  dsimp only
  split_ifs with h₁
  · let K := I.withFloor r₁
    have hu : AdmissibleSuper (operator G) K.a K.b z P := hz.restrict_floor hr₁
    have hp := tighten_low G P hR lower hl K hB z hu
    have hbound := (volume_error_step (floor_update_volume I hB r₁ h₁) he).trans
      (show 2 * (volume I.b I.a : ℚ) * epsilon G.n Bmax ≤
        (2 * (volume I.b I.a : ℚ) + 1) * epsilon G.n Bmax by nlinarith only [he])
    apply le_trans _ (hp.trans hbound)
    rw [RandomTree.probability_map]
    exact RandomTree.probability_mono _ (fun T hf hg => hf hg)
  · apply le_trans (RandomTree.bind_error _ _ (TightLowRequest G P I z) _
      (ρ := epsilon G.n Bmax) (ε := 2 * (volume I.b I.a : ℚ) * epsilon G.n Bmax)
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) he)
      (tightRequest_low G P hR lower hl I hz) ?_) (by ring_nf; rfl)
    intro r₂ hr₂
    split_ifs with h₂
    · let K := I.withCeiling r₂
      let u : Vec (Fin G.n) := fun i => min (z i) (r₂.val i)
      have hu : AdmissibleSuper (operator G) K.a K.b u P :=
        hz.lower_ceiling (operator_laws G) r₂.property.1 r₂.property.2
      have hp := tighten_low G P hR lower hl K hB u hu
      apply le_trans _ (hp.trans (volume_error_step (ceiling_update_volume I hB r₂ h₂) he))
      rw [RandomTree.probability_map]
      apply RandomTree.probability_mono
      intro T hf hg
      obtain ⟨v, hvu, hv, hc⟩ := hg
      apply hf
      exact ⟨v, (fun i => (hvu i).trans (min_le_left _ _)), hv, hc⟩
    · have hok : TightLow G P z (⟨I, rfl, le_refl _, le_refl _⟩ : InnerBox I) := by
        refine ⟨z, le_refl _, hz, ?_⟩
        intro hd
        by_contra hc
        exact h₂ (tightSuper_forces_update G I z r₂ (hr₂ hd (le_of_not_gt hc)))
      rw [RandomTree.probability_leaf, ite_eq_right (not_not_intro hok)]
      exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) he
termination_by volume I.b I.a
decreasing_by
  · exact floor_update_volume I hB r₁ h₁
  · exact ceiling_update_volume I hB r₂ h₂

end MeanPayoff
end

end OAI
