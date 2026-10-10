import OAI.Computability.MeanPayoff.Deviation

namespace OAI

section

namespace MeanPayoff

def epsilon (n Bmax : ℕ) : ℚ := (1 / 2) ^ globalJ n Bmax

theorem epsilon_nonneg (n Bmax : ℕ) : 0 ≤ epsilon n Bmax :=
  pow_nonneg (by norm_num) _

def HighStep (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax) (P : Budgets G.n)
    (y : Vec (Fin G.n)) (q q' : BoxVector I) : Prop :=
  deviation G y q'.val ≤ deviation G y q.val ∧
  (mass P.alpha (nearHigh G y q.val I.D) ≤ (4 / 5) * P.k →
    deviation G y q'.val ≤ deviation G y q.val - I.D)

def LowStep (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax) (P : Budgets G.n)
    (z : Vec (Fin G.n)) (q q' : BoxVector I) : Prop :=
  deviation G q'.val z ≤ deviation G q.val z ∧
  (mass P.beta (nearLow G z q.val I.D) ≤ (4 / 5) * P.m →
    deviation G q'.val z ≤ deviation G q.val z - I.D)

theorem centerUpdate_movement {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (q : BoxVector I) :
    (centerUpdate P hR lower I hB q).All
      (fun q' => ∀ i, |q'.val i - q.val i| ≤ (I.D : ℤ)) := by
  unfold centerUpdate
  rw [RandomTree.all_bind]
  apply RandomTree.all_of_forall
  intro r₁
  rw [RandomTree.map, RandomTree.all_bind]
  apply RandomTree.all_of_forall
  intro r₂ i
  exact I.average_movement q (Int.natCast_nonneg _) r₁.property r₂.property i

theorem centerUpdate_high (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hLower : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width)
    {y : Vec (Fin G.n)} (hy : AdmissibleSub (operator G) I.a I.b y P)
    (q : BoxVector I) (hd : 2 * (I.D : ℤ) ≤ deviation G y q.val) :
    (centerUpdate P hR lower I hB q).probability (fun q' => ¬HighStep G I P y q q') ≤
      2 * epsilon G.n Bmax := by
  let K := I.narrowCentered hB q.val
  let u := centerSub y q.val (deviation G y q.val) I.D
  let bad := mass P.alpha (nearHigh G y q.val I.D) ≤ (4 / 5) * P.k
  have hu : AdmissibleSub (operator G) K.a K.b u P :=
    centered_admissible_high G I P hy q I.D (I.D_positive hB) (I.D_small.trans I.bounded) hd
  have hu₂ : AdmissibleSub (operator G) K.a K.b u P.reduceM := hu
  have hu₁ (hb : bad) : AdmissibleSub (operator G) K.a K.b u P.reduceK := by
    refine ⟨hu.1, ?_⟩
    change mass P.alpha (lowerActive (fun i => q.val i - I.D) u) ≤ (4 / 5) * P.k
    rw [show u = centerSub y q.val (deviation G y q.val) I.D from rfl, centered_active_high]
    exact hb
  have hh₂ := K.repeated_lower _ ((hLower P.reduceM (P.reduceM_rank hR)).1 K u hu₂)
    (globalJ_positive G.n Bmax)
  have hh₁ : (K.repeated (lower P.reduceK (P.reduceK_rank hR) K) (globalJ G.n Bmax)).probability
      (fun r => ¬(bad → u ≤ r.val)) ≤ epsilon G.n Bmax := by
    by_cases hb : bad
    · simpa only [hb, true_implies, epsilon] using
        K.repeated_lower _ ((hLower P.reduceK (P.reduceK_rank hR)).1 K u (hu₁ hb))
          (globalJ_positive G.n Bmax)
    · rw [RandomTree.probability_zero_of_all _
        (RandomTree.all_of_forall _ (fun r => by simp [hb]))]
      exact epsilon_nonneg _ _
  change ((_ : RandomTree (BoxVector K)).bind _).probability _ ≤ _
  apply le_trans (RandomTree.bind_error _ _ (fun r₁ => bad → u ≤ r₁.val) _
    (epsilon_nonneg _ _) hh₁ ?_) (by change epsilon G.n Bmax + epsilon G.n Bmax ≤ 2 * epsilon G.n Bmax; linarith)
  intro r₁ hr₁
  apply RandomTree.map_error _ _ (fun r₂ => u ≤ r₂.val) _ hh₂
  intro r₂ hr₂ hfail
  apply hfail
  constructor
  · apply deviation_le
    exact high_deviation_step hy.1.1.2 (by exact_mod_cast I.D_positive hB) hd
      (le_deviation G y q.val) r₁.property.1 hr₂
  · intro hb
    apply deviation_le
    exact high_bad_step hy.1.1.2 (by exact_mod_cast I.D_positive hB) hd (hr₁ hb) hr₂

theorem centerUpdate_low_deterministic (G : Game) {Bmax : ℕ}
    (P : Budgets G.n) (I : SolveBox G.n Bmax)
    (hB : 128 * globalS Bmax < I.width) {z : Vec (Fin G.n)}
    (hz : I.a ≤ z) (q : BoxVector I)
    (hd : 2 * (I.D : ℤ) ≤ deviation G q.val z)
    (r₁ r₂ : BoxVector (I.narrowCentered hB q.val))
    (hr₁ : r₁.val ≤ centerSuper z q.val (deviation G q.val z) I.D)
    (hr₂ : mass P.beta (nearLow G z q.val I.D) ≤ (4 / 5) * P.m →
      r₂.val ≤ centerSuper z q.val (deviation G q.val z) I.D) :
    LowStep G I P z q (I.averageClipped r₁.val r₂.val) := by
  have hD : (0 : ℤ) < I.D := by exact_mod_cast I.D_positive hB
  constructor
  · apply deviation_le
    exact low_deviation_step hz hD hd (le_deviation G q.val z) hr₁ r₂.property.2
  · intro hb
    apply deviation_le
    exact low_bad_step hz hD hd hr₁ (hr₂ hb)

theorem RandomTree.pair_error {α β γ : Type} (t₁ : RandomTree α) (t₂ : RandomTree β)
    (f : α → β → γ) (good₁ : α → Prop) (good₂ : β → Prop) (bad : γ → Prop)
    {ε : ℚ} (hε : 0 ≤ ε) (h₁ : t₁.probability (fun a => ¬good₁ a) ≤ ε)
    (h₂ : t₂.probability (fun b => ¬good₂ b) ≤ ε)
    (hf : ∀ a b, good₁ a → good₂ b → ¬bad (f a b)) :
    (t₁.bind fun a => t₂.map (f a)).probability bad ≤ 2 * ε := by
  apply le_trans (RandomTree.bind_error t₁ (fun a => t₂.map (f a)) good₁ bad hε h₁ ?_)
    (by exact le_of_eq (by ring))
  intro a ha
  exact RandomTree.map_error t₂ (f a) good₂ bad h₂ (fun b hb => hf a b ha hb)

theorem average_low_error (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width)
    {z : Vec (Fin G.n)} (hz : I.a ≤ z) (q : BoxVector I)
    (hd : 2 * (I.D : ℤ) ≤ deviation G q.val z)
    (t₁ t₂ : RandomTree (BoxVector (I.narrowCentered hB q.val))) {ε : ℚ} (hε : 0 ≤ ε)
    (h₁ : t₁.probability (fun r => ¬r.val ≤ centerSuper z q.val (deviation G q.val z) I.D) ≤ ε)
    (h₂ : t₂.probability (fun r => ¬(mass P.beta (nearLow G z q.val I.D) ≤ (4 / 5) * P.m →
      r.val ≤ centerSuper z q.val (deviation G q.val z) I.D)) ≤ ε) :
    (t₁.bind fun r₁ => t₂.map fun r₂ => I.averageClipped r₁.val r₂.val).probability
      (fun q' => ¬LowStep G I P z q q') ≤ 2 * ε := by
  apply RandomTree.pair_error t₁ t₂ (fun r₁ r₂ => I.averageClipped r₁.val r₂.val)
    (fun r₁ => r₁.val ≤ centerSuper z q.val (deviation G q.val z) I.D)
    (fun r₂ => mass P.beta (nearLow G z q.val I.D) ≤ (4 / 5) * P.m →
      r₂.val ≤ centerSuper z q.val (deviation G q.val z) I.D)
    (fun q' => ¬LowStep G I P z q q') hε h₁ h₂
  intro r₁ r₂ hr₁ hr₂ hfail
  exact hfail (centerUpdate_low_deterministic G P I hB hz q hd r₁ r₂ hr₁ hr₂)

theorem centerUpdate_low (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hLower : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width)
    {z : Vec (Fin G.n)} (hz : AdmissibleSuper (operator G) I.a I.b z P)
    (q : BoxVector I) (hd : 2 * (I.D : ℤ) ≤ deviation G q.val z) :
    (centerUpdate P hR lower I hB q).probability (fun q' => ¬LowStep G I P z q q') ≤
      2 * epsilon G.n Bmax := by
  let K := I.narrowCentered hB q.val
  let u := centerSuper z q.val (deviation G q.val z) I.D
  let bad := mass P.beta (nearLow G z q.val I.D) ≤ (4 / 5) * P.m
  have hu : AdmissibleSuper (operator G) K.a K.b u P :=
    centered_admissible_low G I P hz q I.D (I.D_positive hB) (I.D_small.trans I.bounded) hd
  have hu₁ : AdmissibleSuper (operator G) K.a K.b u P.reduceK := hu
  have hu₂ (hb : bad) : AdmissibleSuper (operator G) K.a K.b u P.reduceM := by
    refine ⟨hu.1, ?_⟩
    change mass P.beta (upperActive (fun i => q.val i + I.D) u) ≤ (4 / 5) * P.m
    rw [show u = centerSuper z q.val (deviation G q.val z) I.D from rfl, centered_active_low]
    exact hb
  have hh₁ := K.repeated_upper _ ((hLower P.reduceK (P.reduceK_rank hR)).2 K u hu₁)
    (globalJ_positive G.n Bmax)
  have hh₂ : (K.repeated (lower P.reduceM (P.reduceM_rank hR) K) (globalJ G.n Bmax)).probability
      (fun r => ¬(bad → r.val ≤ u)) ≤ epsilon G.n Bmax := by
    by_cases hb : bad
    · simpa only [hb, true_implies, epsilon] using
        K.repeated_upper _ ((hLower P.reduceM (P.reduceM_rank hR)).2 K u (hu₂ hb))
          (globalJ_positive G.n Bmax)
    · rw [RandomTree.probability_zero_of_all _
        (RandomTree.all_of_forall _ (fun r => by simp [hb]))]
      exact epsilon_nonneg _ _
  exact average_low_error G P I hB hz.1.1.1 q hd _ _ (epsilon_nonneg _ _) hh₁ hh₂



def Linked {α : Type} (R : α → α → Prop) (q : α) (qs : List α) : Prop :=
  qs.head? = some q ∧ qs.IsChain R

theorem linked_single {α : Type} (R : α → α → Prop) (q : α) : Linked R q [q] := by
  simp [Linked]

theorem linked_cons {α : Type} {R : α → α → Prop} {q q' : α} {qs : List α}
    (h : R q q') (hs : Linked R q' qs) : Linked R q (q :: qs) := by
  refine ⟨rfl, hs.2.cons ?_⟩
  intro r hr
  rw [hs.1] at hr
  have : q' = r := Option.mem_some_iff.mp hr
  simpa [← this] using h

def CenterDrift {n Bmax : ℕ} (I : SolveBox n Bmax) (r : ℕ) (q : BoxVector I) : Prop :=
  ∀ i, |q.val i - I.midpoint.val i| ≤ (r : ℤ) * I.D

theorem centerDrift_start {n Bmax : ℕ} (I : SolveBox n Bmax) : CenterDrift I 0 I.midpoint := by
  intro i
  simp

theorem centerDrift_mono {n Bmax : ℕ} (I : SolveBox n Bmax) {r s : ℕ} (hrs : r ≤ s)
    {q : BoxVector I} (h : CenterDrift I r q) : CenterDrift I s q := by
  intro i
  exact (h i).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hrs) (Int.natCast_nonneg _))

theorem centerDrift_move {n Bmax : ℕ} (I : SolveBox n Bmax) {r : ℕ} {q q' : BoxVector I}
    (h : CenterDrift I r q) (hmove : ∀ i, |q'.val i - q.val i| ≤ (I.D : ℤ)) :
    CenterDrift I (r + 1) q' := by
  intro i
  have hh := (abs_add_le (q'.val i - q.val i) (q.val i - I.midpoint.val i)).trans
    (add_le_add (hmove i) (h i))
  rw [show q'.val i - q.val i + (q.val i - I.midpoint.val i) =
      q'.val i - I.midpoint.val i by ring] at hh
  exact hh.trans_eq (by push_cast; ring)

theorem centerSteps_length {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (t : ℕ) (q : BoxVector I) :
    (centerSteps P hR lower I hB t q).All (fun qs => qs.length = t + 1) := by
  induction t generalizing q with
  | zero => rfl
  | succ t ht =>
    rw [centerSteps, RandomTree.all_bind]
    apply RandomTree.all_of_forall
    intro q'
    rw [RandomTree.map, RandomTree.all_bind]
    exact RandomTree.all_mono _ (ht q') (fun qs hqs => by simpa [RandomTree.All] using hqs)

theorem centerSteps_relation {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (R : BoxVector I → BoxVector I → Prop)
    {δ : ℚ} (hδ : 0 ≤ δ)
    (hstep : ∀ r q, r ≤ globalS Bmax → CenterDrift I r q →
      (centerUpdate P hR lower I hB q).probability (fun q' => ¬R q q') ≤ δ)
    (t r : ℕ) (q : BoxVector I) (hrt : r + t ≤ globalS Bmax) (hq : CenterDrift I r q) :
    (centerSteps P hR lower I hB t q).probability (fun qs => ¬Linked R q qs) ≤ t * δ := by
  induction t generalizing r q with
  | zero => simp [centerSteps, linked_single]
  | succ t ht =>
    have hm : (centerUpdate P hR lower I hB q).All (CenterDrift I (r + 1)) :=
      RandomTree.all_mono _ (centerUpdate_movement P hR lower I hB q)
        (fun q' hh => centerDrift_move I hq hh)
    have hp : (centerUpdate P hR lower I hB q).probability
        (fun q' => ¬ (R q q' ∧ CenterDrift I (r + 1) q')) ≤ δ := by
      apply le_trans _ (hstep r q (by omega) hq)
      apply RandomTree.probability_mono_all
      exact RandomTree.all_mono _ hm (fun q' hh hf hr => hf ⟨hr, hh⟩)
    rw [centerSteps]
    apply le_trans (RandomTree.bind_error _ _
      (fun q' => R q q' ∧ CenterDrift I (r + 1) q') _
      (mul_nonneg (Nat.cast_nonneg _) hδ) hp ?_) (by push_cast; ring_nf; rfl)
    intro q' hq'
    apply RandomTree.map_error _ _ (Linked R q') _
      (ht (r + 1) q' (by omega) hq'.2)
    intro qs hqs hf
    exact hf (linked_cons hq'.1 hqs)

theorem centerSteps_high (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hLower : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width)
    {y : Vec (Fin G.n)} (hy : AdmissibleSub (operator G) I.a I.b y P)
    (hc : (highCore I y).Nonempty) :
    (centerSteps P hR lower I hB (globalS Bmax) I.midpoint).probability
      (fun qs => ¬Linked (HighStep G I P y) I.midpoint qs) ≤
      2 * globalS Bmax * epsilon G.n Bmax := by
  have hh := centerSteps_relation P hR lower I hB (HighStep G I P y)
    (mul_nonneg (by norm_num : (0 : ℚ) ≤ 2) (epsilon_nonneg G.n Bmax)) ?_
    (globalS Bmax) 0 I.midpoint (by omega) (centerDrift_start I)
  · convert hh using 1 ; ring
  intro r q hr hq
  apply centerUpdate_high G P hR lower hLower I hB hy q
  have hd := high_center_deviation G I hB hy.1.1.2 hc (centerDrift_mono I hr hq)
  have hde : I.D ≤ I.E := by
    have hs : 1 ≤ globalS Bmax := (show 1 ≤ 16 by omega).trans (globalS_large Bmax)
    exact (Nat.le_mul_of_pos_left _ (by omega)).trans (I.radius_bounds hB).2.1
  have hde' : (I.D : ℤ) ≤ I.E := by exact_mod_cast hde
  omega

theorem centerSteps_low (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hLower : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width)
    {z : Vec (Fin G.n)} (hz : AdmissibleSuper (operator G) I.a I.b z P)
    (hc : (lowCore I z).Nonempty) :
    (centerSteps P hR lower I hB (globalS Bmax) I.midpoint).probability
      (fun qs => ¬Linked (LowStep G I P z) I.midpoint qs) ≤
      2 * globalS Bmax * epsilon G.n Bmax := by
  have hh := centerSteps_relation P hR lower I hB (LowStep G I P z)
    (mul_nonneg (by norm_num : (0 : ℚ) ≤ 2) (epsilon_nonneg G.n Bmax)) ?_
    (globalS Bmax) 0 I.midpoint (by omega) (centerDrift_start I)
  · convert hh using 1 ; ring
  intro r q hr hq
  apply centerUpdate_low G P hR lower hLower I hB hz q
  have hd := low_center_deviation G I hB hz.1.1.1 hc (centerDrift_mono I hr hq)
  have hde : I.D ≤ I.E := by
    have hs : 1 ≤ globalS Bmax := (show 1 ≤ 16 by omega).trans (globalS_large Bmax)
    exact (Nat.le_mul_of_pos_left _ (by omega)).trans (I.radius_bounds hB).2.1
  have hde' : (I.D : ℤ) ≤ I.E := by exact_mod_cast hde
  omega

end MeanPayoff
end

end OAI
