import OAI.Computability.MeanPayoff.Alternatives

namespace OAI

section

namespace MeanPayoff
open scoped Classical

theorem high_core_exact_half (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    {y : Vec (Fin G.n)} (hy : Subsolution (operator G) I.a I.b y) :
    highCore I y ⊆ Finset.univ.filter
      (fun i => (I.width : ℤ) ≤ 2 * ((I.exactVector G).val i - I.a i)) := by
  have hp : y ≤ (I.exactVector G).val := box_comparison G hy (basic_spec G I.a I.b I.ordered).2.1
  intro i hi
  have hic := (Finset.mem_filter.mp hi).2
  have hpi : y i ≤ (I.exactVector G).val i := hp i
  have hyi : y i ≤ I.b i := hy.1.2 i
  have hw := I.width_bound i
  have hs : (16 : ℤ) ≤ globalS Bmax := by exact_mod_cast globalS_large Bmax
  have hb : (0 : ℤ) < I.width := by exact_mod_cast I.positive
  have hd : 0 ≤ (I.width : ℤ) - (y i - I.a i) := by omega
  have hm := mul_nonneg (sub_nonneg.mpr hs) hd
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  nlinarith only [hic, hm, hb, hpi]

theorem low_core_exact_half (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    {z : Vec (Fin G.n)} (hz : Supersolution (operator G) I.a I.b z) :
    lowCore I z ⊆ (Finset.univ.filter
      (fun i => (I.width : ℤ) ≤ 2 * ((I.exactVector G).val i - I.a i)))ᶜ := by
  have hp : (I.exactVector G).val ≤ z := box_comparison G (basic_spec G I.a I.b I.ordered).1 hz
  intro i hi
  have hic := (Finset.mem_filter.mp hi).2
  have hpi : (I.exactVector G).val i ≤ z i := hp i
  have hzi : I.a i ≤ z i := hz.1.1 i
  have hw := I.width_bound i
  have hs : (16 : ℤ) ≤ globalS Bmax := by exact_mod_cast globalS_large Bmax
  have hb : (0 : ℤ) < I.width := by exact_mod_cast I.positive
  have hd : 0 ≤ (I.width : ℤ) - (I.b i - z i) := by omega
  have hm := mul_nonneg (sub_nonneg.mpr hs) hd
  simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
  nlinarith only [hic, hm, hb, hpi, hw]

theorem orientBase_high (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax)
    {y : Vec (Fin G.n)} (hy : AdmissibleSub (operator G) I.a I.b y P)
    (hc : (4 / 5) * P.k < mass P.alpha (highCore I y)) :
    HighAlternative I P y (orientBase G P I) := by
  unfold orientBase
  dsimp only
  split_ifs with h
  · exact Or.inl rfl
  · apply alternative_witness (fun i => (P.alpha_pos i).le) hc (highCore_support I y)
      ⟨_, le_of_not_gt h⟩ (by simp) (high_core_exact_half G I hy.1)

theorem orientBase_low (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax)
    {z : Vec (Fin G.n)} (hz : AdmissibleSuper (operator G) I.a I.b z P)
    (hc : (4 / 5) * P.m < mass P.beta (lowCore I z)) :
    LowAlternative I P z (orientBase G P I) := by
  unfold orientBase
  dsimp only
  split_ifs with h
  · apply alternative_witness (fun i => (P.beta_pos i).le) hc (lowCore_support I z)
      ⟨_, by rw [P.measure_compl G.positive]; linarith only [h]⟩
      (by simp) (low_core_exact_half G I hz.1)
  · exact Or.inl rfl

theorem core_nonempty {n : ℕ} {w : Fin n → ℚ} {C : Finset (Fin n)} {b : ℚ}
    (hb : 0 < b) (hc : (4 / 5) * b < mass w C) : C.Nonempty := by
  by_contra hn
  have hC : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  simp only [hC, mass, Finset.sum_empty] at hc
  linarith only [hb, hc]

theorem orient_high_support_transfer (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (P : Budgets G.n) (hB : 128 * globalS Bmax < I.width) {y : Vec (Fin G.n)}
    (hy : AdmissibleSub (operator G) I.a I.b y P) (q : BoxVector I)
    (hd : 2 * (I.E : ℤ) ≤ deviation G y q.val) {O : Orientation P}
    (h : HighAlternative (I.wideCentered hB q.val) P
      (centerSub y q.val (deviation G y q.val) I.E) O) : HighAlternative I P y O := by
  have hp := centered_subsolution (operator_laws G) hy.1 q.property
    (show (0 : ℤ) < I.E by exact_mod_cast I.E_positive hB) (le_deviation G y q.val) hd
  apply alternative_mono (fun i => (P.alpha_pos i).le) ?_ rfl (fun _ => id) h
  intro i hi
  have hi' : i ∈ subSupport (fun i => q.val i - I.E)
      (centerSub y q.val (deviation G y q.val) I.E) := (Finset.mem_filter.mp hi).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2 hi'⟩

theorem orient_low_support_transfer (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (P : Budgets G.n) (hB : 128 * globalS Bmax < I.width) {z : Vec (Fin G.n)}
    (hz : AdmissibleSuper (operator G) I.a I.b z P) (q : BoxVector I)
    (hd : 2 * (I.E : ℤ) ≤ deviation G q.val z) {O : Orientation P}
    (h : LowAlternative (I.wideCentered hB q.val) P
      (centerSuper z q.val (deviation G q.val z) I.E) O) : LowAlternative I P z O := by
  have hp := centered_supersolution (operator_laws G) hz.1 q.property
    (show (0 : ℤ) < I.E by exact_mod_cast I.E_positive hB) (le_deviation G q.val z) hd
  apply alternative_mono (fun i => (P.beta_pos i).le) ?_ rfl (fun _ => id) h
  intro i hi
  have hi' : i ∈ superSupport (fun i => q.val i + I.E)
      (centerSuper z q.val (deviation G q.val z) I.E) := (Finset.mem_filter.mp hi).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2 hi'⟩

end MeanPayoff

namespace MeanPayoff
open scoped Classical

theorem RandomTree.failure_zero {α : Type} (t : RandomTree α) {P : α → Prop}
    (h : t.All P) : t.probability (fun a => ¬P a) = 0 :=
  probability_zero_of_all t (all_mono t h (fun _ ha hna => hna ha))

theorem orientationTail_high (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width)
    {y : Vec (Fin G.n)} (hy : AdmissibleSub (operator G) I.a I.b y P)
    (hc : (4 / 5) * P.k < mass P.alpha (highCore I y))
    (qs : List (BoxVector I)) (hlen : qs.length = globalS Bmax + 1)
    (hpath : Linked (HighStep G I P y) I.midpoint qs)
    (child : BoxVector I → RandomTree (Orientation P)) {δ : ℚ} (hδ : 0 ≤ δ)
    (hchild : ∀ j, j < globalS Bmax → ¬HighBad G I P y (qs.getD j I.midpoint) →
      (child (qs.getD j I.midpoint)).probability (fun O => ¬HighAlternative I P y O) ≤ δ) :
    (orientationTail G P I qs child).probability (fun O => ¬HighAlternative I P y O) ≤
      256 / (globalS Bmax : ℚ) + δ := by
  have hn : (0 : ℚ) ≤ 256 / (globalS Bmax : ℚ) + δ :=
    add_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _)) hδ
  have hd := high_core_displacement G I P hB hy.1.1.2 hlen hpath
  unfold orientationTail
  dsimp only
  split_ifs with hH hN
  · rw [RandomTree.probability_leaf]
    split_ifs with hf
    · exact hn
    · exact (hf (Or.inl rfl)).elim
  · have hok : HighAlternative I P y
        ⟨false, [⟨(NegativeDisplacement I (qs.getD (globalS Bmax) I.midpoint))ᶜ,
          by rw [P.measure_compl G.positive]; linarith only [hN]⟩]⟩ := by
      apply alternative_witness (fun i => (P.alpha_pos i).le) hc (highCore_support I y)
        ⟨_, by rw [P.measure_compl G.positive]; linarith only [hN]⟩ (by simp) hd.1
    rw [RandomTree.probability_leaf, ite_eq_right (not_not_intro hok)]
    exact hn
  · by_cases hmore : 256 < badTimes (HighBad G I P y) qs I.midpoint (globalS Bmax)
    · rw [RandomTree.failure_zero _ ?_]
      · exact hn
      rw [RandomTree.all_bind]
      apply RandomTree.all_of_forall
      intro j
      rw [RandomTree.map, RandomTree.all_bind]
      apply RandomTree.all_of_forall
      intro O
      apply alternative_witness (fun i => (P.alpha_pos i).le) hc (highCore_support I y)
        ⟨PositiveDisplacement I (qs.getD (globalS Bmax) I.midpoint), le_of_not_gt hH⟩
        (by simp) (hd.2 hmore)
    · have hsamp : (RandomTree.uniformBelow (sampleExponent Bmax)).probability
          (fun j => ¬(j < globalS Bmax ∧ ¬HighBad G I P y (qs.getD j I.midpoint))) ≤
          256 / (globalS Bmax : ℚ) := by
        apply le_trans _ (RandomTree.sample_badTimes Bmax (HighBad G I P y) qs I.midpoint
          (Nat.le_of_not_gt hmore))
        apply RandomTree.probability_mono_all
        apply RandomTree.all_mono _ (RandomTree.uniformBelow_lt (sampleExponent Bmax))
        intro j hj hfail
        by_contra hb
        exact hfail ⟨hj, hb⟩
      apply RandomTree.bind_error _ _
        (fun j => j < globalS Bmax ∧ ¬HighBad G I P y (qs.getD j I.midpoint)) _ hδ hsamp
      intro j hj
      apply RandomTree.map_error _ _ (HighAlternative I P y) _ (hchild j hj.1 hj.2)
      intro O hO hfail
      apply hfail
      exact alternative_mono (O := O) (fun i => (P.alpha_pos i).le) (Finset.Subset.refl _)
        rfl (fun H hH => List.mem_append_left _ hH) (show Alternative _ _ _ _ O from hO)

theorem orientationTail_low (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width)
    {z : Vec (Fin G.n)} (hz : AdmissibleSuper (operator G) I.a I.b z P)
    (hc : (4 / 5) * P.m < mass P.beta (lowCore I z))
    (qs : List (BoxVector I)) (hlen : qs.length = globalS Bmax + 1)
    (hpath : Linked (LowStep G I P z) I.midpoint qs)
    (child : BoxVector I → RandomTree (Orientation P)) {δ : ℚ} (hδ : 0 ≤ δ)
    (hchild : ∀ j, j < globalS Bmax → ¬LowBad G I P z (qs.getD j I.midpoint) →
      (child (qs.getD j I.midpoint)).probability (fun O => ¬LowAlternative I P z O) ≤ δ) :
    (orientationTail G P I qs child).probability (fun O => ¬LowAlternative I P z O) ≤
      256 / (globalS Bmax : ℚ) + δ := by
  have hn : (0 : ℚ) ≤ 256 / (globalS Bmax : ℚ) + δ :=
    add_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _)) hδ
  have hd := low_core_displacement G I P hB hz.1.1.1 hlen hpath
  unfold orientationTail
  dsimp only
  split_ifs with hH hN
  · have hok : LowAlternative I P z
        ⟨true, [⟨(PositiveDisplacement I (qs.getD (globalS Bmax) I.midpoint))ᶜ,
          by rw [P.measure_compl G.positive]; linarith only [hH]⟩]⟩ := by
      apply alternative_witness (fun i => (P.beta_pos i).le) hc (lowCore_support I z)
        ⟨_, by rw [P.measure_compl G.positive]; linarith only [hH]⟩ (by simp) hd.1
    rw [RandomTree.probability_leaf, ite_eq_right (not_not_intro hok)]
    exact hn
  · rw [RandomTree.probability_leaf]
    split_ifs with hf
    · exact hn
    · exact (hf (Or.inl rfl)).elim
  · by_cases hmore : 256 < badTimes (LowBad G I P z) qs I.midpoint (globalS Bmax)
    · rw [RandomTree.failure_zero _ ?_]
      · exact hn
      rw [RandomTree.all_bind]
      apply RandomTree.all_of_forall
      intro j
      rw [RandomTree.map, RandomTree.all_bind]
      apply RandomTree.all_of_forall
      intro O
      apply alternative_witness (fun i => (P.beta_pos i).le) hc (lowCore_support I z)
        ⟨NegativeDisplacement I (qs.getD (globalS Bmax) I.midpoint), le_of_not_gt hN⟩
        (by simp) (hd.2 hmore)
    · have hsamp : (RandomTree.uniformBelow (sampleExponent Bmax)).probability
          (fun j => ¬(j < globalS Bmax ∧ ¬LowBad G I P z (qs.getD j I.midpoint))) ≤
          256 / (globalS Bmax : ℚ) := by
        apply le_trans _ (RandomTree.sample_badTimes Bmax (LowBad G I P z) qs I.midpoint
          (Nat.le_of_not_gt hmore))
        apply RandomTree.probability_mono_all
        apply RandomTree.all_mono _ (RandomTree.uniformBelow_lt (sampleExponent Bmax))
        intro j hj hfail
        by_contra hb
        exact hfail ⟨hj, hb⟩
      apply RandomTree.bind_error _ _
        (fun j => j < globalS Bmax ∧ ¬LowBad G I P z (qs.getD j I.midpoint)) _ hδ hsamp
      intro j hj
      apply RandomTree.map_error _ _ (LowAlternative I P z) _ (hchild j hj.1 hj.2)
      intro O hO hfail
      apply hfail
      exact alternative_mono (O := O) (fun i => (P.beta_pos i).le) (Finset.Subset.refl _)
        rfl (fun H hH => List.mem_append_left _ hH) (show Alternative _ _ _ _ O from hO)

end MeanPayoff

namespace MeanPayoff

def orientationError (n Bmax : ℕ) : ℚ :=
  256 / (globalS Bmax : ℚ) + 2 * globalS Bmax * epsilon n Bmax

theorem orientationError_nonneg (n Bmax : ℕ) : 0 ≤ orientationError n Bmax :=
  add_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _))
    (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (epsilon_nonneg n Bmax))

theorem clog_double_decrease {B C : ℕ} (hB : 1 < B) (hC : 2 * C ≤ B) :
    Nat.clog 2 C + 1 ≤ Nat.clog 2 B := by
  have hp := Nat.le_pow_clog (by norm_num : 1 < 2) B
  cases hk : Nat.clog 2 B with
  | zero => simp only [hk, pow_zero] at hp; omega
  | succ k =>
    rw [hk, pow_succ] at hp
    have hc : C ≤ 2 ^ k := by omega
    have hh := (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).mpr hc
    omega

theorem orientation_error_step (n Bmax : ℕ) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) :
    2 * globalS Bmax * epsilon n Bmax +
      (256 / (globalS Bmax : ℚ) + (Nat.clog 2 (2 * I.E) : ℚ) * orientationError n Bmax) ≤
      (Nat.clog 2 I.width : ℚ) * orientationError n Bmax := by
  have hs := globalS_large Bmax
  have hr := (I.radius_bounds hB).2.2.2
  have hh := clog_double_decrease (by omega : 1 < I.width) (by omega : 2 * (2 * I.E) ≤ I.width)
  have hh' : (Nat.clog 2 (2 * I.E) : ℚ) + 1 ≤ Nat.clog 2 I.width := by exact_mod_cast hh
  have hm := mul_le_mul_of_nonneg_right hh' (orientationError_nonneg n Bmax)
  calc
    _ = ((Nat.clog 2 (2 * I.E) : ℚ) + 1) * orientationError n Bmax := by
      unfold orientationError
      ring
    _ ≤ _ := hm

theorem RandomTree.failure_with_metadata {α : Type} (t : RandomTree α)
    (A B C : α → Prop) (h : t.All (fun a => A a ∧ B a)) :
    t.probability (fun a => ¬(A a ∧ B a ∧ C a)) ≤ t.probability (fun a => ¬C a) := by
  apply probability_mono_all
  exact all_mono t h (fun a hh hf hc => hf ⟨hh.1, hh.2, hc⟩)

theorem orient_high_bound (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hLower : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (y : Vec (Fin G.n))
    (hy : AdmissibleSub (operator G) I.a I.b y P)
    (hc : (4 / 5) * P.k < mass P.alpha (highCore I y)) :
    (orient G P hR lower I).probability (fun O => ¬HighAlternative I P y O) ≤
      (Nat.clog 2 I.width : ℚ) * orientationError G.n Bmax := by
  induction I using (measure (fun I : SolveBox G.n Bmax => I.width)).wf.induction generalizing y with
  | h I ih =>
      by_cases hsmall : I.width ≤ 128 * globalS Bmax
      · rw [orient, dite_eq_left hsmall, RandomTree.probability_leaf, ite_eq_right (not_not_intro (orientBase_high G P I hy hc))]
        exact mul_nonneg (Nat.cast_nonneg _) (orientationError_nonneg _ _)
      · have hB : 128 * globalS Bmax < I.width := Nat.lt_of_not_ge hsmall
        rw [orient, dite_eq_right hsmall]
        dsimp only
        have hcore := core_nonempty P.k_pos hc
        have hp : (centerSteps P hR lower I hB (globalS Bmax) I.midpoint).probability
            (fun qs => ¬(qs.length = globalS Bmax + 1 ∧ Linked (Moving I) I.midpoint qs ∧
              Linked (HighStep G I P y) I.midpoint qs)) ≤ 2 * globalS Bmax * epsilon G.n Bmax := by
          apply le_trans _ (centerSteps_high G P hR lower hLower I hB hy hcore)
          with_reducible
            exact RandomTree.failure_with_metadata
              (centerSteps P hR lower I hB (globalS Bmax) I.midpoint)
              (fun qs => qs.length = globalS Bmax + 1)
              (Linked (Moving I) I.midpoint) (Linked (HighStep G I P y) I.midpoint)
              (centerSteps_metadata P hR lower I hB (globalS Bmax) I.midpoint)
        let δ := (Nat.clog 2 (2 * I.E) : ℚ) * orientationError G.n Bmax
        have hδ : 0 ≤ δ := mul_nonneg (Nat.cast_nonneg _) (orientationError_nonneg _ _)
        apply le_trans (RandomTree.bind_error
          (centerSteps P hR lower I hB (globalS Bmax) I.midpoint)
          (fun qs => orientationTail G P I qs (fun q => orient G P hR lower (I.wideCentered hB q.val)))
          (fun qs => qs.length = globalS Bmax + 1 ∧ Linked (Moving I) I.midpoint qs ∧
            Linked (HighStep G I P y) I.midpoint qs) (fun O => ¬HighAlternative I P y O)
          (ε := 256 / (globalS Bmax : ℚ) + δ)
          (add_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _)) hδ) hp ?_)
          (orientation_error_step G.n Bmax I hB)
        intro qs hqs
        apply orientationTail_high G P I hB hy hc qs hqs.1 hqs.2.2 _ hδ
        intro j hj hbad
        let q := qs.getD j I.midpoint
        have hq : CenterDrift I (globalS Bmax) q :=
          centerDrift_mono I hj.le (linked_drift I hqs.2.1 (by omega))
        have hd := high_center_deviation G I hB hy.1.1.2 hcore hq
        let K := I.wideCentered hB q.val
        let u := centerSub y q.val (deviation G y q.val) I.E
        have hu : AdmissibleSub (operator G) K.a K.b u P :=
          centered_admissible_high G I P hy q I.E (I.E_positive hB) (I.E_smaller.le.trans I.bounded) hd
        have huc : (4 / 5) * P.k < mass P.alpha (highCore K u) :=
          (lt_of_not_ge hbad).trans_le (mass_mono (fun i => (P.alpha_pos i).le)
            (nearHigh_child_core G I hB y q))
        apply le_trans _ (ih K (by exact I.E_smaller) u hu huc)
        exact RandomTree.probability_mono _ (fun O hf hu => hf
          (orient_high_support_transfer G I P hB hy q hd hu))

theorem orient_low_bound (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hLower : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (z : Vec (Fin G.n))
    (hz : AdmissibleSuper (operator G) I.a I.b z P)
    (hc : (4 / 5) * P.m < mass P.beta (lowCore I z)) :
    (orient G P hR lower I).probability (fun O => ¬LowAlternative I P z O) ≤
      (Nat.clog 2 I.width : ℚ) * orientationError G.n Bmax := by
  induction I using (measure (fun I : SolveBox G.n Bmax => I.width)).wf.induction generalizing z with
  | h I ih =>
      by_cases hsmall : I.width ≤ 128 * globalS Bmax
      · rw [orient, dite_eq_left hsmall, RandomTree.probability_leaf, ite_eq_right (not_not_intro (orientBase_low G P I hz hc))]
        exact mul_nonneg (Nat.cast_nonneg _) (orientationError_nonneg _ _)
      · have hB : 128 * globalS Bmax < I.width := Nat.lt_of_not_ge hsmall
        rw [orient, dite_eq_right hsmall]
        dsimp only
        have hcore := core_nonempty P.m_pos hc
        have hp : (centerSteps P hR lower I hB (globalS Bmax) I.midpoint).probability
            (fun qs => ¬(qs.length = globalS Bmax + 1 ∧ Linked (Moving I) I.midpoint qs ∧
              Linked (LowStep G I P z) I.midpoint qs)) ≤ 2 * globalS Bmax * epsilon G.n Bmax := by
          apply le_trans _ (centerSteps_low G P hR lower hLower I hB hz hcore)
          with_reducible
            exact RandomTree.failure_with_metadata
              (centerSteps P hR lower I hB (globalS Bmax) I.midpoint)
              (fun qs => qs.length = globalS Bmax + 1)
              (Linked (Moving I) I.midpoint) (Linked (LowStep G I P z) I.midpoint)
              (centerSteps_metadata P hR lower I hB (globalS Bmax) I.midpoint)
        let δ := (Nat.clog 2 (2 * I.E) : ℚ) * orientationError G.n Bmax
        have hδ : 0 ≤ δ := mul_nonneg (Nat.cast_nonneg _) (orientationError_nonneg _ _)
        apply le_trans (RandomTree.bind_error
          (centerSteps P hR lower I hB (globalS Bmax) I.midpoint)
          (fun qs => orientationTail G P I qs (fun q => orient G P hR lower (I.wideCentered hB q.val)))
          (fun qs => qs.length = globalS Bmax + 1 ∧ Linked (Moving I) I.midpoint qs ∧
            Linked (LowStep G I P z) I.midpoint qs) (fun O => ¬LowAlternative I P z O)
          (ε := 256 / (globalS Bmax : ℚ) + δ)
          (add_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _)) hδ) hp ?_)
          (orientation_error_step G.n Bmax I hB)
        intro qs hqs
        apply orientationTail_low G P I hB hz hc qs hqs.1 hqs.2.2 _ hδ
        intro j hj hbad
        let q := qs.getD j I.midpoint
        have hq : CenterDrift I (globalS Bmax) q :=
          centerDrift_mono I hj.le (linked_drift I hqs.2.1 (by omega))
        have hd := low_center_deviation G I hB hz.1.1.1 hcore hq
        let K := I.wideCentered hB q.val
        let u := centerSuper z q.val (deviation G q.val z) I.E
        have hu : AdmissibleSuper (operator G) K.a K.b u P :=
          centered_admissible_low G I P hz q I.E (I.E_positive hB) (I.E_smaller.le.trans I.bounded) hd
        have huc : (4 / 5) * P.m < mass P.beta (lowCore K u) :=
          (lt_of_not_ge hbad).trans_le (mass_mono (fun i => (P.beta_pos i).le)
            (nearLow_child_core G I hB z q))
        apply le_trans _ (ih K (by exact I.E_smaller) u hu huc)
        exact RandomTree.probability_mono _ (fun O hf hu => hf
          (orient_low_support_transfer G I P hB hz q hd hu))

end MeanPayoff
end

end OAI
