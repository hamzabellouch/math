import Mathlib

namespace OAI

namespace MetricKMedianRecovery.Population
variable {V : Type*} [PseudoMetricSpace V]

noncomputable def ball (D : Finset V) (w : V) (q : ℝ) : Finset V :=
  D.filter (fun p => dist w p ≤ q)

lemma ball_mono (D : Finset V) (w : V) {q r : ℝ} (h : q ≤ r) :
    ball D w q ⊆ ball D w r := by
  intro p hp
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2.trans h⟩

lemma ball_nonempty_at (D : Finset V) (w : V) {p : V} (hp : p ∈ D) :
    (ball D w (dist w p)).Nonempty := ⟨p, Finset.mem_filter.mpr ⟨hp, le_rfl⟩⟩

noncomputable def candidate (D : Finset V) (P : ℝ) (m : ℕ) (w p : V) : ℝ :=
  max (dist w p) (P / ((m : ℝ) * (ball D w (dist w p)).card))

noncomputable def radius (D : Finset V) (hn : D.Nonempty)
    (P : ℝ) (m : ℕ) (w : V) : ℝ := D.inf' hn (candidate D P m w)

lemma candidate_pos (D : Finset V) (P : ℝ) (m : ℕ) (w : V)
    (hP : 0 < P) (hm : 0 < m) {p : V} (hp : p ∈ D) : 0 < candidate D P m w p := by
  have hc : (0 : ℝ) < (ball D w (dist w p)).card := by
    exact_mod_cast Finset.card_pos.mpr (ball_nonempty_at D w hp)
  exact (div_pos hP (mul_pos (Nat.cast_pos.mpr hm) hc)).trans_le (le_max_right _ _)

lemma radius_pos (D : Finset V) (hn : D.Nonempty) (P : ℝ) (m : ℕ) (w : V)
    (hP : 0 < P) (hm : 0 < m) : 0 < radius D hn P m w := by
  obtain ⟨p, hp, he⟩ := Finset.exists_mem_eq_inf' hn (candidate D P m w)
  rw [radius, he]
  exact candidate_pos D P m w hP hm hp

lemma candidate_feasible (D : Finset V) (P : ℝ) (m : ℕ) (w : V)
    (hP : 0 < P) (hm : 0 < m) {p : V} (hp : p ∈ D) :
    P / m ≤ candidate D P m w p * (ball D w (candidate D P m w p)).card := by
  let C := ball D w (dist w p)
  have hc : (0 : ℝ) < C.card := by
    exact_mod_cast Finset.card_pos.mpr (ball_nonempty_at D w hp)
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hlo : P / ((m : ℝ)*C.card) ≤ candidate D P m w p := le_max_right _ _
  have hsub : C ⊆ ball D w (candidate D P m w p) := ball_mono D w (le_max_left _ _)
  have hh : (C.card : ℝ) ≤ (ball D w (candidate D P m w p)).card := by
    exact_mod_cast Finset.card_le_card hsub
  have he : P / ((m : ℝ)*C.card) * C.card = P / m := by field_simp
  rw [← he]
  exact (mul_le_mul_of_nonneg_right hlo hc.le).trans
    (mul_le_mul_of_nonneg_left hh (candidate_pos D P m w hP hm hp).le)

lemma radius_feasible (D : Finset V) (hn : D.Nonempty) (P : ℝ) (m : ℕ) (w : V)
    (hP : 0 < P) (hm : 0 < m) :
    P / m ≤ radius D hn P m w * (ball D w (radius D hn P m w)).card := by
  obtain ⟨p, hp, he⟩ := Finset.exists_mem_eq_inf' hn (candidate D P m w)
  simpa only [radius, he] using candidate_feasible D P m w hP hm hp

lemma radius_minimal (D : Finset V) (hn : D.Nonempty) (P : ℝ) (m : ℕ) (w : V)
    (hP : 0 < P) (hm : 0 < m) {q : ℝ} (_hq : 0 ≤ q)
    (hpop : P / m ≤ q * (ball D w q).card) : radius D hn P m w ≤ q := by
  have hpos : (0 : ℝ) < P / m := div_pos hP (Nat.cast_pos.mpr hm)
  have hc : (0 : ℝ) < (ball D w q).card := by
    by_contra hh
    have he : ((ball D w q).card : ℝ) = 0 := le_antisymm (le_of_not_gt hh) (Nat.cast_nonneg _)
    rw [he, mul_zero] at hpop
    linarith
  have hne : (ball D w q).Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hc)
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image (ball D w q) (dist w) hne
  have hpeq : ball D w (dist w p) = ball D w q := by
    apply Finset.Subset.antisymm (ball_mono D w (Finset.mem_filter.mp hp).2)
    intro x hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, hmax x hx⟩
  have hdiv : P / ((m : ℝ)*(ball D w q).card) ≤ q := by
    apply (div_le_iff₀ (mul_pos (Nat.cast_pos.mpr hm) hc)).mpr
    have hh := (div_le_iff₀ (Nat.cast_pos.mpr hm)).mp hpop
    nlinarith
  apply (Finset.inf'_le (candidate D P m w) (Finset.mem_filter.mp hp).1).trans
  exact max_le (Finset.mem_filter.mp hp).2 (by simpa only [hpeq] using hdiv)

lemma radius_isLeast (D : Finset V) (hn : D.Nonempty) (P : ℝ) (m : ℕ) (w : V)
    (hP : 0 < P) (hm : 0 < m) :
    IsLeast {q : ℝ | 0 ≤ q ∧ P/m ≤ q * (ball D w q).card} (radius D hn P m w) := by
  exact ⟨⟨(radius_pos D hn P m w hP hm).le, radius_feasible D hn P m w hP hm⟩,
    fun q hq => radius_minimal D hn P m w hP hm hq.1 hq.2⟩

omit [PseudoMetricSpace V] in

lemma sublevel_card [DecidableEq V] (C : Finset V) (f : V → ℝ) (hf : ∀ p ∈ C, 0 ≤ f p)
    (mean a : ℝ) (hmean : ∑ p ∈ C, f p = mean * C.card) (ha : 0 < a) :
    (1-1/a) * (C.card : ℝ) ≤ ((C.filter (fun p => f p ≤ a*mean)).card : ℝ) := by
  classical
  let N := C.filter (fun p => f p ≤ a*mean)
  by_cases hm : mean = 0
  · have hzero : ∀ p ∈ C, f p = 0 := by
      have hs : ∑ p ∈ C, f p = 0 := by simpa only [hm, zero_mul] using hmean
      exact (Finset.sum_eq_zero_iff_of_nonneg hf).mp hs
    have hN : N = C := by
      apply Finset.filter_eq_self.mpr
      intro p hp
      simp [hzero p hp, hm]
    change (1-1/a)*(C.card : ℝ) ≤ (N.card : ℝ)
    rw [hN]
    nlinarith [mul_nonneg (one_div_pos.mpr ha).le (Nat.cast_nonneg (α := ℝ) C.card)]
  · by_cases hn : C.Nonempty
    · have hc : (0 : ℝ) < C.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hn)
      have hmn : 0 < mean := by
        have hs : 0 ≤ mean * C.card := hmean ▸ Finset.sum_nonneg hf
        exact lt_of_le_of_ne (nonneg_of_mul_nonneg_left hs hc) (Ne.symm hm)
      have hh : (a*mean) * ((C \ N).card : ℝ) ≤ ∑ p ∈ C \ N, f p := by
        calc
          _ = ∑ _p ∈ C \ N, a*mean := by simp [mul_comm]
          _ ≤ _ := Finset.sum_le_sum (fun p hp => by
            have hnp := (Finset.mem_sdiff.mp hp).2
            have hpC := (Finset.mem_sdiff.mp hp).1
            exact (lt_of_not_ge (fun h => hnp (Finset.mem_filter.mpr ⟨hpC,h⟩))).le)
      have hs : (∑ p ∈ C \ N, f p) ≤ mean * C.card := by
        rw [← hmean]
        exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun p hp _ => hf p hp)
      have hcard := Finset.card_sdiff_add_card_eq_card (show N ⊆ C from Finset.filter_subset _ _)
      have hcard' : ((C \ N).card : ℝ) + (N.card : ℝ) = C.card := by exact_mod_cast hcard
      change (1-1/a)*(C.card : ℝ) ≤ (N.card : ℝ)
      have hmc : a*((C \ N).card : ℝ) ≤ C.card := by
        nlinarith [hh.trans hs]
      apply (mul_le_mul_iff_right₀ ha).mp
      field_simp
      nlinarith
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.card_empty, Nat.cast_zero, mul_zero,
        Finset.filter_empty, le_refl]

lemma leader_radius_le [DecidableEq V] (D C : Finset V) (hn : D.Nonempty)
    (hC : C.Nonempty) (hCD : C ⊆ D) (P : ℝ) (m : ℕ) (w o : V)
    (mean a : ℝ) (hP : 0 < P) (hm : 0 < m) (ha : 0 ≤ a)
    (hmean : ∑ p ∈ C, dist p o = mean * C.card)
    (hnear : dist w o ≤ a * mean) :
    radius D hn P m w ≤ (a+2)*mean + 2*P/((m : ℝ)*C.card) := by
  classical
  have hc : (0 : ℝ) < C.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hC)
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hm0 : 0 ≤ mean := by
    have hh : 0 ≤ mean*C.card := hmean ▸ Finset.sum_nonneg (fun _ _ => dist_nonneg)
    exact nonneg_of_mul_nonneg_left hh hc
  let Q := (a+2)*mean + 2*P/((m : ℝ)*C.card)
  let N := C.filter (fun p => dist p o ≤ 2*mean)
  have hQ : 0 ≤ Q := add_nonneg (mul_nonneg (by linarith) hm0)
    (div_nonneg (by positivity) (mul_pos hm' hc).le)
  have hN : (C.card : ℝ)/2 ≤ N.card := by
    have hh := sublevel_card C (fun p => dist p o) (fun _ _ => dist_nonneg)
      mean 2 hmean (by norm_num)
    norm_num at hh
    linarith
  have hsub : N ⊆ ball D w Q := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨hCD hp'.1, ?_⟩
    have ht := dist_triangle w o p
    rw [dist_comm o p] at ht
    have hnterm : 0 ≤ 2*P/((m : ℝ)*C.card) := div_nonneg (by positivity) (mul_pos hm' hc).le
    dsimp [Q]
    nlinarith [hp'.2]
  have hcard : (C.card : ℝ)/2 ≤ (ball D w Q).card := hN.trans (by
    exact_mod_cast Finset.card_le_card hsub)
  apply radius_minimal D hn P m w hP hm hQ
  calc
    P/(m : ℝ) = (2*P/((m : ℝ)*C.card)) * ((C.card : ℝ)/2) := by field_simp
    _ ≤ Q * ((C.card : ℝ)/2) := mul_le_mul_of_nonneg_right
      (by dsimp [Q]; nlinarith [mul_nonneg (show 0 ≤ a+2 by linarith) hm0]) (by positivity)
    _ ≤ Q * (ball D w Q).card := mul_le_mul_of_nonneg_left hcard hQ

lemma third_balls_disjoint (D : Finset V) (wa wb : V) (qa qb ra rb R kappa : ℝ)
    (hqa : 0 < qa) (hqb : 0 < qb) (_hk0 : 0 ≤ kappa) (hk1 : kappa ≤ 1)
    (ha : 10*qa < ra) (hb : 10*qb < rb)
    (hlip : ra ≤ dist wa wb + rb) (hR : R ≤ (1+kappa)*ra+kappa*qa)
    (hfar : 10*rb < dist wb wa + R) :
    Disjoint (ball D wa qa) (ball D wb qb) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hp' := (Finset.mem_filter.mp hp).2
  have hq' := (Finset.mem_filter.mp hq).2
  have ht := dist_triangle wa p wb
  rw [dist_comm p wb] at ht
  have hd : dist wa wb ≤ qa+qb := by linarith
  have hra : 0 < ra := by linarith
  have hR' : R ≤ 2*ra+qa := by
    have h₁ := mul_le_mul_of_nonneg_right hk1 hra.le
    have h₂ := mul_le_mul_of_nonneg_right hk1 hqa.le
    nlinarith
  rw [dist_comm wb wa] at hfar
  nlinarith

omit [PseudoMetricSpace V] in

lemma disjoint_population_budget {I : Type*} [DecidableEq V]
    (D : Finset V) (A : Finset I) (C : I → Finset V) (q r : I → ℝ)
    (cost : V → ℝ) (P : ℝ) (m : ℕ) (hP : 0 < P) (hm : 0 < m)
    (hcost : ∀ p ∈ D, 0 ≤ cost p) (hPsum : ∑ p ∈ D, cost p = P)
    (hC : ∀ i ∈ A, C i ⊆ D) (hdis : Set.PairwiseDisjoint (↑A) C)
    (hq : ∀ i ∈ A, 0 < q i) (hr : ∀ i ∈ A, 0 ≤ r i)
    (hpop : ∀ i ∈ A, P/(m : ℝ) ≤ q i * (C i).card)
    (hcharge : ∀ i ∈ A, ∀ p ∈ C i, (9/10 : ℝ)*r i ≤ cost p) :
    ∑ i ∈ A, r i / q i ≤ (10/9 : ℝ)*m := by
  classical
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hsub : A.biUnion C ⊆ D := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp
    exact hC i hi hpi
  have htotal : (∑ i ∈ A, (9/10 : ℝ)*r i*(C i).card) ≤ P := by
    calc
      _ = ∑ i ∈ A, ∑ _p ∈ C i, (9/10 : ℝ)*r i := by simp [mul_comm]
      _ ≤ ∑ i ∈ A, ∑ p ∈ C i, cost p := by
        exact Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (hcharge i hi))
      _ = ∑ p ∈ A.biUnion C, cost p := (Finset.sum_biUnion hdis).symm
      _ ≤ ∑ p ∈ D, cost p := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun p hp _ => hcost p hp)
      _ = P := hPsum
  have hpoint : ∀ i ∈ A, (9/10 : ℝ)*(P/m)*(r i/q i) ≤ (9/10 : ℝ)*r i*(C i).card := by
    intro i hi
    have hh := mul_le_mul_of_nonneg_right (hpop i hi)
      (show 0 ≤ (9/10 : ℝ)*r i/q i from div_nonneg (mul_nonneg (by norm_num) (hr i hi)) (hq i hi).le)
    have he : q i*(C i).card*((9/10 : ℝ)*r i/q i) = (9/10 : ℝ)*r i*(C i).card := by
      field_simp [ne_of_gt (hq i hi)]
    rw [he] at hh
    calc
      _ = P/m*((9/10 : ℝ)*r i/q i) := by ring
      _ ≤ _ := hh
  have hs := (Finset.sum_le_sum hpoint).trans htotal
  rw [← Finset.mul_sum] at hs
  have he : (9/10 : ℝ)*(P/m)*((10/9 : ℝ)*m) = P := by field_simp
  have hs' : (9/10 : ℝ)*(P/m)*(∑ i ∈ A, r i/q i) ≤
      (9/10 : ℝ)*(P/m)*((10/9 : ℝ)*m) := hs.trans_eq he.symm
  exact (mul_le_mul_iff_right₀ (mul_pos (by norm_num : (0 : ℝ)<9/10) (div_pos hP hm'))).mp hs'

omit [PseudoMetricSpace V] in

lemma ceiling_index_budget {I : Type*} (A : Finset I) (q r : I → ℝ)
    (kappa : ℝ) (m : ℕ) (hk : 0 < kappa) (hA : A.card ≤ m)
    (hq : ∀ i ∈ A, 0 < q i) (hr : ∀ i ∈ A, 0 ≤ r i)
    (hbudget : ∑ i ∈ A, r i/q i ≤ (10/9 : ℝ)*m) :
    (∑ i ∈ A, (Nat.ceil (r i/(kappa*q i)) : ℝ)) ≤ (10/(9*kappa)+1)*m := by
  have hpoint : ∀ i ∈ A, (Nat.ceil (r i/(kappa*q i)) : ℝ) ≤ (r i/q i)/kappa+1 := by
    intro i hi
    have hh := Nat.ceil_lt_add_one_of_gt_neg_one
      (show (-1 : ℝ) < r i/(kappa*q i) by
        have := div_nonneg (hr i hi) (mul_pos hk (hq i hi)).le
        linarith)
    have he : r i/(kappa*q i) = (r i/q i)/kappa := by ring
    rw [he] at hh ⊢
    exact hh.le
  have hs := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  rw [← Finset.sum_div] at hs
  have hb := div_le_div_of_nonneg_right hbudget hk.le
  have hc : (A.card : ℝ) ≤ m := by exact_mod_cast hA
  calc
    _ ≤ (∑ i ∈ A, r i/q i)/kappa + (A.card : ℝ) := hs
    _ ≤ ((10/9 : ℝ)*m)/kappa + m := add_le_add hb hc
    _ = _ := by ring

end MetricKMedianRecovery.Population

end OAI
