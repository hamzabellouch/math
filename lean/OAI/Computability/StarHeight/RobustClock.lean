import OAI.Computability.StarHeight.TagPartitions

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uP uA uA2 uC uC2 uC3 uC4 uC5
universe uι uP2 uP3 uP4 uC6 uC7 uC8 uC9
universe uT uA3 uB uC10 uT2 uA4 uB2 uC11
universe uA5 uB3 uC12 uT3 uA6 uB4 uC13 uT4
universe uA7 uB5 uC14 uT5 uA8 uB6 uC15 uT6
universe uA9 uB7 uC16 uT7 uA10 uB8 uC17 uA11
universe uB9 uA12 uB10 uC18 uA13 uB11 uP5 uC19
universe uT8 uP6 uC20 uT9 uP7 uT10 uP8 uT11
universe uP9 uC21

namespace RobustClock

variable {P : Type uP} [DecidableEq P]

def vertices : List (P × P) → Finset P
  | [] => ∅
  | e :: es => insert e.1 (insert e.2 (vertices es))

def FreshPairs : List (P × P) → Prop
  | [] => True
  | e :: es => e.1 ≠ e.2 ∧ (e.1 ∉ vertices es ∨ e.2 ∉ vertices es) ∧ FreshPairs es

lemma mem_vertices {es : List (P × P)} {e : P × P} (he : e ∈ es) :
    e.1 ∈ vertices es ∧ e.2 ∈ vertices es := by
  induction es with
  | nil => simp at he
  | cons a es ih =>
      rcases List.mem_cons.mp he with rfl | he
      · simp [vertices]
      · obtain ⟨h1, h2⟩ := ih he
        simp [vertices, h1, h2]

lemma card_vertices (es : List (P × P)) : (vertices es).card ≤ 2 * es.length := by
  induction es with
  | nil => simp [vertices]
  | cons e es ih =>
      have h1 := Finset.card_insert_le e.1 (insert e.2 (vertices es))
      have h2 := Finset.card_insert_le e.2 (vertices es)
      simp only [vertices, List.length_cons]
      omega

lemma FreshPairs.nodup {es : List (P × P)} (h : FreshPairs es) : es.Nodup := by
  induction es with
  | nil => exact List.nodup_nil
  | cons e es ih =>
      refine List.nodup_cons.mpr ⟨?_, ih h.2.2⟩
      intro he
      obtain ⟨h1, h2⟩ := mem_vertices he
      exact h.2.1.elim (fun hn => hn h1) (fun hn => hn h2)

lemma FreshPairs.realize {A : Type uA} [AddCommGroup A]
    {es : List (P × P)} (h : FreshPairs es) (d : P × P → A) :
    ∃ v : P → A, ∀ e ∈ es, v e.2 - v e.1 = d e := by
  classical
  induction es with
  | nil => exact ⟨fun _ => 0, by simp⟩
  | cons e es ih =>
      obtain ⟨v, hv⟩ := ih h.2.2
      rcases h.2.1 with hnew | hnew
      · refine ⟨Function.update v e.1 (v e.2 - d e), ?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · simp only [Function.update_self, Function.update_of_ne h.1.symm]
          abel
        · obtain ⟨ha1, ha2⟩ := mem_vertices ha
          have hn1 : a.1 ≠ e.1 := fun hh => hnew (hh ▸ ha1)
          have hn2 : a.2 ≠ e.1 := fun hh => hnew (hh ▸ ha2)
          simp only [Function.update_of_ne hn1, Function.update_of_ne hn2]
          exact hv a ha
      · refine ⟨Function.update v e.2 (v e.1 + d e), ?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · simp only [Function.update_self, Function.update_of_ne h.1]
          abel
        · obtain ⟨ha1, ha2⟩ := mem_vertices ha
          have hn1 : a.1 ≠ e.2 := fun hh => hnew (hh ▸ ha1)
          have hn2 : a.2 ≠ e.2 := fun hh => hnew (hh ▸ ha2)
          simp only [Function.update_of_ne hn1, Function.update_of_ne hn2]
          exact hv a ha

lemma realize_sequence {A : Type uA2} [AddCommGroup A] {F : ℕ} (f : Fin F → P × P)
    (hf : FreshPairs (List.ofFn f)) (d : Fin F → A) :
    ∃ v : P → A, ∀ j, v (f j).2 - v (f j).1 = d j := by
  classical
  have hinj : Function.Injective f := List.nodup_ofFn.mp hf.nodup
  obtain ⟨v, hv⟩ := hf.realize (Function.extend f d (fun _ => 0))
  refine ⟨v, fun j => ?_⟩
  simpa only [hinj.extend_apply] using hv (f j) (List.mem_ofFn.mpr ⟨j, rfl⟩)

lemma extract_forest (B : Finset (P × P)) (hB : ∀ e ∈ B, e.1 ≠ e.2)
    (F : ℕ) (hcard : 4 * F ^ 2 < B.card) :
    ∃ f : Fin F → P × P, FreshPairs (List.ofFn f) ∧ ∀ j, f j ∈ B := by
  have build : ∀ n ≤ F, ∃ es : List (P × P), es.length = n ∧ FreshPairs es ∧
      ∀ e ∈ es, e ∈ B := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨[], rfl, trivial, by simp⟩
    | succ n ih =>
        intro hn
        obtain ⟨es, hlen, hf, he⟩ := ih (by omega)
        have hverts : (vertices es).card ≤ 2 * F := by
          have hc := card_vertices es
          rw [hlen] at hc
          omega
        have hnot : ¬B ⊆ (vertices es) ×ˢ (vertices es) := by
          intro hsub
          have hc := Finset.card_le_card hsub
          rw [Finset.card_product] at hc
          have hm := Nat.mul_le_mul hverts hverts
          nlinarith
        obtain ⟨e, heB, heout⟩ := Finset.not_subset.mp hnot
        have heFresh : e.1 ∉ vertices es ∨ e.2 ∉ vertices es := by
          simpa only [Finset.mem_product, not_and_or] using heout
        refine ⟨e :: es, by simp [hlen], ⟨hB e heB, heFresh, hf⟩, ?_⟩
        intro a ha
        exact (List.mem_cons.mp ha).elim (fun h => h ▸ heB) (he a)
  obtain ⟨es, hlen, hf, he⟩ := build F le_rfl
  subst F
  exact ⟨es.get, by simpa only [List.ofFn_get] using hf,
    fun j => he (es.get j) (List.get_mem es j)⟩

lemma count_of_no_forest (B : Finset (P × P)) (hB : ∀ e ∈ B, e.1 ≠ e.2)
    (F : ℕ) (hn : ∀ f : Fin F → P × P, FreshPairs (List.ofFn f) →
      ∃ j, f j ∉ B) : B.card ≤ 4 * F ^ 2 := by
  by_contra h
  obtain ⟨f, hf, hm⟩ := extract_forest B hB F (Nat.lt_of_not_ge h)
  obtain ⟨j, hj⟩ := hn f hf
  exact hj (hm j)

abbrev Circle := UnitAddCircle

@[simp] lemma coe_integer (k : ℤ) : (((k : ℝ) : Circle)) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨k, by simp⟩

lemma representative (a : Circle) : ∃ r : ℝ, (r : Circle) = a ∧ |r| = ‖a‖ := by
  obtain ⟨x⟩ := a
  change ∃ r : ℝ, (r : Circle) = (x : Circle) ∧ |r| = ‖(x : Circle)‖
  refine ⟨x - round x, ?_, ?_⟩
  · rw [AddCircle.coe_sub, coe_integer, sub_zero]
  · simpa using (AddCircle.norm_eq (1 : ℝ) (x := x)).symm

lemma norm_coe_le_abs (r : ℝ) : ‖(r : Circle)‖ ≤ |r| :=
  QuotientAddGroup.norm_mk_le_norm

lemma coe_mod_fraction (n : ℕ) (hn : 0 < n) (k : ℤ) :
    ((((k % (n : ℤ) : ℤ) : ℝ) / n : ℝ) : Circle) = (((k : ℝ) / n : ℝ) : Circle) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hc : ((k % (n : ℤ) : ℤ) : ℝ) + (n : ℝ) * ((k / (n : ℤ) : ℤ) : ℝ) = k := by
    exact_mod_cast Int.emod_add_mul_ediv k (n : ℤ)
  have hh : ((k % (n : ℤ) : ℤ) : ℝ) / n = (k : ℝ) / n - ((k / (n : ℤ) : ℤ) : ℝ) := by
    apply (div_eq_iff hnR).mpr
    rw [sub_mul, div_mul_cancel₀ _ hnR]
    linarith
  rw [hh, AddCircle.coe_sub, coe_integer, sub_zero]

lemma grid_near (n : ℕ) (hn : 0 < n) (a : Circle) :
    ∃ j : Fin n, ‖a + (((j : ℝ) / n : ℝ) : Circle)‖ ≤ 1 / (2 * n) := by
  obtain ⟨r, rfl, _⟩ := representative a
  let k : ℤ := -round ((n : ℝ) * r)
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 := Int.emod_nonneg k hnZ.ne'
  let j : Fin n := ⟨(k % (n : ℤ)).toNat,
    (Int.toNat_lt hk0).mpr (Int.emod_lt_of_pos k hnZ)⟩
  have hj : (j : ℝ) = ((k % (n : ℤ) : ℤ) : ℝ) := by
    change (((k % (n : ℤ)).toNat : ℕ) : ℝ) = _
    exact_mod_cast Int.toNat_of_nonneg hk0
  refine ⟨j, ?_⟩
  rw [hj, coe_mod_fraction n hn, ← AddCircle.coe_add]
  apply (norm_coe_le_abs _).trans
  have hh : r + (k : ℝ) / n = ((n : ℝ) * r - round ((n : ℝ) * r)) / n := by
    dsimp [k]
    push_cast
    field_simp
    ring
  rw [hh, abs_div, abs_of_pos hnR]
  calc
    |(n : ℝ) * r - round ((n : ℝ) * r)| / n ≤ (1 / 2 : ℝ) / n :=
      div_le_div_of_nonneg_right (abs_sub_round _) hnR.le
    _ = 1 / (2 * n) := by ring

def Near (C : Set Circle) (r : ℝ) : Set Circle :=
  {x | ∃ c ∈ C, dist x c ≤ r}

def centersI : Set Circle := {((0 : ℝ) : Circle), ((1 / 6 : ℝ) : Circle),
  ((3 / 6 : ℝ) : Circle)}

def centersJ : Set Circle := {((2 / 6 : ℝ) : Circle), ((4 / 6 : ℝ) : Circle),
  ((5 / 6 : ℝ) : Circle)}

lemma center_separation {c d : Circle} (hc : c ∈ centersI) (hd : d ∈ centersJ) :
    1 / 6 ≤ dist c d := by
  simp only [centersI, centersJ, Set.mem_insert_iff, Set.mem_singleton_iff] at hc hd
  rcases hc with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl <;>
    norm_num [dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq]

lemma center_sums (j : Fin 6) : ∃ c ∈ centersI, ∃ d ∈ centersJ,
    c + d = (((j : ℝ) / 6 : ℝ) : Circle) := by
  fin_cases j
  · refine ⟨((1 / 6 : ℝ) : Circle), by simp [centersI],
      ((5 / 6 : ℝ) : Circle), by simp [centersJ], ?_⟩
    norm_num [← AddCircle.coe_add]
  · refine ⟨((3 / 6 : ℝ) : Circle), by simp [centersI],
      ((4 / 6 : ℝ) : Circle), by simp [centersJ], ?_⟩
    rw [← AddCircle.coe_add]
    have he : (3 / 6 + 4 / 6 : ℝ) = 1 / 6 + 1 := by ring
    rw [he, AddCircle.coe_add_period]
    norm_num
  · exact ⟨((0 : ℝ) : Circle), by simp [centersI],
      ((2 / 6 : ℝ) : Circle), by simp [centersJ], by simp⟩
  · refine ⟨((1 / 6 : ℝ) : Circle), by simp [centersI],
      ((2 / 6 : ℝ) : Circle), by simp [centersJ], ?_⟩
    norm_num [← AddCircle.coe_add]
  · exact ⟨((0 : ℝ) : Circle), by simp [centersI],
      ((4 / 6 : ℝ) : Circle), by simp [centersJ], by simp⟩
  · exact ⟨((0 : ℝ) : Circle), by simp [centersI],
      ((5 / 6 : ℝ) : Circle), by simp [centersJ], by simp⟩

lemma type_one_difference {i j : Circle}
    (hi : i ∈ Near centersI (1 / 16)) (hj : j ∈ Near centersJ (1 / 16)) :
    1 / 24 ≤ ‖i - j‖ := by
  obtain ⟨c, hc, hic⟩ := hi
  obtain ⟨d, hd, hjd⟩ := hj
  have hsep := center_separation hc hd
  have ht := dist_triangle4 c i j d
  rw [dist_comm c i, dist_eq_norm i j] at ht
  linarith

lemma type_one_interior (z : Circle) :
    ∃ i j : Circle, i + j = z ∧ ∀ h : Circle, ‖h‖ ≤ 1 / 96 →
      i + h ∈ Near centersI (1 / 16) ∧ j - h ∈ Near centersJ (1 / 16) := by
  obtain ⟨k, hk⟩ := grid_near 6 (by omega) (-z)
  obtain ⟨c, hc, d, hd, hsum⟩ := center_sums k
  have herr : ‖z - (c + d)‖ ≤ 1 / 12 := by
    rw [hsum, ← norm_neg, neg_sub, sub_eq_add_neg]
    simpa only [Nat.cast_ofNat, show (1 : ℝ) / (2 * 6) = 1 / 12 by norm_num, add_comm] using hk
  obtain ⟨δ, hδ, hnorm⟩ := representative (z - (c + d))
  let t : Circle := ((δ / 2 : ℝ) : Circle)
  have ht : ‖t‖ ≤ 1 / 24 := by
    apply (norm_coe_le_abs _).trans
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), hnorm]
    linarith
  refine ⟨c + t, d + t, ?_, ?_⟩
  · have htt : t + t = z - (c + d) := by
      dsimp [t]
      rw [← AddCircle.coe_add, show δ / 2 + δ / 2 = δ by ring, hδ]
    calc
      c + t + (d + t) = c + d + (t + t) := by abel
      _ = z := by rw [htt]; abel
  · intro h hh
    constructor
    · refine ⟨c, hc, ?_⟩
      have hnorm := norm_add_le t h
      have he : c + t + h - c = t + h := by abel
      rw [dist_eq_norm, he]
      linarith
    · refine ⟨d, hd, ?_⟩
      have hnorm := norm_sub_le t h
      have he : d + t - h - d = t - h := by abel
      rw [dist_eq_norm, he]
      linarith

noncomputable def smallCoords {C : Type uC} [Fintype C] (x : C → Circle) (r : ℝ) : Finset C := by
  classical
  exact Finset.univ.filter (fun c => ‖x c‖ ≤ r)

lemma mem_smallCoords {C : Type uC2} [Fintype C] (x : C → Circle) (r : ℝ) (c : C) :
    c ∈ smallCoords x r ↔ ‖x c‖ ≤ r := by
  classical
  simp [smallCoords]

def TypeTwo {C : Type uC3} [Fintype C] (s : ℕ) : Set (C → Circle) :=
  {x | s + 1 ≤ (smallCoords x (1 / 100)).card}

lemma type_two_difference {C : Type uC4} [Fintype C] (s : ℕ)
    (hC : Fintype.card C = 2 * s + 1) {i j : C → Circle}
    (hi : i ∈ TypeTwo s) (hj : j ∈ TypeTwo s) :
    ∃ c, ‖i c - j c‖ ≤ 2 / 100 := by
  classical
  have hc : (Finset.univ : Finset C).card <
      (smallCoords i (1 / 100)).card + (smallCoords j (1 / 100)).card := by
    change s + 1 ≤ _ at hi hj
    simp only [Finset.card_univ, hC]
    omega
  obtain ⟨c, hc'⟩ := Finset.inter_nonempty_of_card_lt_card_add_card
    (Finset.subset_univ _) (Finset.subset_univ _) hc
  obtain ⟨hci, hcj⟩ := Finset.mem_inter.mp hc'
  have hic := (mem_smallCoords _ _ _).mp hci
  have hjc := (mem_smallCoords _ _ _).mp hcj
  refine ⟨c, ?_⟩
  have hh := norm_sub_le (i c) (j c)
  linarith

lemma type_two_interior {C : Type uC5} [Fintype C] (s : ℕ)
    (hC : Fintype.card C = 2 * s + 1) (z : C → Circle)
    (hz : ∃ c, ‖z c‖ ≤ 1 / 200) :
    ∃ i j : C → Circle, i + j = z ∧ ∀ h : C → Circle,
      (∀ c, ‖h c‖ ≤ 1 / 400) → i + h ∈ TypeTwo s ∧ j - h ∈ TypeTwo s := by
  classical
  obtain ⟨c₀, hc₀⟩ := hz
  have hcard : s ≤ ((Finset.univ : Finset C).erase c₀).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hC]
    omega
  obtain ⟨A, hA, hAc⟩ := Finset.exists_subset_card_eq hcard
  have hcA : c₀ ∉ A := fun hm => (Finset.mem_erase.mp (hA hm)).1 rfl
  let i : C → Circle := fun c => if c ∈ A then 0 else z c
  let j : C → Circle := z - i
  refine ⟨i, j, ?_, ?_⟩
  · dsimp [j]
    abel
  · intro h hh
    constructor
    · change s + 1 ≤ (smallCoords (i + h) (1 / 100)).card
      have hsub : insert c₀ A ⊆ smallCoords (i + h) (1 / 100) := by
        intro c hc
        apply (mem_smallCoords _ _ _).mpr
        rcases Finset.mem_insert.mp hc with hcc | hc
        · subst c
          have hnorm := norm_add_le (z c₀) (h c₀)
          change ‖i c₀ + h c₀‖ ≤ _
          simp only [i, hcA, ite_false]
          linarith [hh c₀]
        · change ‖i c + h c‖ ≤ _
          simp only [i, hc, ite_true, zero_add]
          linarith [hh c]
      have hle := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hcA, hAc] at hle
      exact hle
    · change s + 1 ≤ (smallCoords (j - h) (1 / 100)).card
      have hsub : Aᶜ ⊆ smallCoords (j - h) (1 / 100) := by
        intro c hc
        have hc' := Finset.mem_compl.mp hc
        apply (mem_smallCoords _ _ _).mpr
        change ‖z c - i c - h c‖ ≤ _
        simp only [i, hc', ite_false, sub_self, zero_sub, norm_neg]
        linarith [hh c]
      have hle := Finset.card_le_card hsub
      rw [Finset.card_compl, hC, hAc] at hle
      omega

def FirstI (ε : ℝ) (side : Bool) : Set Circle :=
  if side then {i | 4 * ε ≤ ‖i‖} else {i | ‖i‖ ≤ ε}

def FirstJ (ε : ℝ) (side : Bool) : Set Circle :=
  if side then {j | ‖j‖ ≤ ε} else {j | 4 * ε ≤ ‖j‖}

lemma first_left_right {ε : ℝ} {i j : Circle}
    (hi : i ∈ FirstI ε false) (hj : j ∈ FirstJ ε true) : ‖i + j‖ ≤ 2 * ε := by
  change ‖i‖ ≤ ε at hi
  change ‖j‖ ≤ ε at hj
  linarith [norm_add_le i j]

lemma first_same_side {ε : ℝ} (side : Bool) {i j : Circle}
    (hi : i ∈ FirstI ε side) (hj : j ∈ FirstJ ε side) : 3 * ε ≤ ‖i + j‖ := by
  cases side
  · change ‖i‖ ≤ ε at hi
    change 4 * ε ≤ ‖j‖ at hj
    have h := norm_sub_le_norm_add j i
    rw [add_comm j i] at h
    linarith
  · change 4 * ε ≤ ‖i‖ at hi
    change ‖j‖ ≤ ε at hj
    linarith [norm_sub_le_norm_add i j]

lemma first_interior {ε : ℝ} (hε : 0 < ε) (side : Bool) (z : Circle)
    (hz : 6 * ε < ‖z‖) : ∃ i j : Circle, i + j = z ∧
      ∀ h : Circle, ‖h‖ ≤ ε / 2 → i + h ∈ FirstI ε side ∧ j - h ∈ FirstJ ε side := by
  cases side
  · refine ⟨0, z, zero_add _, ?_⟩
    intro h hh
    change ‖0 + h‖ ≤ ε ∧ 4 * ε ≤ ‖z - h‖
    simp only [zero_add]
    constructor
    · linarith
    · linarith [norm_sub_norm_le z h]
  · refine ⟨z, 0, add_zero _, ?_⟩
    intro h hh
    change 4 * ε ≤ ‖z + h‖ ∧ ‖0 - h‖ ≤ ε
    simp only [zero_sub, norm_neg]
    constructor
    · linarith [norm_sub_le_norm_add z h]
    · linarith

lemma pow_two_half {a b : ℕ} (h : a < b) :
    2 * (2 : ℝ) ^ a ≤ (2 : ℝ) ^ b := by
  rw [mul_comm, ← pow_succ]
  exact pow_le_pow_right₀ (by norm_num) h

lemma pow_two_pos_diff_inj {a b c d : ℕ} (hab : a < b) (hcd : c < d)
    (h : (2 : ℝ) ^ b - 2 ^ a = 2 ^ d - 2 ^ c) : a = c ∧ b = d := by
  have hbd : b = d := by
    rcases lt_trichotomy b d with hbd | hbd | hbd
    · have h1 := pow_two_half hbd
      have h2 := pow_two_half hcd
      have h3 := pow_pos (by norm_num : (0 : ℝ) < 2) a
      linarith
    · exact hbd
    · have h1 := pow_two_half hbd
      have h2 := pow_two_half hab
      have h3 := pow_pos (by norm_num : (0 : ℝ) < 2) c
      linarith
  have hac : (2 : ℝ) ^ a = 2 ^ c := by rw [hbd] at h; linarith
  refine ⟨?_, hbd⟩
  exact (pow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)) hac

lemma pow_two_diff_ne_zero {a b : ℕ} (hab : a ≠ b) :
    (2 : ℝ) ^ b - 2 ^ a ≠ 0 := by
  intro h
  exact hab ((pow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)) (sub_eq_zero.mp h)).symm

lemma pow_two_diff_inj {a b c d : ℕ} (hab : a ≠ b) (_hcd : c ≠ d)
    (h : (2 : ℝ) ^ b - 2 ^ a = 2 ^ d - 2 ^ c) : a = c ∧ b = d := by
  rcases lt_or_gt_of_ne hab with hab | hab
  · have hp : (2 : ℝ) ^ a < 2 ^ b := pow_lt_pow_right₀ (by norm_num) hab
    have hcd' : c < d := by
      by_contra hn
      have hle := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_of_not_gt hn)
      linarith
    exact pow_two_pos_diff_inj hab hcd' h
  · have hp : (2 : ℝ) ^ b < 2 ^ a := pow_lt_pow_right₀ (by norm_num) hab
    have hcd' : d < c := by
      by_contra hn
      have hle := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_of_not_gt hn)
      linarith
    have he : (2 : ℝ) ^ a - 2 ^ b = 2 ^ c - 2 ^ d := by linarith
    obtain ⟨hbd, hac⟩ := pow_two_pos_diff_inj hab hcd' he
    exact ⟨hac, hbd⟩

noncomputable def realRoster [Fintype P] (p : P) : ℝ :=
  (2 : ℝ) ^ (Fintype.equivFin P p).val / (16 * 2 ^ Fintype.card P)

omit [DecidableEq P] in
lemma realRoster_range [Fintype P] (p : P) : 0 < realRoster p ∧ realRoster p < 1 / 16 := by
  have hd : (0 : ℝ) < 16 * 2 ^ Fintype.card P := by positivity
  constructor
  · exact div_pos (by positivity) hd
  · rw [realRoster, div_lt_iff₀ hd]
    have hh := pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) (Fintype.equivFin P p).isLt
    nlinarith

omit [DecidableEq P] in
lemma realRoster_diff_ne_zero [Fintype P] {p q : P} (hpq : p ≠ q) :
    realRoster q - realRoster p ≠ 0 := by
  have hindex : (Fintype.equivFin P p).val ≠ (Fintype.equivFin P q).val := by
    intro h
    exact hpq ((Fintype.equivFin P).injective (Fin.ext h))
  have hraw := pow_two_diff_ne_zero hindex
  dsimp [realRoster]
  rw [← sub_div]
  exact div_ne_zero hraw (by positivity)

omit [DecidableEq P] in
lemma realRoster_diff_inj [Fintype P] {p q r s : P} (hpq : p ≠ q) (hrs : r ≠ s)
    (h : realRoster q - realRoster p = realRoster s - realRoster r) : p = r ∧ q = s := by
  have hindex {p q : P} (hpq : p ≠ q) :
      (Fintype.equivFin P p).val ≠ (Fintype.equivFin P q).val := by
    intro h
    exact hpq ((Fintype.equivFin P).injective (Fin.ext h))
  dsimp [realRoster] at h
  rw [← sub_div, ← sub_div, div_left_inj' (by positivity : (16 * (2 : ℝ) ^ Fintype.card P) ≠ 0)] at h
  obtain ⟨ha, hb⟩ := pow_two_diff_inj (hindex hpq) (hindex hrs) h
  exact ⟨(Fintype.equivFin P).injective (Fin.ext ha), (Fintype.equivFin P).injective (Fin.ext hb)⟩

noncomputable def firstRoster [Fintype P] (p : P) : Circle := (realRoster p : Circle)

omit [DecidableEq P] in
lemma realRoster_diff_range [Fintype P] (p q : P) :
    realRoster q - realRoster p ∈ Set.Ico (-(1 / 8 : ℝ)) (-(1 / 8 : ℝ) + 1) := by
  have hp := realRoster_range p
  have hq := realRoster_range q
  constructor <;> linarith

omit [DecidableEq P] in
lemma firstRoster_diff_ne_zero [Fintype P] {p q : P} (hpq : p ≠ q) :
    firstRoster q - firstRoster p ≠ 0 := by
  intro h
  have he : ((realRoster q - realRoster p : ℝ) : Circle) = ((0 : ℝ) : Circle) := by
    simpa only [AddCircle.coe_sub, AddCircle.coe_zero, firstRoster] using h
  have hz : (0 : ℝ) ∈ Set.Ico (-(1 / 8 : ℝ)) (-(1 / 8 : ℝ) + 1) := by constructor <;> norm_num
  have hr := (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ))
    (realRoster_diff_range p q) hz).mp he
  exact realRoster_diff_ne_zero hpq hr

omit [DecidableEq P] in
lemma firstRoster_diff_inj [Fintype P] {p q r s : P} (hpq : p ≠ q) (hrs : r ≠ s)
    (h : firstRoster q - firstRoster p = firstRoster s - firstRoster r) : p = r ∧ q = s := by
  have he : ((realRoster q - realRoster p : ℝ) : Circle) =
      ((realRoster s - realRoster r : ℝ) : Circle) := by
    simpa only [AddCircle.coe_sub, firstRoster] using h
  exact realRoster_diff_inj hpq hrs ((AddCircle.coe_eq_coe_iff_of_mem_Ico
    (p := (1 : ℝ)) (realRoster_diff_range p q) (realRoster_diff_range r s)).mp he)

lemma finite_positive_lower {ι : Type uι} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ r : ℝ, 0 < r ∧ ∀ i, r < f i := by
  classical
  have aux (J : Finset ι) : ∃ r : ℝ, 0 < r ∧ ∀ i ∈ J, r < f i := by
    induction J using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i J hi ih =>
        obtain ⟨r, hr, hri⟩ := ih
        refine ⟨min r (f i / 2), lt_min hr (by linarith [hf i]), ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          exact (min_le_right _ _).trans_lt (by linarith [hf i])
        · exact (min_le_left _ _).trans_lt (hri j hj)
  obtain ⟨r, hr, hri⟩ := aux Finset.univ
  exact ⟨r, hr, fun i => hri i (Finset.mem_univ _)⟩

def OffPair (P : Type uP2) := {e : P × P // e.1 ≠ e.2}

noncomputable instance [Fintype P] : Fintype (OffPair P) := by
  classical
  unfold OffPair
  infer_instance

omit [DecidableEq P] in
lemma firstRoster_parameters [Fintype P] :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 100 ∧
      (∀ p q : P, p ≠ q → 16 * ε < ‖firstRoster q - firstRoster p‖) ∧
      (∀ p q r s : P, p ≠ q → r ≠ s → (p, q) ≠ (r, s) →
        16 * ε < ‖(firstRoster q - firstRoster p) - (firstRoster s - firstRoster r)‖) := by
  classical
  let d (e : OffPair P) : Circle := firstRoster e.1.2 - firstRoster e.1.1
  have hd (e : OffPair P) : 0 < ‖d e‖ := norm_pos_iff.mpr (firstRoster_diff_ne_zero e.2)
  obtain ⟨δ, hδ, hδd⟩ := finite_positive_lower (fun e => ‖d e‖) hd
  have hdd (es : {es : OffPair P × OffPair P // es.1 ≠ es.2}) :
      0 < ‖d es.1.1 - d es.1.2‖ := by
    apply norm_pos_iff.mpr
    intro h
    obtain ⟨ha, hb⟩ := firstRoster_diff_inj es.1.1.2 es.1.2.2 (sub_eq_zero.mp h)
    exact es.2 (Subtype.ext (Prod.ext ha hb))
  obtain ⟨δ', hδ', hδd'⟩ := finite_positive_lower
    (fun es : {es : OffPair P × OffPair P // es.1 ≠ es.2} => ‖d es.1.1 - d es.1.2‖) hdd
  let ε := min (1 / 200 : ℝ) (min δ δ') / 32
  have hε : 0 < ε := div_pos (lt_min (by norm_num) (lt_min hδ hδ')) (by norm_num)
  have hε0 : ε ≤ 1 / 200 / 32 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hεδ : 32 * ε ≤ δ := by
    have hh := (min_le_right (1 / 200 : ℝ) (min δ δ')).trans (min_le_left δ δ')
    dsimp [ε]
    linarith
  have hεδ' : 32 * ε ≤ δ' := by
    have hh := (min_le_right (1 / 200 : ℝ) (min δ δ')).trans (min_le_right δ δ')
    dsimp [ε]
    linarith
  refine ⟨ε, hε, by linarith, ?_, ?_⟩
  · intro p q hpq
    have hh := hδd ⟨(p, q), hpq⟩
    change δ < ‖firstRoster q - firstRoster p‖ at hh
    linarith
  · intro p q r s hpq hrs hne
    have he : (⟨(p, q), hpq⟩ : OffPair P) ≠ ⟨(r, s), hrs⟩ :=
      fun h => hne (congrArg Subtype.val h)
    have hh := hδd' ⟨(⟨(p, q), hpq⟩, ⟨(r, s), hrs⟩), he⟩
    change δ' < ‖(firstRoster q - firstRoster p) - (firstRoster s - firstRoster r)‖ at hh
    linarith

lemma norm_difference_perturb (p q p' q' : Circle) :
    ‖(q' - p') - (q - p)‖ ≤ ‖q' - q‖ + ‖p' - p‖ := by
  convert norm_sub_le (q' - q) (p' - p) using 1
  congr 1
  abel

omit [DecidableEq P] in
lemma first_roster_separation {ε η : ℝ} (hε : 0 < ε) (hη : η ≤ ε / 2)
    (v v' : P → Circle) (hv' : ∀ p, ‖v' p - v p‖ < η)
    {p q r s : P} (hsep : 16 * ε < ‖(v q - v p) - (v s - v r)‖) :
    12 * ε < ‖(v' q - v' p) - (v' s - v' r)‖ := by
  have hpq := norm_difference_perturb (v p) (v q) (v' p) (v' q)
  have hrs := norm_difference_perturb (v r) (v s) (v' r) (v' s)
  have hall := norm_difference_perturb (v s - v r) (v q - v p)
    (v' s - v' r) (v' q - v' p)
  have hn := norm_sub_norm_le ((v q - v p) - (v s - v r))
    ((v' q - v' p) - (v' s - v' r))
  rw [norm_sub_rev ((v q - v p) - (v s - v r))] at hn
  linarith [hv' p, hv' q, hv' r, hv' s]

lemma first_obstruction_count [Fintype P] {ε η : ℝ} (hε : 0 < ε) (hη : η ≤ ε / 2)
    (v' : P → Circle) (hv' : ∀ p, ‖v' p - firstRoster p‖ < η)
    (hsep : ∀ p q r s : P, p ≠ q → r ≠ s → (p, q) ≠ (r, s) →
      16 * ε < ‖(firstRoster q - firstRoster p) - (firstRoster s - firstRoster r)‖)
    (a : Circle) :
    (Finset.univ.filter (fun e : P × P => e.1 ≠ e.2 ∧ ‖a + v' e.2 - v' e.1‖ ≤ 6 * ε)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he hf
  by_contra hne
  have hs := first_roster_separation hε hη firstRoster v' hv' (hsep e.1 e.2 f.1 f.2 he.1 hf.1 hne)
  have hn := norm_sub_le (a + v' e.2 - v' e.1) (a + v' f.2 - v' f.1)
  have heq : (a + v' e.2 - v' e.1) - (a + v' f.2 - v' f.1) =
      (v' e.2 - v' e.1) - (v' f.2 - v' f.1) := by abel
  rw [heq] at hn
  linarith [he.2, hf.2]

def Forest (P : Type uP3) [DecidableEq P] :=
  {f : Fin 400 → P × P // FreshPairs (List.ofFn f)}

noncomputable instance [Fintype P] : Fintype (Forest P) := by
  classical
  unfold Forest
  infer_instance

def Batch (P : Type uP4) [DecidableEq P] := Option (Forest P × Bool)

noncomputable instance [Fintype P] : Fintype (Batch P) := by
  unfold Batch
  infer_instance

lemma batch_card [Fintype P] : Fintype.card (Batch P) = 2 * Fintype.card (Forest P) + 1 := by
  simp only [Batch, Fintype.card_option, Fintype.card_prod, Fintype.card_bool]
  omega

noncomputable def forestRoster (f : Forest P) : P → Circle :=
  Classical.choose (realize_sequence f.1 f.2 (fun j => (((j : ℝ) / 400 : ℝ) : Circle)))

lemma forestRoster_spec (f : Forest P) (j : Fin 400) :
    forestRoster f (f.1 j).2 - forestRoster f (f.1 j).1 = (((j : ℝ) / 400 : ℝ) : Circle) :=
  Classical.choose_spec (realize_sequence f.1 f.2 (fun j => (((j : ℝ) / 400 : ℝ) : Circle))) j

noncomputable def batchRoster (p : P) : Batch P → Circle
  | none => 0
  | some (f, _) => forestRoster f p

lemma batch_forest_hit {η : ℝ} (hη : η ≤ 1 / 1600)
    (v' : P → Batch P → Circle) (hv' : ∀ p c, ‖v' p c - batchRoster p c‖ < η)
    (a : Batch P → Circle) (f : Forest P) :
    ∃ j : Fin 400, ∃ c : Batch P,
      ‖a c + v' (f.1 j).2 c - v' (f.1 j).1 c‖ ≤ 1 / 200 := by
  let c : Batch P := some (f, false)
  obtain ⟨j, hj⟩ := grid_near 400 (by norm_num) (a c)
  have heq : batchRoster (f.1 j).2 c - batchRoster (f.1 j).1 c =
      (((j : ℝ) / 400 : ℝ) : Circle) := forestRoster_spec f j
  have hold : ‖a c + batchRoster (f.1 j).2 c - batchRoster (f.1 j).1 c‖ ≤ 1 / 800 := by
    rw [add_sub_assoc, heq]
    norm_num at hj ⊢
    exact hj
  have hh := norm_difference_perturb
    (batchRoster (f.1 j).1 c) (batchRoster (f.1 j).2 c)
    (v' (f.1 j).1 c) (v' (f.1 j).2 c)
  have hn := norm_add_le (a c + batchRoster (f.1 j).2 c - batchRoster (f.1 j).1 c)
    ((v' (f.1 j).2 c - v' (f.1 j).1 c) -
      (batchRoster (f.1 j).2 c - batchRoster (f.1 j).1 c))
  have halg : (a c + batchRoster (f.1 j).2 c - batchRoster (f.1 j).1 c) +
      ((v' (f.1 j).2 c - v' (f.1 j).1 c) -
        (batchRoster (f.1 j).2 c - batchRoster (f.1 j).1 c)) =
      a c + v' (f.1 j).2 c - v' (f.1 j).1 c := by abel
  rw [halg] at hn
  refine ⟨j, c, ?_⟩
  linarith [hv' (f.1 j).1 c, hv' (f.1 j).2 c]

lemma batch_obstruction_count [Fintype P] {η : ℝ} (hη : η ≤ 1 / 1600)
    (v' : P → Batch P → Circle) (hv' : ∀ p c, ‖v' p c - batchRoster p c‖ < η)
    (a : Batch P → Circle) :
    (Finset.univ.filter (fun e : P × P => e.1 ≠ e.2 ∧
      ∀ c : Batch P, 1 / 200 < ‖a c + v' e.2 c - v' e.1 c‖)).card ≤ 4 * 400 ^ 2 := by
  classical
  let B := Finset.univ.filter (fun e : P × P => e.1 ≠ e.2 ∧
    ∀ c : Batch P, 1 / 200 < ‖a c + v' e.2 c - v' e.1 c‖)
  apply count_of_no_forest B
  · intro e he
    exact (Finset.mem_filter.mp he).2.1
  · intro f hf
    obtain ⟨j, c, hj⟩ := batch_forest_hit hη v' hv' a ⟨f, hf⟩
    refine ⟨j, fun hm => ?_⟩
    have hbad := (Finset.mem_filter.mp hm).2.2 c
    linarith

def BlockI {C : Type uC6} [Fintype C] (s : ℕ) (t : Bool) (x : C → Circle) : Prop :=
  if t then x ∈ TypeTwo s else ∀ c, x c ∈ Near centersI (1 / 16)

def BlockJ {C : Type uC7} [Fintype C] (s : ℕ) (t : Bool) (x : C → Circle) : Prop :=
  if t then x ∈ TypeTwo s else ∀ c, x c ∈ Near centersJ (1 / 16)

lemma block_reversal_false {C : Type uC8} [Fintype C] (s : ℕ)
    (hC : Fintype.card C = 2 * s + 1) {t u : Bool} (htu : t ≠ u)
    {i j i' j' : C → Circle} (hi : BlockI s t i) (hj : BlockJ s t j)
    (hi' : BlockI s u i') (hj' : BlockJ s u j') (he : i + j' = i' + j) : False := by
  have hd (c : C) : i c - j c = i' c - j' c := by
    have hc := congrFun he c
    change i c + j' c = i' c + j c at hc
    calc
      i c - j c = (i c + j' c) - j c - j' c := by abel
      _ = (i' c + j c) - j c - j' c := by rw [hc]
      _ = i' c - j' c := by abel
  cases t <;> cases u
  · exact htu rfl
  · obtain ⟨c, hc⟩ := type_two_difference s hC hi' hj'
    have hs := type_one_difference (hi c) (hj c)
    rw [hd c] at hs
    linarith
  · obtain ⟨c, hc⟩ := type_two_difference s hC hi hj
    have hs := type_one_difference (hi' c) (hj' c)
    rw [← hd c] at hs
    linarith
  · exact htu rfl

lemma block_interior {C : Type uC9} [Fintype C] (s : ℕ)
    (hC : Fintype.card C = 2 * s + 1) (t : Bool) (z : C → Circle)
    (hz : ∃ c, ‖z c‖ ≤ 1 / 200) {ρ : ℝ} (hρ1 : ρ ≤ 1 / 96) (hρ2 : ρ ≤ 1 / 400) :
    ∃ i j : C → Circle, i + j = z ∧ ∀ h : C → Circle,
      (∀ c, ‖h c‖ ≤ ρ) → BlockI s t (i + h) ∧ BlockJ s t (j - h) := by
  classical
  cases t
  · choose i j hij hp using (fun c => type_one_interior (z c))
    refine ⟨i, j, funext hij, ?_⟩
    intro h hh
    exact ⟨fun c => (hp c (h c) ((hh c).trans hρ1)).1,
      fun c => (hp c (h c) ((hh c).trans hρ1)).2⟩
  · obtain ⟨i, j, hij, hp⟩ := type_two_interior s hC z hz
    exact ⟨i, j, hij, fun h hh => hp h (fun c => (hh c).trans hρ2)⟩

def ClockI {T : Type uT} {A : Type uA3} {B : Type uB} {C : Type uC10} [Fintype C] (ε : ℝ) (s : ℕ)
    (p : A → T → Bool) (t : B → T → Bool) (α : T) : Set ((A ⊕ (B × C)) → Circle) :=
  {x | (∀ a, x (Sum.inl a) ∈ FirstI ε (p a α)) ∧
    ∀ b, BlockI s (t b α) (fun c => x (Sum.inr (b, c)))}

def ClockJ {T : Type uT2} {A : Type uA4} {B : Type uB2} {C : Type uC11} [Fintype C] (ε : ℝ) (s : ℕ)
    (p : A → T → Bool) (t : B → T → Bool) (α : T) : Set ((A ⊕ (B × C)) → Circle) :=
  {x | (∀ a, x (Sum.inl a) ∈ FirstJ ε (p a α)) ∧
    ∀ b, BlockJ s (t b α) (fun c => x (Sum.inr (b, c)))}

def Obstruction {A : Type uA5} {B : Type uB3} {C : Type uC12} (ε : ℝ) : Set ((A ⊕ (B × C)) → Circle) :=
  {z | (∃ a, ‖z (Sum.inl a)‖ ≤ 6 * ε) ∨
    (∃ b, ∀ c, 1 / 200 < ‖z (Sum.inr (b, c))‖)}

def Edge {T : Type uT3} {A : Type uA6} {B : Type uB4} {C : Type uC13} [Fintype C] (ε : ℝ) (s : ℕ)
    (p : A → T → Bool) (t : B → T → Bool) (z : (A ⊕ (B × C)) → Circle) (α lam : T) : Prop :=
  ∃ i ∈ ClockI ε s p t α, ∃ j ∈ ClockJ ε s p t lam, i + j = z

lemma unequal_edge_unique {T : Type uT4} {A : Type uA7} {B : Type uB5} {C : Type uC14} [DecidableEq T] [Fintype C]
    {ε : ℝ} (hε : 0 < ε) (s : ℕ) (hC : Fintype.card C = 2 * s + 1)
    (p : A → T → Bool) (t : B → T → Bool)
    (hp : ∀ α lam γ ν, TagPartitions.Feasible α lam γ ν →
      ∃ a, TagPartitions.Satisfies α lam γ ν (p a))
    (ht : ∀ α lam, α ≠ lam → ∃ b, t b α ≠ t b lam)
    {z : (A ⊕ (B × C)) → Circle} {α lam γ ν : T} (hαlam : α ≠ lam)
    (hα : Edge ε s p t z α lam) (hγ : Edge ε s p t z γ ν) : γ = α ∧ ν = lam := by
  obtain ⟨i, hi, j, hj, hij⟩ := hα
  obtain ⟨i', hi', j', hj', hij'⟩ := hγ
  have hpair : ({α, lam} : Finset T) = {γ, ν} := by
    by_contra hn
    obtain ⟨a, ha, hl, hsame⟩ := hp α lam γ ν ⟨hαlam, hn⟩
    have hia := hi.1 a
    have hja := hj.1 a
    rw [ha] at hia
    rw [hl] at hja
    have hlo := first_left_right hia hja
    have hia' := hi'.1 a
    have hja' := hj'.1 a
    rw [← hsame] at hja'
    have hhi := first_same_side (p a γ) hia' hja'
    have he := congrFun (hij.trans hij'.symm) (Sum.inl a)
    change i (Sum.inl a) + j (Sum.inl a) = i' (Sum.inl a) + j' (Sum.inl a) at he
    rw [he] at hlo
    linarith
  have ha : α = γ ∨ α = ν := by
    have hm : α ∈ ({γ, ν} : Finset T) := hpair ▸ (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hl : lam = γ ∨ lam = ν := by
    have hm : lam ∈ ({γ, ν} : Finset T) := hpair ▸ (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hor : (γ = α ∧ ν = lam) ∨ (γ = lam ∧ ν = α) := by aesop
  rcases hor with h | ⟨hγ, hν⟩
  · exact h
  · subst γ
    subst ν
    obtain ⟨b, hb⟩ := ht α lam hαlam
    exfalso
    apply block_reversal_false s hC hb (hi.2 b) (hj'.2 b) (hi'.2 b) (hj.2 b)
    funext c
    exact congrFun (hij.trans hij'.symm) (Sum.inr (b, c))

lemma graph_alternative {T : Type uT5} {A : Type uA8} {B : Type uB6} {C : Type uC15} [DecidableEq T] [Fintype C]
    {ε : ℝ} (hε : 0 < ε) (s : ℕ) (hC : Fintype.card C = 2 * s + 1)
    (p : A → T → Bool) (t : B → T → Bool)
    (hp : ∀ α lam γ ν, TagPartitions.Feasible α lam γ ν →
      ∃ a, TagPartitions.Satisfies α lam γ ν (p a))
    (ht : ∀ α lam, α ≠ lam → ∃ b, t b α ≠ t b lam)
    (z : (A ⊕ (B × C)) → Circle) :
    (∀ α lam, Edge ε s p t z α lam → α = lam) ∨
      ∃ α lam, α ≠ lam ∧ Edge ε s p t z α lam ∧
        ∀ γ ν, Edge ε s p t z γ ν → γ = α ∧ ν = lam := by
  classical
  by_cases h : ∃ α lam, α ≠ lam ∧ Edge ε s p t z α lam
  · obtain ⟨α, lam, hne, he⟩ := h
    exact Or.inr ⟨α, lam, hne, he, fun γ ν h' => unequal_edge_unique hε s hC p t hp ht hne he h'⟩
  · left
    intro α lam he
    by_contra hn
    exact h ⟨α, lam, hn, he⟩

lemma clock_interior {T : Type uT6} {A : Type uA9} {B : Type uB7} {C : Type uC16} [Fintype C]
    {ε ρ : ℝ} (hε : 0 < ε) (hρ0 : ρ ≤ ε / 2) (hρ1 : ρ ≤ 1 / 96) (hρ2 : ρ ≤ 1 / 400)
    (s : ℕ) (hC : Fintype.card C = 2 * s + 1)
    (p : A → T → Bool) (t : B → T → Bool) (α : T)
    (z : (A ⊕ (B × C)) → Circle) (hz : z ∉ Obstruction ε) :
    ∃ i j : (A ⊕ (B × C)) → Circle, i + j = z ∧
      ∀ h : (A ⊕ (B × C)) → Circle, (∀ c, ‖h c‖ ≤ ρ) →
        i + h ∈ ClockI ε s p t α ∧ j - h ∈ ClockJ ε s p t α := by
  classical
  have hfirst (a : A) : 6 * ε < ‖z (Sum.inl a)‖ := by
    by_contra hn
    exact hz (Or.inl ⟨a, le_of_not_gt hn⟩)
  have hbatch (b : B) : ∃ c, ‖z (Sum.inr (b, c))‖ ≤ 1 / 200 := by
    by_contra hn
    push Not at hn
    exact hz (Or.inr ⟨b, hn⟩)
  choose iA jA hsA hpA using (fun a => first_interior hε (p a α) (z (Sum.inl a)) (hfirst a))
  choose iB jB hsB hpB using (fun b => block_interior s hC (t b α)
    (fun c => z (Sum.inr (b, c))) (hbatch b) hρ1 hρ2)
  let i : (A ⊕ (B × C)) → Circle := Sum.elim iA (fun bc => iB bc.1 bc.2)
  let j : (A ⊕ (B × C)) → Circle := Sum.elim jA (fun bc => jB bc.1 bc.2)
  refine ⟨i, j, ?_, ?_⟩
  · funext c
    cases c with
    | inl a => exact hsA a
    | inr bc => exact congrFun (hsB bc.1) bc.2
  · intro h hh
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro a
      exact (hpA a (h (Sum.inl a)) ((hh _).trans hρ0)).1
    · intro b
      exact (hpB b (fun c => h (Sum.inr (b, c))) (fun c => hh _)).1
    · intro a
      exact (hpA a (h (Sum.inl a)) ((hh _).trans hρ0)).2
    · intro b
      exact (hpB b (fun c => h (Sum.inr (b, c))) (fun c => hh _)).2

lemma clock_ball {T : Type uT7} {A : Type uA10} {B : Type uB8} {C : Type uC17} [Fintype A] [Fintype B] [Fintype C]
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ)
    (hρ0 : ρ ≤ ε / 2) (hρ1 : ρ ≤ 1 / 96) (hρ2 : ρ ≤ 1 / 400)
    (s : ℕ) (hC : Fintype.card C = 2 * s + 1)
    (p : A → T → Bool) (t : B → T → Bool) (α : T)
    (z : (A ⊕ (B × C)) → Circle) (hz : z ∉ Obstruction ε) :
    ∃ i : (A ⊕ (B × C)) → Circle, ∀ x, dist x i < ρ →
      x ∈ ClockI ε s p t α ∧ z - x ∈ ClockJ ε s p t α := by
  obtain ⟨i, j, hij, hp⟩ := clock_interior hε hρ0 hρ1 hρ2 s hC p t α z hz
  refine ⟨i, ?_⟩
  intro x hx
  have hnorm (c) : ‖(x - i) c‖ ≤ ρ := by
    exact le_of_lt (by simpa only [Pi.sub_apply, dist_eq_norm] using (dist_pi_lt_iff hρ).mp hx c)
  obtain ⟨hi, hj⟩ := hp (x - i) hnorm
  have hi' : i + (x - i) = x := by abel
  have hj' : j - (x - i) = z - x := by rw [← hij]; abel
  exact ⟨hi' ▸ hi, hj' ▸ hj⟩

noncomputable def roster [Fintype P] {A : Type uA11} {B : Type uB9} (p : P) : (A ⊕ (B × Batch P)) → Circle :=
  Sum.elim (fun _ => firstRoster p) (fun bc => batchRoster p bc.2)

noncomputable def obstructionPairs [Fintype P] {A : Type uA12} {B : Type uB10} {C : Type uC18} (ε : ℝ)
    (a : (A ⊕ (B × C)) → Circle) (v : P → (A ⊕ (B × C)) → Circle) : Finset (P × P) := by
  classical
  exact Finset.univ.filter (fun e => e.1 ≠ e.2 ∧ a + v e.2 - v e.1 ∈ Obstruction ε)

lemma roster_estimate [Fintype P] {A : Type uA13} {B : Type uB11} [Fintype A] [Fintype B]
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (hηε : η ≤ ε / 2) (hη0 : η ≤ 1 / 1600)
    (hsep : ∀ p q r s : P, p ≠ q → r ≠ s → (p, q) ≠ (r, s) →
      16 * ε < ‖(firstRoster q - firstRoster p) - (firstRoster s - firstRoster r)‖)
    (v' : P → (A ⊕ (B × Batch P)) → Circle)
    (hv' : ∀ p, dist (v' p) (roster p) < η)
    (a : (A ⊕ (B × Batch P)) → Circle) :
    (obstructionPairs ε a v').card ≤
        Fintype.card A + 4 * 400 ^ 2 * Fintype.card B := by
  classical
  unfold obstructionPairs
  have hnorm (p : P) (c : A ⊕ (B × Batch P)) :
      ‖v' p c - roster p c‖ < η := by
    simpa only [dist_eq_norm] using (dist_pi_lt_iff hη).mp (hv' p) c
  let EA (c : A) : Finset (P × P) := Finset.univ.filter (fun e => e.1 ≠ e.2 ∧
    ‖a (Sum.inl c) + v' e.2 (Sum.inl c) - v' e.1 (Sum.inl c)‖ ≤ 6 * ε)
  let EB (b : B) : Finset (P × P) := Finset.univ.filter (fun e => e.1 ≠ e.2 ∧
    ∀ c : Batch P, 1 / 200 < ‖a (Sum.inr (b, c)) + v' e.2 (Sum.inr (b, c)) - v' e.1 (Sum.inr (b, c))‖)
  have hEA (c : A) : (EA c).card ≤ 1 := first_obstruction_count hε hηε
    (fun p => v' p (Sum.inl c)) (fun p => hnorm p (Sum.inl c)) hsep (a (Sum.inl c))
  have hEB (b : B) : (EB b).card ≤ 4 * 400 ^ 2 := batch_obstruction_count hη0
    (fun p c => v' p (Sum.inr (b, c))) (fun p c => hnorm p (Sum.inr (b, c)))
    (fun c => a (Sum.inr (b, c)))
  have hcover : Finset.univ.filter (fun e : P × P => e.1 ≠ e.2 ∧
      a + v' e.2 - v' e.1 ∈ Obstruction ε) ⊆
      Finset.univ.biUnion EA ∪ Finset.univ.biUnion EB := by
    intro e he
    obtain ⟨hne, hob⟩ := (Finset.mem_filter.mp he).2
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
    rcases hob with ⟨c, hc⟩ | ⟨b, hb⟩
    · exact Or.inl ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, hc⟩⟩
    · exact Or.inr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, hb⟩⟩
  have ha := Finset.card_biUnion_le_card_mul Finset.univ EA 1 (fun c _ => hEA c)
  have hb := Finset.card_biUnion_le_card_mul Finset.univ EB (4 * 400 ^ 2) (fun b _ => hEB b)
  have hu := Finset.card_union_le (Finset.univ.biUnion EA) (Finset.univ.biUnion EB)
  have hd := Finset.card_le_card hcover
  simp only [Finset.card_univ, mul_one] at ha hb
  omega

noncomputable def badPairs {P : Type uP5} {C : Type uC19} [Fintype P]
    (W : Set (C → Circle)) (a : C → Circle) (v : P → C → Circle) : Finset (P × P) := by
  classical
  exact Finset.univ.filter (fun e => e.1 ≠ e.2 ∧ a + v e.2 - v e.1 ∈ W)

structure Specification (T : Type uT8) (P : Type uP6) (C : Type uC20) [Fintype T] [Fintype P] [Fintype C] where
  I : T → Set (C → Circle)
  J : T → Set (C → Circle)
  W : Set (C → Circle)
  v : P → C → Circle
  ρ : ℝ
  η : ℝ
  radius_pos : 0 < ρ
  tolerance_pos : 0 < η
  graph : ∀ z : C → Circle,
    (∀ α lam, (∃ i ∈ I α, ∃ j ∈ J lam, i + j = z) → α = lam) ∨
    ∃ α lam, α ≠ lam ∧ (∃ i ∈ I α, ∃ j ∈ J lam, i + j = z) ∧
      ∀ γ ν, (∃ i ∈ I γ, ∃ j ∈ J ν, i + j = z) → γ = α ∧ ν = lam
  interior : ∀ z : C → Circle, z ∉ W → ∀ α,
    ∃ i : C → Circle, ∀ x, dist x i < ρ → x ∈ I α ∧ z - x ∈ J α
  count : ∀ v' : P → C → Circle, (∀ p, dist (v' p) (v p) < η) →
    ∀ a : C → Circle, ((badPairs W a v').card : ℝ) ≤
      10000000 * Real.log (2 * Fintype.card T)

abbrev Coordinates (T : Type uT9) (P : Type uP7) [Fintype T] [DecidableEq P] :=
  Fin (TagPartitions.repetitions (Fintype.card T)) ⊕
    (Fin (TagPartitions.typeCount (Fintype.card T)) × Batch P)

theorem exists_clock (T : Type uT10) (P : Type uP8) [Fintype T] [Nonempty T] [Fintype P] [DecidableEq P] :
    Nonempty (Specification T P (Coordinates T P)) := by
  classical
  obtain ⟨p, hp⟩ := TagPartitions.exists_partitions (T := T)
  obtain ⟨t, ht⟩ := TagPartitions.exists_types (T := T)
  obtain ⟨ε, hε, _, _, hsep⟩ := firstRoster_parameters (P := P)
  let η := min (ε / 2) (1 / 1600 : ℝ)
  let ρ := min (ε / 2) (min (1 / 96 : ℝ) (1 / 400))
  have hη : 0 < η := lt_min (half_pos hε) (by norm_num)
  have hρ : 0 < ρ := lt_min (half_pos hε) (lt_min (by norm_num) (by norm_num))
  refine ⟨{
    I := ClockI ε (Fintype.card (Forest P)) p t
    J := ClockJ ε (Fintype.card (Forest P)) p t
    W := Obstruction ε
    v := roster
    ρ := ρ
    η := η
    radius_pos := hρ
    tolerance_pos := hη
    graph := ?_
    interior := ?_
    count := ?_ }⟩
  · exact graph_alternative hε _ (batch_card (P := P)) p t hp ht
  · intro z hz α
    exact clock_ball hε hρ (min_le_left _ _)
      ((min_le_right _ _).trans (min_le_left _ _))
      ((min_le_right _ _).trans (min_le_right _ _))
      _ (batch_card (P := P)) p t α z hz
  · intro v' hv' a
    have hb := roster_estimate hε hη (min_le_left _ _) (min_le_right _ _) hsep v' hv' a
    have hbR : ((badPairs (Obstruction ε) a v').card : ℝ) ≤
        ((TagPartitions.repetitions (Fintype.card T) +
          4 * 400 ^ 2 * TagPartitions.typeCount (Fintype.card T) : ℕ) : ℝ) := by
      have hb' : (badPairs (Obstruction ε) a v').card ≤
          TagPartitions.repetitions (Fintype.card T) +
            4 * 400 ^ 2 * TagPartitions.typeCount (Fintype.card T) := by
        have he : badPairs (Obstruction ε) a v' = obstructionPairs ε a v' := by
          ext e
          simp [badPairs, obstructionPairs]
        rw [he]
        simpa only [Fintype.card_fin] using hb
      exact_mod_cast hb'
    exact hbR.trans (TagPartitions.total_count_bound Fintype.card_pos)

lemma Specification.diagonal {T : Type uT11} {P : Type uP9} {C : Type uC21} [Fintype T] [Fintype P] [Fintype C]
    (S : Specification T P C) (z : C → Circle) (hz : z ∉ S.W) :
    ∀ α lam, (∃ i ∈ S.I α, ∃ j ∈ S.J lam, i + j = z) ↔ α = lam := by
  intro α lam
  have hdiag (a : T) : ∃ i ∈ S.I a, ∃ j ∈ S.J a, i + j = z := by
    obtain ⟨i, hi⟩ := S.interior z hz a
    obtain ⟨hI, hJ⟩ := hi i (by simpa using S.radius_pos)
    exact ⟨i, hI, z - i, hJ, by abel⟩
  constructor
  · intro he
    rcases S.graph z with h | ⟨a, l, hne, _, hu⟩
    · exact h α lam he
    · obtain ⟨ha, hl⟩ := hu a a (hdiag a)
      exact False.elim (hne hl)
  · rintro rfl
    exact hdiag α

end RobustClock

end GeneralizedStarHeight

end OAI
