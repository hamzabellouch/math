import OAI.Combinatorics.TreeEdit.SegmentComparison

namespace OAI

namespace TreeEdit

universe u

variable {α : Type u} {x y z : List α}

theorem card_orderEmb_le_choose (a s : ℕ) :
    Fintype.card (Fin s ↪o Fin a) ≤ a.choose s := by
  classical
  let rangeSet : (Fin s ↪o Fin a) → Finset (Fin a) :=
    fun f => Finset.univ.image f
  have hcard (f : Fin s ↪o Fin a) : (rangeSet f).card = s := by
    simp [rangeSet, Finset.card_image_of_injective _ f.injective]
  let F : (Fin s ↪o Fin a) → (Finset.univ : Finset (Fin a)).powersetCard s :=
    fun f => ⟨rangeSet f, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard f⟩⟩
  have hF : Function.Injective F := by
    intro f g hfg
    have he : rangeSet f = rangeSet g := congrArg Subtype.val hfg
    have hf := Finset.orderEmbOfFin_unique' (hcard f)
      (f := f) (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    have hg := Finset.orderEmbOfFin_unique' (hcard f)
      (f := g) (fun i => by rw [he]; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    exact hf.trans hg.symm
  simpa using Fintype.card_le_of_injective F hF

theorem card_prescribed_bits {P : ℕ} (s : Finset (Fin P)) (pattern : Fin P → Bool) :
    (Finset.univ.filter (fun w : Fin P → Bool => ∀ i ∈ s, w i = pattern i)).card ≤
      2 ^ (P - s.card) := by
  classical
  let T := Finset.univ.filter (fun w : Fin P → Bool => ∀ i ∈ s, w i = pattern i)
  let F : T → (↥(sᶜ) → Bool) := fun w i => w.val i.val
  have hF : Function.Injective F := by
    intro v w hvw
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ s
    · exact ((Finset.mem_filter.mp v.property).2 i hi).trans
        ((Finset.mem_filter.mp w.property).2 i hi).symm
    · exact congrFun hvw ⟨i, Finset.mem_compl.mpr hi⟩
  have hh := Fintype.card_le_of_injective F hF
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_bool,
    Finset.card_compl, Fintype.card_fin, T] using hh

theorem choose_weight_bound (a s : ℕ) (hs : s ≤ a) :
    a.choose s * 16 ^ s ≤ 17 ^ a := by
  have hh := Finset.single_le_sum (f := fun j => 16 ^ j * 1 ^ (a - j) * a.choose j)
    (s := Finset.range (a + 1)) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega : s < a + 1))
  have hp : (17 : ℕ) ^ a = ∑ j ∈ Finset.range (a + 1), 16 ^ j * 1 ^ (a - j) * a.choose j := by
    simpa using (add_pow (16 : ℕ) 1 a)
  rw [← hp] at hh
  simpa [Nat.mul_comm] using hh

theorem choose_matching_bound (a s t : ℕ) (hs : s ≤ a)
    (hdense : 99 * a ≤ 100 * s) (ht : 4 * t ≤ a) :
    (a.choose s) ^ 2 * 2 ^ t ≤ 2 ^ s := by
  have hweight := choose_weight_bound a s hs
  have hon : (17 : ℕ) ^ 4 ≤ 2 ^ 17 := by norm_num
  have hp : (a.choose s) ^ 4 * 2 ^ (16 * s) ≤ 2 ^ (17 * a) := by
    calc
      _ = (a.choose s * 16 ^ s) ^ 4 := by
        rw [Nat.mul_pow, ← Nat.pow_mul]
        have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
        rw [h16, ← Nat.pow_mul]
        norm_num only [Nat.reducePow]
        congr 2; omega
      _ ≤ (17 ^ a) ^ 4 := Nat.pow_le_pow_left hweight 4
      _ = (17 ^ 4) ^ a := by rw [← Nat.pow_mul, ← Nat.pow_mul]; congr 1; omega
      _ ≤ (2 ^ 17) ^ a := Nat.pow_le_pow_left hon a
      _ = 2 ^ (17 * a) := by rw [← Nat.pow_mul]
  have hexp : 17 * a + 2 * t ≤ 18 * s := by omega
  have hpow := Nat.mul_le_mul_right (2 ^ (2 * t)) hp
  have hbig : (a.choose s) ^ 4 * 2 ^ (2 * t) * 2 ^ (16 * s) ≤
      2 ^ (2 * s) * 2 ^ (16 * s) := by
    calc
      _ = ((a.choose s) ^ 4 * 2 ^ (16 * s)) * 2 ^ (2 * t) := by ring
      _ ≤ 2 ^ (17 * a) * 2 ^ (2 * t) := hpow
      _ = 2 ^ (17 * a + 2 * t) := (Nat.pow_add _ _ _).symm
      _ ≤ 2 ^ (18 * s) := Nat.pow_le_pow_right (by decide) hexp
      _ = 2 ^ (2 * s) * 2 ^ (16 * s) := by rw [← Nat.pow_add]; congr 1; omega
  have hc : (a.choose s) ^ 4 * 2 ^ (2 * t) ≤ 2 ^ (2 * s) :=
    Nat.le_of_mul_le_mul_right hbig (by positivity)
  have hsq : ((a.choose s) ^ 2 * 2 ^ t) ^ 2 ≤ (2 ^ s) ^ 2 := by
    simpa only [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm t 2,
      Nat.mul_comm s 2, Nat.reduceMul] using hc
  exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hsq

theorem card_agreement_embedding {P s : ℕ} (f : Fin s ↪ Fin P) (bits : Fin s → Bool) :
    (Finset.univ.filter (fun w : Fin P → Bool => ∀ i, w (f i) = bits i)).card ≤
      2 ^ (P - s) := by
  classical
  let S := Finset.univ.image f
  let T := Finset.univ.filter (fun w : Fin P → Bool => ∀ i, w (f i) = bits i)
  let F : T → (↥(Sᶜ) → Bool) := fun w i => w.val i.val
  have hF : Function.Injective F := by
    intro v w hvw
    apply Subtype.ext
    funext j
    by_cases hj : j ∈ S
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
      exact ((Finset.mem_filter.mp v.property).2 i).trans
        ((Finset.mem_filter.mp w.property).2 i).symm
    · exact congrFun hvw ⟨j, Finset.mem_compl.mpr hj⟩
  have hS : S.card = s := by simp [S, Finset.card_image_of_injective _ f.injective]
  have hh := Fintype.card_le_of_injective F hF
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_bool,
    Finset.card_compl, Fintype.card_fin, T, hS] using hh

def segmentPositions {P a : ℕ} (p : ℕ) (hp : p + a ≤ P) : Fin a ↪o Fin P :=
  OrderEmbedding.ofStrictMono (fun i => ⟨p + i.val, by omega⟩)
    (by intro i j hij; change p + i.val < p + j.val; omega)

theorem card_matched_segments {P a s : ℕ} (v : Fin P → Bool)
    (p q : ℕ) (hp : p + a ≤ P) (hq : q + a ≤ P) :
    (Finset.univ.filter (fun w : Fin P → Bool =>
      ∃ f g : Fin s ↪o Fin a, ∀ i,
        w (segmentPositions q hq (g i)) = v (segmentPositions p hp (f i)))).card ≤
      (a.choose s) ^ 2 * 2 ^ (P - s) := by
  classical
  let T := fun fg : (Fin s ↪o Fin a) × (Fin s ↪o Fin a) =>
    Finset.univ.filter (fun w : Fin P → Bool => ∀ i,
      w (segmentPositions q hq (fg.2 i)) = v (segmentPositions p hp (fg.1 i)))
  have hT (fg) : (T fg).card ≤ 2 ^ (P - s) :=
    card_agreement_embedding (fg.2.comp (segmentPositions q hq)).toEmbedding _
  have he : Finset.univ.filter (fun w : Fin P → Bool =>
      ∃ f g : Fin s ↪o Fin a, ∀ i,
        w (segmentPositions q hq (g i)) = v (segmentPositions p hp (f i))) =
      Finset.univ.biUnion T := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion, T, Prod.exists]
  rw [he]
  calc
    _ ≤ ∑ fg ∈ Finset.univ, (T fg).card := Finset.card_biUnion_le
    _ ≤ ∑ _fg : (Fin s ↪o Fin a) × (Fin s ↪o Fin a), 2 ^ (P - s) :=
      Finset.sum_le_sum (fun fg _ => hT fg)
    _ = (Fintype.card (Fin s ↪o Fin a)) ^ 2 * 2 ^ (P - s) := by simp [sq]
    _ ≤ (a.choose s) ^ 2 * 2 ^ (P - s) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (card_orderEmb_le_choose a s) 2)

theorem large_lcs_segment_witness {P a s : ℕ} (v w : Fin P → Bool)
    (p q : ℕ) (hp : p + a ≤ P) (hq : q + a ≤ P)
    (hs : s ≤ lcs (segment (vectorWord v).val p a) (segment (vectorWord w).val q a)) :
    ∃ f g : Fin s ↪o Fin a, ∀ i,
      w (segmentPositions q hq (g i)) = v (segmentPositions p hp (f i)) := by
  let X := segment (vectorWord v).val p a
  let Y := segment (vectorWord w).val q a
  have hX : X.length = a := length_segment _ (by simpa only [vectorWord, List.length_ofFn] using hp)
  have hY : Y.length = a := length_segment _ (by simpa only [vectorWord, List.length_ofFn] using hq)
  obtain ⟨A⟩ := exists_lcs_alignment X Y
  let e := Fin.castLEOrderEmb hs
  let f := (e.comp A.left).comp (Fin.castOrderIso hX).toOrderEmbedding
  let g := (e.comp A.right).comp (Fin.castOrderIso hY).toOrderEmbedding
  refine ⟨f, g, ?_⟩
  intro i
  have h := A.agree (e i)
  simp only [X, Y, List.get_eq_getElem] at h
  rw [segment_get, segment_get] at h
  change w ⟨q + (A.right (e i)).val, _⟩ = v ⟨p + (A.left (e i)).val, _⟩
  simp only [vectorWord, List.getElem_ofFn] at h
  convert h.symm using 2

theorem card_bad_segment {P a t : ℕ} (v : Fin P → Bool)
    (p q : ℕ) (hp : p + a ≤ P) (hq : q + a ≤ P) (ht : 4 * t ≤ a) :
    (Finset.univ.filter (fun w : Fin P → Bool =>
      99 * a < 100 * lcs (segment (vectorWord v).val p a)
        (segment (vectorWord w).val q a))).card * 2 ^ t ≤ 2 ^ P := by
  classical
  let s := a - a / 100
  have hsa : s ≤ a := Nat.sub_le _ _
  have hdense : 99 * a ≤ 100 * s := by dsimp [s]; omega
  have hsub : Finset.univ.filter (fun w : Fin P → Bool =>
      99 * a < 100 * lcs (segment (vectorWord v).val p a)
        (segment (vectorWord w).val q a)) ⊆
      Finset.univ.filter (fun w : Fin P → Bool =>
        ∃ f g : Fin s ↪o Fin a, ∀ i,
          w (segmentPositions q hq (g i)) = v (segmentPositions p hp (f i))) := by
    intro w hw
    have hw' := (Finset.mem_filter.mp hw).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ w, large_lcs_segment_witness v w p q hp hq ?_⟩
    dsimp [s]
    omega
  have hc := (Finset.card_le_card hsub).trans (card_matched_segments v p q hp hq)
  have hentropy := choose_matching_bound a s t hsa hdense ht
  calc
    _ ≤ ((a.choose s) ^ 2 * 2 ^ (P - s)) * 2 ^ t := Nat.mul_le_mul_right _ hc
    _ = ((a.choose s) ^ 2 * 2 ^ t) * 2 ^ (P - s) := by ring
    _ ≤ 2 ^ s * 2 ^ (P - s) := Nat.mul_le_mul_right _ hentropy
    _ = 2 ^ P := by
      rw [← Nat.pow_add, Nat.add_sub_of_le (hsa.trans (by omega : a ≤ P))]

def VectorSeparated {P : ℕ} (cutoff : ℕ) (v w : Fin P → Bool) : Prop :=
  ∀ p q a : ℕ, cutoff ≤ a → p + a ≤ P → q + a ≤ P →
    100 * lcs (segment (vectorWord v).val p a) (segment (vectorWord w).val q a) ≤ 99 * a

theorem VectorSeparated.symm {P cutoff : ℕ} {v w : Fin P → Bool}
    (h : VectorSeparated cutoff v w) : VectorSeparated cutoff w v := by
  intro p q a ha hp hq
  rw [lcs_comm]
  exact h q p a ha hq hp

attribute [local instance] Classical.propDecidable

theorem card_bad_vector {P cutoff t : ℕ} (v : Fin P → Bool) (ht : 4 * t ≤ cutoff) :
    (Finset.univ.filter (fun w : Fin P → Bool => ¬ VectorSeparated cutoff v w)).card * 2 ^ t ≤
      (P + 1) ^ 3 * 2 ^ P := by
  classical
  let I := Fin (P + 1) × Fin (P + 1) × Fin (P + 1)
  let valid := fun j : I => cutoff ≤ j.2.2.val ∧
    j.1.val + j.2.2.val ≤ P ∧ j.2.1.val + j.2.2.val ≤ P
  let T := fun j : I => if valid j then
    Finset.univ.filter (fun w : Fin P → Bool =>
      99 * j.2.2.val < 100 * lcs (segment (vectorWord v).val j.1.val j.2.2.val)
        (segment (vectorWord w).val j.2.1.val j.2.2.val)) else ∅
  have hT (j : I) : (T j).card * 2 ^ t ≤ 2 ^ P := by
    by_cases hj : valid j
    · simp only [T, ite_eq_left hj]
      exact card_bad_segment v _ _ hj.2.1 hj.2.2 (ht.trans hj.1)
    · simp [T, hj]
  have hsub : Finset.univ.filter (fun w : Fin P → Bool => ¬ VectorSeparated cutoff v w) ⊆
      Finset.univ.biUnion T := by
    intro w hw
    have hh := (Finset.mem_filter.mp hw).2
    simp only [VectorSeparated, not_forall, not_le] at hh
    obtain ⟨p, q, a, ha, hp, hq, hbad⟩ := hh
    let j : I := (⟨p, by omega⟩, ⟨q, by omega⟩, ⟨a, by omega⟩)
    have hj : valid j := ⟨ha, hp, hq⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_univ j, ?_⟩
    simp only [T, ite_eq_left hj]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hbad⟩
  calc
    _ ≤ (Finset.univ.biUnion T).card * 2 ^ t :=
      Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
    _ ≤ (∑ j : I, (T j).card) * 2 ^ t := Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = ∑ j : I, ((T j).card * 2 ^ t) := Finset.sum_mul _ _ _
    _ ≤ ∑ _j : I, 2 ^ P := Finset.sum_le_sum (fun j _ => hT j)
    _ = (P + 1) ^ 3 * 2 ^ P := by simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_prod, Fintype.card_fin, smul_eq_mul, I]; ring

theorem exists_separated_vectors (P cutoff t K : ℕ) (ht : 4 * t ≤ cutoff)
    (hcount : K * (P + 1) ^ 3 < 2 ^ t) :
    ∃ c : Fin K → (Fin P → Bool), ∀ i j, i ≠ j → VectorSeparated cutoff (c i) (c j) := by
  classical
  induction K with
  | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  | succ K ih =>
      have hK : K * (P + 1) ^ 3 < 2 ^ t := lt_of_le_of_lt
        (Nat.mul_le_mul_right _ (Nat.le_succ K)) hcount
      obtain ⟨c, hc⟩ := ih hK
      let B := Finset.univ.biUnion (fun i : Fin K =>
        Finset.univ.filter (fun w : Fin P → Bool => ¬ VectorSeparated cutoff (c i) w))
      have hB : B.card * 2 ^ t ≤ K * (P + 1) ^ 3 * 2 ^ P := by
        calc
          _ ≤ (∑ i : Fin K, (Finset.univ.filter (fun w : Fin P → Bool =>
              ¬ VectorSeparated cutoff (c i) w)).card) * 2 ^ t :=
            Nat.mul_le_mul_right _ Finset.card_biUnion_le
          _ = ∑ i : Fin K, ((Finset.univ.filter (fun w : Fin P → Bool =>
              ¬ VectorSeparated cutoff (c i) w)).card * 2 ^ t) := Finset.sum_mul _ _ _
          _ ≤ ∑ _i : Fin K, ((P + 1) ^ 3 * 2 ^ P) :=
            Finset.sum_le_sum (fun i _ => card_bad_vector (c i) ht)
          _ = K * (P + 1) ^ 3 * 2 ^ P := by simp [Nat.mul_assoc]
      have hlt : B.card < (Finset.univ : Finset (Fin P → Bool)).card := by
        have hh : B.card * 2 ^ t < 2 ^ t * 2 ^ P :=
          hB.trans_lt (Nat.mul_lt_mul_of_pos_right hK (by positivity))
        rw [Nat.mul_comm (2 ^ t)] at hh
        have hh' := Nat.lt_of_mul_lt_mul_right hh
        simpa using hh'
      have hnot : ¬ (Finset.univ : Finset (Fin P → Bool)) ⊆ B := by
        intro hsub
        exact (not_le_of_gt hlt) (Finset.card_le_card hsub)
      obtain ⟨w, _, hw⟩ := Finset.not_subset.mp hnot
      have hwc (i : Fin K) : VectorSeparated cutoff (c i) w := by
        by_contra hn
        apply hw
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
          Finset.mem_filter.mpr ⟨Finset.mem_univ w, hn⟩⟩
      refine ⟨Fin.cons w c, ?_⟩
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro hij; exact (hij rfl).elim
        · intro _; exact (hwc j).symm
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro _; exact hwc i
        · intro hij; exact hc i j (by intro h; exact hij (congrArg Fin.succ h))

theorem exists_segment_code {Γ : Type u} [Fintype Γ] (P cutoff t : ℕ)
    (ht : 4 * t ≤ cutoff) (hcount : Fintype.card Γ * (P + 1) ^ 3 < 2 ^ t) :
    ∃ c : Γ → Word Bool P, SegmentCode c cutoff := by
  obtain ⟨c, hc⟩ := exists_separated_vectors P cutoff t (Fintype.card Γ) ht hcount
  let e := Fintype.equivFin Γ
  refine ⟨fun a => vectorWord (c (e a)), ?_⟩
  intro a b hab p q len hlen hp hq
  exact hc (e a) (e b) (fun h => hab (e.injective h)) p q len hlen hp hq

noncomputable def sourceCodeCutoff (M : ℕ) : ℕ :=
  ⌈120 * (Real.log (M : ℝ) / Real.log 2)⌉₊

theorem sourceCodeCutoff_bounds {M : ℕ} (hM : 2 ≤ M) :
    120 * Nat.log 2 M ≤ sourceCodeCutoff M ∧
      sourceCodeCutoff M ≤ 120 * (Nat.log 2 M + 1) := by
  have hM0 : M ≠ 0 := by omega
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp := Nat.pow_log_le_self 2 hM0
  have hq := Nat.lt_pow_succ_log_self (by decide : 1 < 2) M
  have hp' : (2 : ℝ) ^ Nat.log 2 M ≤ (M : ℝ) := by exact_mod_cast hp
  have hq' : (M : ℝ) < (2 : ℝ) ^ (Nat.log 2 M + 1) := by exact_mod_cast hq
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ Nat.log 2 M) hp'
  have hu := Real.log_lt_log (by exact_mod_cast (by omega : 0 < M)) hq'
  rw [Real.log_pow] at hl hu
  have hlo : (Nat.log 2 M : ℝ) ≤ Real.log (M : ℝ) / Real.log 2 :=
    (le_div_iff₀ hlog).mpr hl
  have hup : Real.log (M : ℝ) / Real.log 2 ≤ (Nat.log 2 M + 1 : ℕ) :=
    (div_le_iff₀ hlog).mpr hu.le
  constructor
  · have hh := Nat.le_ceil (120 * (Real.log (M : ℝ) / Real.log 2))
    have hc : (120 : ℝ) * (Nat.log 2 M : ℝ) ≤ (sourceCodeCutoff M : ℝ) := by
      exact (mul_le_mul_of_nonneg_left hlo (by norm_num)).trans hh
    exact_mod_cast hc
  · apply Nat.ceil_le.mpr
    have hh := mul_le_mul_of_nonneg_left hup (by norm_num : (0 : ℝ) ≤ 120)
    exact_mod_cast hh

theorem cutoff_dyadic_domination {n : ℕ} (hn : 16 ≤ n) :
    480 * (n + 1) ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [Nat.pow_succ]
      omega

theorem sourceCodeCutoff_absorb {M : ℕ} (hM : 2 ^ 16 ≤ M) :
    4 * M * sourceCodeCutoff M ≤ M ^ 2 := by
  have hM2 : 2 ≤ M := by norm_num at hM; omega
  have hn : 16 ≤ Nat.log 2 M := Nat.le_log_of_pow_le (by decide) hM
  have hdom := (cutoff_dyadic_domination hn).trans (Nat.pow_log_le_self 2 (by omega : M ≠ 0))
  have hc := (sourceCodeCutoff_bounds hM2).2
  calc
    _ ≤ 4 * M * (120 * (Nat.log 2 M + 1)) := Nat.mul_le_mul_left _ hc
    _ = M * (480 * (Nat.log 2 M + 1)) := by ring
    _ ≤ M * M := Nat.mul_le_mul_left M hdom
    _ = M ^ 2 := (sq M).symm

theorem polynomial_code_count {M : ℕ} (hM : 2 ≤ M) :
    M * (M ^ 2 + 1) ^ 3 < 2 ^ (8 * (Nat.log 2 M + 1) + 4) := by
  have hsq : M ^ 2 + 1 ≤ 2 * M ^ 2 := by nlinarith
  have hpow : M ≤ 2 ^ (Nat.log 2 M + 1) := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) M).le
  calc
    _ ≤ M * (2 * M ^ 2) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsq 3)
    _ = 8 * M ^ 7 := by ring
    _ ≤ 8 * (2 ^ (Nat.log 2 M + 1)) ^ 7 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpow 7)
    _ = 2 ^ ((Nat.log 2 M + 1) * 7 + 3) := by
      rw [Nat.pow_add 2 ((Nat.log 2 M + 1) * 7) 3, Nat.pow_mul]
      norm_num
      ring
    _ < 2 ^ (8 * (Nat.log 2 M + 1) + 4) :=
      Nat.pow_lt_pow_right (by decide) (by omega)

theorem source_segment_code_exists {Γ : Type u} [Fintype Γ] {M : ℕ}
    (hM : 2 ≤ M) (hK : Fintype.card Γ ≤ M) :
    ∃ c : Γ → Word Bool (M ^ 2), SegmentCode c (sourceCodeCutoff M) := by
  let t := 8 * (Nat.log 2 M + 1) + 4
  have hn : 1 ≤ Nat.log 2 M := Nat.log_pos (by decide) hM
  have hcut := (sourceCodeCutoff_bounds hM).1
  have ht : 4 * t ≤ sourceCodeCutoff M := by dsimp [t]; omega
  apply exists_segment_code (M ^ 2) (sourceCodeCutoff M) t ht
  exact (Nat.mul_le_mul_right _ hK).trans_lt (polynomial_code_count hM)

theorem binary_conversion : FixedLengthBinaryConversion.{u} := by
  refine ⟨2 ^ 16, ?_⟩
  intro M hM Γ inst hK₁ hK
  have hM2 : 2 ≤ M := by norm_num at hM; omega
  obtain ⟨c, hc⟩ := source_segment_code_exists hM2 hK
  refine ⟨c, ?_⟩
  intro x y
  have hlen (z : Word Γ M) : (encode c z.val).length = M ^ 3 := by
    rw [length_encode, z.property]
    ring
  refine ⟨hlen x, hlen y, ?_⟩
  exact code_edit_comparison (by positivity : 0 < M ^ 2) (sourceCodeCutoff_absorb hM) c hc x y

end TreeEdit

end OAI
