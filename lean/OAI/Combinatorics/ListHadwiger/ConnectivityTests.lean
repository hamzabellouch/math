import OAI.Combinatorics.ListHadwiger.Concentration

namespace OAI

namespace LinearListHadwiger

namespace ConnectivityTests

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V]

def IsCutMatching (G : SimpleGraph V) (B : Finset V) (E : Finset (V × V)) : Prop :=
  (∀ e ∈ E, e.1 ∈ B ∧ e.2 ∉ B ∧ G.Adj e.1 e.2) ∧
  (E : Set (V × V)).Pairwise (fun e f => e.1 ≠ f.1 ∧ e.2 ≠ f.2)

def endpoints (E : Finset (V × V)) : Finset V :=
  E.image Prod.fst ∪ E.image Prod.snd

lemma endpoints_card_le {V : Type} [Fintype V] [DecidableEq V] (E : Finset (V × V)) : (endpoints E).card ≤ 2 * E.card := by
  exact (Finset.card_union_le _ _).trans (by
    have h₁ := Finset.card_image_le (s := E) (f := Prod.fst)
    have h₂ := Finset.card_image_le (s := E) (f := Prod.snd)
    omega)

lemma IsCutMatching.mono {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {B : Finset V} {E F : Finset (V × V)}
    (h : IsCutMatching G B E) (hFE : F ⊆ E) : IsCutMatching G B F :=
  ⟨fun e he => h.1 e (hFE he), h.2.mono hFE⟩

lemma IsCutMatching.fst_card {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {B : Finset V} {E : Finset (V × V)}
    (h : IsCutMatching G B E) : (E.image Prod.fst).card = E.card := by
  apply Finset.card_image_iff.mpr
  intro e he f hf heq
  by_contra hn
  exact (h.2 he hf hn).1 heq

lemma IsCutMatching.snd_card {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {B : Finset V} {E : Finset (V × V)}
    (h : IsCutMatching G B E) : (E.image Prod.snd).card = E.card := by
  apply Finset.card_image_iff.mpr
  intro e he f hf heq
  by_contra hn
  exact (h.2 he hf hn).2 heq

lemma IsCutMatching.endpoints_inter_left {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {B : Finset V}
    {E : Finset (V × V)} (h : IsCutMatching G B E) :
    endpoints E ∩ B = E.image Prod.fst := by
  ext v
  simp only [endpoints, Finset.mem_inter, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨hmem, hv⟩
    rcases hmem with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
    · exact ⟨e, he, rfl⟩
    · exact False.elim ((h.1 e he).2.1 hv)
  · rintro ⟨e, he, rfl⟩
    exact ⟨Or.inl ⟨e, he, rfl⟩, (h.1 e he).1⟩

lemma IsCutMatching.endpoints_inter_right {G : SimpleGraph V} {B : Finset V}
    {E : Finset (V × V)} (h : IsCutMatching G B E) :
    endpoints E ∩ Bᶜ = E.image Prod.snd := by
  ext v
  simp only [endpoints, Finset.mem_inter, Finset.mem_union, Finset.mem_image,
    Finset.mem_compl]
  constructor
  · rintro ⟨hmem, hv⟩
    rcases hmem with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
    · exact False.elim (hv (h.1 e he).1)
    · exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨Or.inr ⟨e, he, rfl⟩, (h.1 e he).2.1⟩

lemma cross_edge_of_connected {W : Type} (H : SimpleGraph W) (hc : H.Connected)
    (P : W → Prop) (a b : W) (ha : P a) (hb : ¬P b) :
    ∃ x y, P x ∧ ¬P y ∧ H.Adj x y := by
  classical
  obtain ⟨p⟩ := hc.preconnected a b
  have step : ∀ {x y : W}, H.Walk x y → P x → ¬P y →
      ∃ u v, P u ∧ ¬P v ∧ H.Adj u v := by
    intro x y q
    induction q with
    | nil => exact fun hx hy => False.elim (hy hx)
    | @cons x z y hxz q ih =>
      intro hx hy
      by_cases hz : P z
      · exact ih hz hy
      · exact ⟨x, z, hx, hz, hxz⟩
  exact step p ha hb

lemma crossing_edge_avoiding (G : SimpleGraph V) (B X : Finset V) {k : ℕ}
    (hc : KConnectedOn G Finset.univ k) (hx : X.card < k)
    (hb : (X ∩ B).card < B.card) (hbc : (X ∩ Bᶜ).card < Bᶜ.card) :
    ∃ a ∈ B, ∃ b ∉ B, a ∉ X ∧ b ∉ X ∧ G.Adj a b := by
  have hba : ¬B ⊆ X := by
    intro hh
    rw [Finset.inter_eq_right.mpr hh] at hb
    exact (lt_self_iff_false _).mp hb
  have hbca : ¬Bᶜ ⊆ X := by
    intro hh
    rw [Finset.inter_eq_right.mpr hh] at hbc
    exact (lt_self_iff_false _).mp hbc
  obtain ⟨a, ha, hax⟩ := Finset.not_subset.mp hba
  obtain ⟨b, hb, hbx⟩ := Finset.not_subset.mp hbca
  have hconn := hc.2 X (Finset.subset_univ _) hx
  let a' : {v // v ∈ (Finset.univ \ X : Finset V)} := ⟨a, by simp [hax]⟩
  let b' : {v // v ∈ (Finset.univ \ X : Finset V)} := ⟨b, by simp [hbx]⟩
  obtain ⟨u, v, hu, hv, hadj⟩ := cross_edge_of_connected _ hconn
    (fun v => v.val ∈ B) a' b' ha (Finset.mem_compl.mp hb)
  exact ⟨u.val, hu, v.val, hv, (Finset.mem_sdiff.mp u.property).2,
    (Finset.mem_sdiff.mp v.property).2, hadj⟩

theorem exists_cut_matching (G : SimpleGraph V) (B : Finset V) {k m : ℕ}
    (hc : KConnectedOn G Finset.univ k) (hk : 2 * m ≤ k)
    (hb : m ≤ B.card) (hbc : m ≤ Bᶜ.card) :
    ∃ E : Finset (V × V), IsCutMatching G B E ∧ E.card = m := by
  classical
  induction m with
  | zero => exact ⟨∅, by simp [IsCutMatching], rfl⟩
  | succ m ih =>
    obtain ⟨E, he, hcard⟩ := ih (by omega) (by omega) (by omega)
    have hx : (endpoints E).card < k := (endpoints_card_le E).trans_lt (by omega)
    have hbl : (endpoints E ∩ B).card < B.card := by
      rw [he.endpoints_inter_left, he.fst_card, hcard]
      omega
    have hbr : (endpoints E ∩ Bᶜ).card < Bᶜ.card := by
      rw [he.endpoints_inter_right, he.snd_card, hcard]
      omega
    obtain ⟨a, ha, b, hb, hax, hbx, hadj⟩ := crossing_edge_avoiding G B (endpoints E)
      hc hx hbl hbr
    have hane : ∀ e ∈ E, a ≠ e.1 := by
      intro e heq heq'
      apply hax
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, heq, heq'.symm⟩)
    have hbne : ∀ e ∈ E, b ≠ e.2 := by
      intro e heq heq'
      apply hbx
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, heq, heq'.symm⟩)
    have hnot : (a,b) ∉ E := fun h => hane (a,b) h rfl
    refine ⟨insert (a,b) E, ⟨?_, ?_⟩, by simp [hnot, hcard]⟩
    · intro e heq
      rcases Finset.mem_insert.mp heq with rfl | heq
      · exact ⟨ha, hb, hadj⟩
      · exact he.1 e heq
    · intro e heq f hfq hne
      rcases Finset.mem_insert.mp heq with rfl | heq
      · rcases Finset.mem_insert.mp hfq with rfl | hfq
        · exact False.elim (hne rfl)
        · exact ⟨hane f hfq, hbne f hfq⟩
      · rcases Finset.mem_insert.mp hfq with rfl | hfq
        · exact ⟨(hane e heq).symm, (hbne e heq).symm⟩
        · exact he.2 heq hfq hne

theorem finite_hitting {α β : Type} [Fintype α] [Fintype β]
    (s : ℕ) (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1)
    (R : β → α → Prop) [DecidableRel R] (p : ℝ) (hp : 0 ≤ p)
    (hrow : ∀ v, ∑ a, w a * (if ¬R v a then 1 else 0) ≤ p)
    (hsmall : (Fintype.card β : ℝ) * p ^ s < 1) :
    ∃ f : Fin s → α, ∀ v, ∃ i, R v (f i) := by
  classical
  let m : (Fin s → α) → ℝ := fun f => ∏ i, w (f i)
  let bad : β → (Fin s → α) → ℝ := fun v f => if ∀ i, ¬R v (f i) then 1 else 0
  have hm : ∀ f, 0 ≤ m f := fun f => Finset.prod_nonneg fun i _ => hw (f i)
  have hnorm : ∑ f, m f = 1 := by
    dsimp [m]
    rw [← Fintype.prod_sum]
    simp [hs]
  have hevent (v : β) : ∑ f, m f * bad v f ≤ p ^ s := by
    calc
      ∑ f, m f * bad v f = ∏ i : Fin s, ∑ a, w a * (if ¬R v a then 1 else 0) := by
        rw [Fintype.prod_sum]
        apply Finset.sum_congr rfl
        intro f _
        simp only [Finset.prod_mul_distrib, Finset.prod_boole, Finset.mem_univ,
          forall_const, m, bad]
      _ ≤ ∏ _i : Fin s, p := by
        have hnonneg : 0 ≤ ∑ a, w a * (if ¬R v a then 1 else 0) :=
          Finset.sum_nonneg fun a _ => mul_nonneg (hw a) (by split_ifs <;> norm_num)
        have hprod (T : Finset (Fin s)) :
            (∏ _i ∈ T, ∑ a, w a * (if ¬R v a then 1 else 0)) ≤ ∏ _i ∈ T, p := by
          induction T using Finset.induction_on with
          | empty => simp
          | @insert index T hindex ih =>
            simp only [Finset.prod_insert hindex]
            exact mul_le_mul (hrow v) ih (Finset.prod_nonneg fun _ _ => hnonneg) hp
        exact hprod Finset.univ
      _ = p ^ s := by simp
  by_contra h
  have hbad : ∀ f : Fin s → α, ∃ v, ∀ i, ¬R v (f i) := by
    simpa only [not_exists, not_forall] using h
  have hone : 1 ≤ ∑ f, ∑ v, m f * bad v f := by
    rw [← hnorm]
    apply Finset.sum_le_sum
    intro f _
    obtain ⟨v, hv⟩ := hbad f
    calc
      m f = m f * bad v f := by simp [bad, hv]
      _ ≤ ∑ v, m f * bad v f := Finset.single_le_sum (f := fun v => m f * bad v f)
        (fun v _ => mul_nonneg (hm f) (by dsimp [bad]; split_ifs <;> norm_num))
        (Finset.mem_univ _)
  have hupper : (∑ f, ∑ v, m f * bad v f) ≤ (Fintype.card β : ℝ) * p ^ s := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _v : β, p ^ s := Finset.sum_le_sum fun v _ => hevent v
      _ = _ := by simp
  linarith

lemma sum_uniform_mask (A D : Finset V) (z : ℝ) :
    (∑ a : V, (if a ∈ A then z else 0) * (if a ∈ D then 1 else 0)) =
      ((A ∩ D).card : ℝ) * z := by
  calc
    _ = ∑ a : V, if a ∈ A ∩ D then z else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a ∈ A <;> by_cases hd : a ∈ D <;> simp [ha, hd]
    _ = _ := by rw [Finset.sum_ite_mem]; simp

theorem exists_neighborhood_cover (G : SimpleGraph V) (A : Finset V) [DecidableRel G.Adj]
    {n k : ℝ} (hn : 1 ≤ n) (hk : 0 < k) (ha : A.Nonempty)
    (hAn : (A.card : ℝ) ≤ n)
    (hd : ∀ v ∈ A, k / 3 ≤ ((A.filter (G.Adj v)).card : ℝ)) :
    ∃ R ⊆ A, R.card ≤ ⌈10 * (n / k) * Real.log (2 * n)⌉₊ ∧
      ∀ v ∈ A, ∃ r ∈ R, G.Adj v r := by
  classical
  let s := ⌈10 * (n / k) * Real.log (2 * n)⌉₊
  let c : ℝ := A.card
  have hc : 0 < c := by
    dsimp [c]
    exact_mod_cast Finset.card_pos.mpr ha
  have hcn : c ≤ n := hAn
  let w : V → ℝ := fun a => if a ∈ A then c⁻¹ else 0
  have hw : ∀ a, 0 ≤ w a := fun a => by dsimp [w]; positivity
  have hs : ∑ a, w a = 1 := by
    dsimp [w]
    rw [Finset.sum_ite_mem]
    simp only [Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    change c * c⁻¹ = 1
    exact mul_inv_cancel₀ hc.ne'
  let rel : A → V → Prop := fun v a => a ∈ A ∧ G.Adj v.val a
  let p := Real.exp (-k / (3 * n))
  have hp : 0 ≤ p := (Real.exp_pos _).le
  have hrow : ∀ v : A, ∑ a, w a * (if ¬rel v a then 1 else 0) ≤ p := by
    intro v
    let D := A.filter fun a => ¬G.Adj v.val a
    have hsum : (∑ a, w a * (if ¬rel v a then 1 else 0)) = (D.card : ℝ) / c := by
      calc
        _ = ∑ a : V, (if a ∈ A then c⁻¹ else 0) * (if a ∈ D then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases ha : a ∈ A <;> by_cases hadj : G.Adj v.val a <;>
            simp [w, rel, D, ha, hadj]
        _ = ((A ∩ D).card : ℝ) * c⁻¹ := sum_uniform_mask A D _
        _ = (D.card : ℝ) / c := by
          rw [Finset.inter_eq_right.mpr (Finset.filter_subset _ _)]; rfl
    have hcard : ((A.filter (G.Adj v.val)).card : ℝ) + (D.card : ℝ) = c := by
      dsimp [D, c]
      exact_mod_cast Finset.card_filter_add_card_filter_not (s := A) (G.Adj v.val)
    have hdegree := hd v.val v.property
    have hcpos : 0 < 3 * n := by linarith
    have hquot : (D.card : ℝ) / c ≤ 1 - k / (3 * n) := by
      apply (div_le_iff₀ hc).mpr
      have hkn : k / (3 * n) * c ≤ k / 3 := by
        calc
          _ ≤ k / (3 * n) * n := mul_le_mul_of_nonneg_left hcn (by positivity)
          _ = k / 3 := by field_simp
      nlinarith
    rw [hsum]
    exact hquot.trans (by simpa [p, neg_div] using Real.one_sub_le_exp_neg (k / (3 * n)))
  have hlog : 0 < Real.log (2 * n) := Real.log_pos (by linarith)
  have hsreal : 10 * (n / k) * Real.log (2 * n) ≤ (s : ℝ) := Nat.le_ceil _
  have hexponent : (s : ℝ) * (k / (3 * n)) ≥ Real.log (2 * n) := by
    have hh := mul_le_mul_of_nonneg_right hsreal (show 0 ≤ k by positivity)
    have heq : (10 * (n / k) * Real.log (2 * n)) * k = 10 * n * Real.log (2 * n) := by
      field_simp
    rw [heq] at hh
    have h3n : 0 < 3 * n := by linarith
    rw [← mul_div_assoc]
    apply (le_div_iff₀ h3n).mpr
    change Real.log (2 * n) * (3 * n) ≤ (s : ℝ) * k
    nlinarith
  have hsmall : (Fintype.card A : ℝ) * p ^ s < 1 := by
    have he : p ^ s ≤ (2 * n)⁻¹ := by
      dsimp [p]
      rw [← Real.exp_nat_mul]
      calc
        _ ≤ Real.exp (-Real.log (2 * n)) := by
          apply Real.exp_le_exp.mpr
          simp only [neg_div, mul_neg]
          linarith
        _ = (2 * n)⁻¹ := by rw [Real.exp_neg, Real.exp_log (by linarith)]
    have hca : (Fintype.card A : ℝ) = c := by simp [c]
    rw [hca]
    calc
      c * p ^ s ≤ n * (2 * n)⁻¹ := mul_le_mul hcn he (pow_nonneg hp _) (by linarith)
      _ = 1 / 2 := by field_simp
      _ < 1 := by norm_num
  obtain ⟨f, hf⟩ := finite_hitting s w hw hs rel p hp hrow hsmall
  let R := (Finset.univ.image f) ∩ A
  refine ⟨R, Finset.inter_subset_right, ?_, ?_⟩
  · exact (Finset.card_le_card Finset.inter_subset_left).trans
      ((Finset.card_image_le).trans (by simp [s]))
  · intro v hv
    obtain ⟨i, hiA, hiadj⟩ := hf ⟨v, hv⟩
    exact ⟨f i, Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hiA⟩,
      hiadj⟩

lemma sum_powers_le (n s : ℕ) : ∑ i ∈ Finset.range (s + 1), n ^ i ≤ (n + 1) ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ]
    have hh : n ^ s ≤ (n + 1) ^ s := Nat.pow_le_pow_left (by omega) s
    rw [pow_succ, pow_succ]
    nlinarith

def smallSets (s : ℕ) : Finset (Finset V) :=
  (Finset.range (s + 1)).biUnion fun i => Finset.univ.powersetCard i

lemma mem_smallSets {s : ℕ} {R : Finset V} : R ∈ smallSets s ↔ R.card ≤ s := by
  simp only [smallSets, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard,
    Finset.subset_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro h; exact ⟨R.card, by omega, rfl⟩

lemma smallSets_card_le (s : ℕ) :
    (smallSets (V := V) s).card ≤ (Fintype.card V + 1) ^ (s + 1) := by
  calc
    _ ≤ ∑ i ∈ Finset.range (s + 1), (Finset.univ.powersetCard i : Finset (Finset V)).card :=
      Finset.card_biUnion_le
    _ = ∑ i ∈ Finset.range (s + 1), (Fintype.card V).choose i := by
      simp only [Finset.card_powersetCard, Finset.card_univ]
    _ ≤ ∑ i ∈ Finset.range (s + 1), (Fintype.card V) ^ i :=
      Finset.sum_le_sum fun i _ => Nat.choose_le_pow _ _
    _ ≤ (Fintype.card V + 1) ^ s := sum_powers_le _ _
    _ ≤ (Fintype.card V + 1) ^ (s + 1) := Nat.pow_le_pow_right (by omega) (by omega)

lemma IsCutMatching.card_le_cover {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {B : Finset V} {E : Finset (V × V)}
    (h : IsCutMatching G B E) (T : Finset V)
    (hcover : ∀ e ∈ E, e.1 ∈ T ∨ e.2 ∈ T) : E.card ≤ (endpoints E ∩ T).card := by
  let f : V × V → V := fun e => if e.1 ∈ T then e.1 else e.2
  have hf : Set.InjOn f (E : Set (V × V)) := by
    intro e he e' he' heq
    by_contra hn
    have hh := h.2 he he' hn
    by_cases heT : e.1 ∈ T <;> by_cases heT' : e'.1 ∈ T
    · exact hh.1 (by simpa [f, heT, heT'] using heq)
    · have heq' : e.1 = e'.2 := by simpa [f, heT, heT'] using heq
      exact (h.1 e' he').2.1 (heq' ▸ (h.1 e he).1)
    · have heq' : e.2 = e'.1 := by simpa [f, heT, heT'] using heq
      exact (h.1 e he).2.1 (heq' ▸ (h.1 e' he').1)
    · exact hh.2 (by simpa [f, heT, heT'] using heq)
  have hsub : E.image f ⊆ endpoints E ∩ T := by
    intro v hv
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
    by_cases heT : e.1 ∈ T
    · simp only [f, ite_eq_left heT]
      exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨e, he, rfl⟩), heT⟩
    · simp only [f, ite_eq_right heT]
      exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨e, he, rfl⟩), (hcover e he).resolve_left heT⟩
  rw [← Finset.card_image_iff.mpr hf]
  exact Finset.card_le_card hsub

lemma separator_neighbors_le {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {S A Z A' : Finset V} (hsep : SeparatorSplit G S A Z A') {v : V} (hv : v ∈ A) :
    (S.filter (G.Adj v)).card ≤ (A.filter (G.Adj v)).card + Z.card := by
  have hi : S.filter (G.Adj v) ⊆ A.filter (G.Adj v) ∪ Z := by
    intro w hw
    obtain ⟨hwS, hadj⟩ := Finset.mem_filter.mp hw
    rw [← hsep.union_eq] at hwS
    rcases Finset.mem_union.mp hwS with hawz | haw'
    · rcases Finset.mem_union.mp hawz with haw | hwz
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨haw, hadj⟩)
      · exact Finset.mem_union_right _ hwz
    · exact False.elim (hsep.anticomplete v hv w haw' hadj)
  exact (Finset.card_le_card hi).trans (Finset.card_union_le _ _)

lemma SeparatorSplit.swap_test {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {S A Z A' : Finset V}
    (h : SeparatorSplit G S A Z A') : SeparatorSplit G S A' Z A := by
  refine ⟨?_, h.sep_right.symm, h.left_right.symm, h.left_sep.symm,
    h.right_nonempty, h.left_nonempty, ?_⟩
  · rw [← h.union_eq]; ext v; simp only [Finset.mem_union]; tauto
  · intro v hv w hw hadj
    exact h.anticomplete w hw v hv hadj.symm

noncomputable def neighborhoodUnion (G : SimpleGraph V) (R : Finset V) : Finset V :=
  by classical exact Finset.univ.filter fun v => ∃ r ∈ R, G.Adj r v

lemma mem_neighborhoodUnion {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {R : Finset V} {v : V} :
    v ∈ neighborhoodUnion G R ↔ ∃ r ∈ R, G.Adj r v := by
  classical
  simp [neighborhoodUnion]

theorem separator_test (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℝ} {k : ℕ} (hn : 1 ≤ n) (hk : 64 ≤ k) (horder : (Fintype.card V : ℝ) ≤ n)
    {U A Z A' : Finset V} (hsep : SeparatorSplit G (Finset.univ \ U) A Z A')
    (hz : Z.card < k / 32)
    (hdeg : ∀ v, k ≤ 2 * (((Finset.univ \ U).filter (G.Adj v)).card)) :
    ∃ R : Finset V, R.card ≤ ⌈10 * (n / k) * Real.log (2 * n)⌉₊ ∧
      k / 8 ≤ (neighborhoodUnion G R).card ∧
      k / 8 ≤ (neighborhoodUnion G R)ᶜ.card ∧
      ∀ E, IsCutMatching G (neighborhoodUnion G R) E → E.card = k / 8 →
        k ≤ 32 * (endpoints E ∩ U).card := by
  classical
  have hkin : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hZreal : 32 * (Z.card : ℝ) < (k : ℝ) := by exact_mod_cast (show 32 * Z.card < k by omega)
  have hinternal : ∀ v ∈ A, (k : ℝ) / 3 ≤ ((A.filter (G.Adj v)).card : ℝ) := by
    intro v hv
    have hd := hdeg v
    have hh := separator_neighbors_le G hsep hv
    have hd' : (k : ℝ) ≤ 2 * ((((Finset.univ \ U).filter (G.Adj v)).card : ℕ) : ℝ) := by
      exact_mod_cast hd
    have hh' : ((((Finset.univ \ U).filter (G.Adj v)).card : ℕ) : ℝ) ≤
        ((A.filter (G.Adj v)).card : ℝ) + (Z.card : ℝ) := by exact_mod_cast hh
    linarith
  have hinternal' : ∀ v ∈ A', (k : ℝ) / 3 ≤ ((A'.filter (G.Adj v)).card : ℝ) := by
    intro v hv
    have hd := hdeg v
    have hh := separator_neighbors_le G (SeparatorSplit.swap_test hsep) hv
    have hd' : (k : ℝ) ≤ 2 * ((((Finset.univ \ U).filter (G.Adj v)).card : ℕ) : ℝ) := by
      exact_mod_cast hd
    have hh' : ((((Finset.univ \ U).filter (G.Adj v)).card : ℕ) : ℝ) ≤
        ((A'.filter (G.Adj v)).card : ℝ) + (Z.card : ℝ) := by exact_mod_cast hh
    linarith
  have ha : (k : ℝ) / 3 ≤ (A.card : ℝ) := by
    obtain ⟨v, hv⟩ := hsep.left_nonempty
    exact (hinternal v hv).trans (by exact_mod_cast Finset.card_filter_le A (G.Adj v))
  have ha' : (k : ℝ) / 3 ≤ (A'.card : ℝ) := by
    obtain ⟨v, hv⟩ := hsep.right_nonempty
    exact (hinternal' v hv).trans (by exact_mod_cast Finset.card_filter_le A' (G.Adj v))
  obtain ⟨R, hRA, hRcard, hRAcover⟩ := exists_neighborhood_cover G A hn hkin hsep.left_nonempty
    ((by exact_mod_cast Finset.card_le_univ A : (A.card : ℝ) ≤ Fintype.card V).trans horder) hinternal
  have hAB : A ⊆ neighborhoodUnion G R := by
    intro v hv
    obtain ⟨r, hr, hadj⟩ := hRAcover v hv
    exact mem_neighborhoodUnion.mpr ⟨r, hr, hadj.symm⟩
  have hAB' : A' ⊆ (neighborhoodUnion G R)ᶜ := by
    intro v hv
    apply Finset.mem_compl.mpr
    intro hmem
    obtain ⟨r, hr, hadj⟩ := mem_neighborhoodUnion.mp hmem
    exact hsep.anticomplete r (hRA hr) v hv hadj
  have hma : k / 8 ≤ A.card := by
    have hh : (k : ℝ) ≤ 3 * A.card := by linarith
    have hh' : k ≤ 3 * A.card := by exact_mod_cast hh
    omega
  have hma' : k / 8 ≤ A'.card := by
    have hh : (k : ℝ) ≤ 3 * A'.card := by linarith
    have hh' : k ≤ 3 * A'.card := by exact_mod_cast hh
    omega
  refine ⟨R, hRcard, hma.trans (Finset.card_le_card hAB),
    hma'.trans (Finset.card_le_card hAB'), ?_⟩
  intro E he hecard
  have hcover : ∀ e ∈ E, e.1 ∈ U ∪ Z ∨ e.2 ∈ U ∪ Z := by
    intro e heE
    by_contra hncover
    have hleft : e.1 ∉ U ∪ Z := fun hh => hncover (Or.inl hh)
    have hright : e.2 ∉ U ∪ Z := fun hh => hncover (Or.inr hh)
    have heS : e.1 ∈ Finset.univ \ U := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact fun hh => hleft (Finset.mem_union_left _ hh)
    have heS' : e.2 ∈ Finset.univ \ U := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact fun hh => hright (Finset.mem_union_left _ hh)
    have heA : e.1 ∈ A := by
      rw [← hsep.union_eq] at heS
      rcases Finset.mem_union.mp heS with hh | hh
      · exact (Finset.mem_union.mp hh).resolve_right (fun h => hleft (Finset.mem_union_right _ h))
      · exact False.elim ((Finset.mem_compl.mp (hAB' hh)) (he.1 e heE).1)
    have heA' : e.2 ∈ A' := by
      rw [← hsep.union_eq] at heS'
      rcases Finset.mem_union.mp heS' with hh | hh
      · rcases Finset.mem_union.mp hh with h | h
        · exact False.elim ((he.1 e heE).2.1 (hAB h))
        · exact False.elim (hright (Finset.mem_union_right _ h))
      · exact hh
    exact hsep.anticomplete e.1 heA e.2 heA' (he.1 e heE).2.2
  have hehe := he.card_le_cover (U ∪ Z) hcover
  have hsub : endpoints E ∩ (U ∪ Z) ⊆ (endpoints E ∩ U) ∪ Z := by
    intro v hv
    obtain ⟨hvE, hv⟩ := Finset.mem_inter.mp hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvE, hv⟩)
    · exact Finset.mem_union_right _ hv
  have hsize := hehe.trans ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))
  rw [hecard] at hsize
  omega

theorem cut_test (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℝ} {k : ℕ}
    (hk : 64 ≤ k) (horder : (Fintype.card V : ℝ) ≤ n)
    (hc : KConnectedOn G Finset.univ k) :
    ∃ F : Finset (Finset (V × V)),
      (F.card : ℝ) ≤ (n + 1) ^ (⌈10 * (n / k) * Real.log (2 * n)⌉₊ + 1) ∧
      (∀ E ∈ F, E.card = k / 8 ∧ ∃ B, IsCutMatching G B E) ∧
      ∀ U : Finset V,
        (∀ v, k ≤ 2 * ((Finset.univ \ U).filter (fun w => G.Adj v w)).card) →
        (∀ E ∈ F, 32 * (endpoints E ∩ U).card < k) →
        KConnectedOn G (Finset.univ \ U) (k / 32) := by
  classical
  have hord : k < Fintype.card V := by simpa using hc.1
  have hn : 1 ≤ n := (by exact_mod_cast (show 1 ≤ Fintype.card V by omega) :
    (1 : ℝ) ≤ Fintype.card V).trans horder
  let s := ⌈10 * (n / k) * Real.log (2 * n)⌉₊
  let goodR := (smallSets (V := V) s).filter fun R =>
    k / 8 ≤ (neighborhoodUnion G R).card ∧ k / 8 ≤ (neighborhoodUnion G R)ᶜ.card
  have hM : ∀ R : goodR, ∃ E, IsCutMatching G (neighborhoodUnion G R.val) E ∧ E.card = k / 8 := by
    intro R
    obtain ⟨_, hleft, hright⟩ := Finset.mem_filter.mp R.property
    exact exists_cut_matching G _ hc (by omega) hleft hright
  choose f hf hcard using hM
  let F := Finset.univ.image f
  have hfF : ∀ R : goodR, f R ∈ F := fun R => Finset.mem_image.mpr ⟨R, Finset.mem_univ _, rfl⟩
  refine ⟨F, ?_, ?_, ?_⟩
  · have hnum : F.card ≤ (Fintype.card V + 1) ^ (s + 1) := by
      calc
        F.card ≤ (Finset.univ : Finset goodR).card := Finset.card_image_le
        _ = goodR.card := by simp
        _ ≤ (smallSets (V := V) s).card := Finset.card_filter_le _ _
        _ ≤ _ := smallSets_card_le s
    have hreal : (F.card : ℝ) ≤ ((Fintype.card V : ℝ) + 1) ^ (s + 1) := by exact_mod_cast hnum
    exact hreal.trans (by gcongr)
  · intro E he
    obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp he
    exact ⟨hcard R, neighborhoodUnion G R.val, hf R⟩
  · intro U hdeg htest
    have hresord : k / 32 < (Finset.univ \ U).card := by
      have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
      let v : V := Classical.choice inferInstance
      have hd := hdeg v
      have hi : ((Finset.univ \ U).filter (fun w => G.Adj v w)).card ≤
          (Finset.univ \ U).card := Finset.card_filter_le _ _
      omega
    by_contra hres
    obtain ⟨A, Z, A', hz, hsep⟩ := exists_separator G (Finset.univ \ U) hresord hres
    obtain ⟨R, hR, hleft, hright, hdetect⟩ := separator_test G hn hk horder hsep hz hdeg
    have hRg : R ∈ goodR := Finset.mem_filter.mpr ⟨mem_smallSets.mpr hR, hleft, hright⟩
    let r : goodR := ⟨R, hRg⟩
    have hlarge := hdetect (f r) (hf r) (hcard r)
    have hsmall := htest (f r) (hfF r)
    omega

end ConnectivityTests

end LinearListHadwiger

end OAI
