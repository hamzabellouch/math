import OAI.Combinatorics.ListHadwiger.Connectivity

namespace OAI

namespace LinearListHadwiger
open scoped Classical

namespace PaletteReservation

noncomputable def weight {α : Type} [Fintype α] (p : ℝ) (σ : α → Bool) : ℝ :=
  ∏ a, if σ a then p else 1 - p

noncomputable def count {α : Type} (X : Finset α) (σ : α → Bool) : ℕ :=
  (X.filter fun a => σ a = true).card

lemma weight_nonneg {α : Type} [Fintype α] {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (σ : α → Bool) : 0 ≤ weight p σ := by
  apply Finset.prod_nonneg
  intro a _
  split <;> linarith

lemma weighted_product {α : Type} [Fintype α] (p : ℝ) (f : α → Bool → ℝ) :
    (∑ σ : α → Bool, weight p σ * ∏ a, f a (σ a)) =
      ∏ a, ((1 - p) * f a false + p * f a true) := by
  classical
  simp only [weight, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun a (b : Bool) =>
    (if b then p else 1 - p) * f a b)]
  apply Finset.prod_congr rfl
  intro a _
  simp [add_comm]

lemma sum_weight {α : Type} [Fintype α] (p : ℝ) :
    ∑ σ : α → Bool, weight p σ = 1 := by
  have h := weighted_product p (fun (_ : α) (_ : Bool) => (1 : ℝ))
  simpa using h

lemma pow_count {α : Type} [Fintype α] (X : Finset α) (σ : α → Bool) (z : ℝ) :
    z ^ count X σ = ∏ a : α, if a ∈ X ∧ σ a = true then z else 1 := by
  classical
  have he : (Finset.univ.filter fun a : α => a ∈ X ∧ σ a = true) =
      X.filter (fun a => σ a = true) := by ext a; simp
  simp [count, Finset.prod_ite, he]

lemma moment {α : Type} [Fintype α] (p z : ℝ) (X : Finset α) :
    (∑ σ : α → Bool, weight p σ * z ^ count X σ) =
      (1 - p + p * z) ^ X.card := by
  classical
  simp_rw [pow_count]
  rw [weighted_product p (fun a b => if a ∈ X ∧ b = true then z else 1)]
  have hprod : (∏ a : α,
        ((1 - p) * (if a ∈ X ∧ false = true then z else 1) +
          p * (if a ∈ X ∧ true = true then z else 1))) =
      ∏ a : α, if a ∈ X then (1 - p + p * z) else 1 := by
    apply Finset.prod_congr rfl
    intro a _
    by_cases ha : a ∈ X <;> simp [ha]
  rw [hprod]
  simp

lemma exists_lt_of_mean_lt {Ω : Type} [Fintype Ω] (w F : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hs : ∑ ω, w ω = 1)
    (hF : (∑ ω, w ω * F ω) < 1) : ∃ ω, F ω < 1 := by
  by_contra hn
  push Not at hn
  have hh : (∑ ω, w ω) ≤ ∑ ω, w ω * F ω := by
    apply Finset.sum_le_sum
    intro ω _
    nlinarith [hw ω, hn ω]
  linarith

lemma lower_moment_bound {α : Type} [Fintype α] (X : Finset α)
    {u m : ℕ} (hu : X.card = u) (hu0 : 0 < u) (hm : 2 * m ≤ u) :
    (∑ σ : α → Bool, weight (2 * (m : ℝ) / u) σ *
      ((2 : ℝ) ^ m * (1 / 2 : ℝ) ^ count X σ)) ≤ (3 / 4 : ℝ) ^ m := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu0
  have hmR : 2 * (m : ℝ) ≤ u := by exact_mod_cast hm
  rw [show (∑ σ : α → Bool, weight (2 * (m : ℝ) / u) σ *
      ((2 : ℝ) ^ m * (1 / 2 : ℝ) ^ count X σ)) =
      (2 : ℝ) ^ m * ∑ σ : α → Bool,
        weight (2 * (m : ℝ) / u) σ * (1 / 2 : ℝ) ^ count X σ by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring]
  rw [moment, hu]
  have hbase : 1 - 2 * (m : ℝ) / u + 2 * (m : ℝ) / u * (1 / 2) =
      1 - (m : ℝ) / u := by ring
  rw [hbase]
  have hnonneg : 0 ≤ 1 - (m : ℝ) / u := by
    have hle : (m : ℝ) / u ≤ 1 := (div_le_one huR).mpr (by linarith)
    linarith
  have he : 1 - (m : ℝ) / u ≤ Real.exp (-(m : ℝ) / u) := by
    have hh := Real.add_one_le_exp (-(m : ℝ) / u)
    simpa only [neg_div, sub_eq_add_neg, add_comm] using hh
  have hpow := pow_le_pow_left₀ hnonneg he u
  have heq : Real.exp (-(m : ℝ) / u) ^ u = Real.exp (-(m : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [heq] at hpow
  have he2 : Real.exp (-1) ≤ (3 / 8 : ℝ) := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos (1 : ℝ))).mpr
    have hx := Real.exp_one_gt_d9
    norm_num at hx ⊢
    linarith
  calc
    (2 : ℝ) ^ m * (1 - (m : ℝ) / u) ^ u
        ≤ 2 ^ m * Real.exp (-(m : ℝ)) := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (2 * Real.exp (-1)) ^ m := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      ring
    _ ≤ (3 / 4 : ℝ) ^ m := by
      apply pow_le_pow_left₀ (by positivity)
      linarith

lemma upper_moment_bound {α : Type} [Fintype α] (X : Finset α)
    {u m : ℕ} (hu : X.card = u) (hu0 : 0 < u) :
    (∑ σ : α → Bool, weight (2 * (m : ℝ) / u) σ *
      ((2 : ℝ) ^ count X σ / (2 : ℝ) ^ (4 * m))) ≤ (3 / 4 : ℝ) ^ m := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu0
  rw [show (∑ σ : α → Bool, weight (2 * (m : ℝ) / u) σ *
      ((2 : ℝ) ^ count X σ / (2 : ℝ) ^ (4 * m))) =
      (∑ σ : α → Bool, weight (2 * (m : ℝ) / u) σ *
        (2 : ℝ) ^ count X σ) / (2 : ℝ) ^ (4 * m) by
    rw [Finset.sum_div]; apply Finset.sum_congr rfl; intros; ring]
  rw [moment, hu]
  have hbase : 1 - 2 * (m : ℝ) / u + 2 * (m : ℝ) / u * 2 =
      1 + 2 * (m : ℝ) / u := by ring
  rw [hbase]
  have hpow := pow_le_pow_left₀
    (show 0 ≤ 1 + 2 * (m : ℝ) / u by positivity)
    (show 1 + 2 * (m : ℝ) / u ≤ Real.exp (2 * (m : ℝ) / u) by
      linarith [Real.add_one_le_exp (2 * (m : ℝ) / u)]) u
  have heq : Real.exp (2 * (m : ℝ) / u) ^ u = Real.exp (2 * (m : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [heq] at hpow
  have he3 : Real.exp 1 ≤ 3 := by
    have hh := Real.exp_one_lt_d9
    norm_num at hh
    linarith
  calc
    (1 + 2 * (m : ℝ) / u) ^ u / 2 ^ (4 * m)
        ≤ Real.exp (2 * (m : ℝ)) / 2 ^ (4 * m) :=
      div_le_div_of_nonneg_right hpow (by positivity)
    _ = (Real.exp 1 ^ 2 / 16) ^ m := by
      have hnum : Real.exp (2 * (m : ℝ)) = (Real.exp 1 ^ 2) ^ m := by
        rw [← pow_mul, ← Real.exp_nat_mul]
        congr 1
        simp
      have hden : (2 : ℝ) ^ (4 * m) = (16 : ℝ) ^ m := by
        rw [pow_mul]
        norm_num
      rw [hnum, hden, div_pow]
    _ ≤ (3 / 4 : ℝ) ^ m := by
      apply pow_le_pow_left₀ (by positivity)
      have hh : Real.exp 1 ^ 2 ≤ (3 : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) he3 _
      norm_num at hh ⊢
      linarith

theorem exists_reservation {V α : Type} [Fintype α] (L : V → Finset α)
    (X T : Finset V) {u m : ℕ} (hu0 : 0 < u) (hm : 2 * m ≤ u)
    (hL : ∀ v ∈ X ∪ T, (L v).card = u)
    (hsmall : ((X.card + T.card : ℕ) : ℝ) * (3 / 4 : ℝ) ^ m < 1) :
    ∃ R : Finset α, (∀ v ∈ X, m ≤ (L v ∩ R).card) ∧
      ∀ v ∈ T, (L v ∩ R).card ≤ 4 * m := by
  classical
  let p : ℝ := 2 * (m : ℝ) / u
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hp' : p ≤ 1 := by
    dsimp [p]
    apply (div_le_one (by exact_mod_cast hu0)).mpr
    exact_mod_cast hm
  let lower : V → (α → Bool) → ℝ := fun v σ =>
    (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ count (L v) σ
  let upper : V → (α → Bool) → ℝ := fun v σ =>
    (2 : ℝ) ^ count (L v) σ / (2 : ℝ) ^ (4 * m)
  let F : (α → Bool) → ℝ := fun σ => (∑ v ∈ X, lower v σ) + ∑ v ∈ T, upper v σ
  have hlow : ∀ v ∈ X, (∑ σ, weight p σ * lower v σ) ≤ (3 / 4 : ℝ) ^ m := by
    intro v hv
    exact lower_moment_bound (L v) (hL v (Finset.mem_union_left T hv)) hu0 hm
  have hup : ∀ v ∈ T, (∑ σ, weight p σ * upper v σ) ≤ (3 / 4 : ℝ) ^ m := by
    intro v hv
    exact upper_moment_bound (L v) (hL v (Finset.mem_union_right X hv)) hu0
  have hmean : ∑ σ, weight p σ * F σ < 1 := by
    have heq : (∑ σ, weight p σ * F σ) =
        (∑ v ∈ X, ∑ σ, weight p σ * lower v σ) +
          ∑ v ∈ T, ∑ σ, weight p σ * upper v σ := by
      simp only [F, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
      congr 1 <;> rw [Finset.sum_comm]
    rw [heq]
    have h1 := Finset.sum_le_sum hlow
    have h2 := Finset.sum_le_sum hup
    simp only [Finset.sum_const, nsmul_eq_mul] at h1 h2
    have hsum : (X.card : ℝ) * (3 / 4 : ℝ) ^ m +
        (T.card : ℝ) * (3 / 4 : ℝ) ^ m =
        ((X.card + T.card : ℕ) : ℝ) * (3 / 4 : ℝ) ^ m := by push_cast; ring
    linarith
  obtain ⟨σ, hσ⟩ := exists_lt_of_mean_lt (weight p) F
    (weight_nonneg hp hp') (sum_weight p) hmean
  let R := Finset.univ.filter fun a : α => σ a = true
  have hcount : ∀ v, (L v ∩ R).card = count (L v) σ := by
    intro v
    apply congrArg Finset.card
    ext a
    simp [R]
  refine ⟨R, ?_, ?_⟩
  · intro v hv
    rw [hcount]
    by_contra hn
    have hcm : count (L v) σ ≤ m := by omega
    have hpen : 1 ≤ lower v σ := by
      dsimp [lower]
      rw [one_div_pow, one_div, ← div_eq_mul_inv]
      apply (one_le_div (by positivity)).mpr
      exact pow_le_pow_right₀ (by norm_num) hcm
    have hterm : lower v σ ≤ F σ := by
      have h1 := Finset.single_le_sum
        (f := fun v => lower v σ) (s := X) (fun _ _ => by dsimp [lower]; positivity) hv
      have h2 : 0 ≤ ∑ v ∈ T, upper v σ := Finset.sum_nonneg
        (fun _ _ => by dsimp [upper]; positivity)
      dsimp [F]
      linarith
    linarith
  · intro v hv
    rw [hcount]
    by_contra hn
    have hcm : 4 * m ≤ count (L v) σ := by omega
    have hpen : 1 ≤ upper v σ := by
      dsimp [upper]
      apply (one_le_div (by positivity)).mpr
      exact pow_le_pow_right₀ (by norm_num) hcm
    have hterm : upper v σ ≤ F σ := by
      have h1 := Finset.single_le_sum
        (f := fun v => upper v σ) (s := T) (fun _ _ => by dsimp [upper]; positivity) hv
      have h2 : 0 ≤ ∑ v ∈ X, lower v σ := Finset.sum_nonneg
        (fun _ _ => by dsimp [lower]; positivity)
      dsimp [F]
      linarith
    linarith

end PaletteReservation

theorem choosable_iff_finite_colors {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    Choosable G k ↔ ∀ (Color : Type) [Fintype Color] (L : V → Finset Color),
      (∀ v, k ≤ (L v).card) → ListColorable G L := by
  classical
  constructor
  · intro h Color _ L hL
    exact h Color L hL
  · intro h Color L hL
    let C : Finset Color := Finset.univ.biUnion L
    have hc : ∀ v (c : ↥(L v)), c.val ∈ C := fun v c =>
      Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, c.property⟩
    let emb : ∀ v, ↥(L v) ↪ ↥C := fun v =>
      ⟨fun c => ⟨c.val, hc v c⟩, fun a b hab => Subtype.ext (congrArg (fun x : ↥C => x.val) hab)⟩
    let L' : V → Finset ↥C := fun v => (L v).attach.map (emb v)
    have hcard : ∀ v, (L' v).card = (L v).card := fun v => by simp [L']
    obtain ⟨c, hc', hp⟩ := h ↥C L' (fun v => by rw [hcard]; exact hL v)
    refine ⟨fun v => (c v).val, ?_, ?_⟩
    · intro v
      obtain ⟨a, _, heq⟩ := Finset.mem_map.mp (hc' v)
      have hh := congrArg Subtype.val heq
      change a.val = (c v).val at hh
      change (c v).val ∈ L v
      rw [← hh]
      exact a.property
    · intro v w hadj heq
      exact hp hadj (Subtype.ext heq)

lemma validOn_of_choosable {V Color : Type} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (L : V → Finset Color) (φ : V → Color)
    {k : ℕ} (h : Choosable (G.induce (↑S : Set V)) k)
    (hL : ∀ v ∈ S, k ≤ (L v).card) : ∃ c, ValidOn G S L c := by
  classical
  obtain ⟨c, hc, hp⟩ := h Color (fun v => L v.val) (fun v => hL v.val v.property)
  let c' : V → Color := fun v => if hv : v ∈ S then c ⟨v, hv⟩ else φ v
  refine ⟨c', ?_, ?_⟩
  · intro v hv
    simpa only [c', dite_eq_left hv] using hc ⟨v, hv⟩
  · intro v hv w hw hadj
    simpa only [c', dite_eq_left hv, dite_eq_left hw] using
      hp (v := ⟨v, hv⟩) (w := ⟨w, hw⟩) hadj

lemma ValidOn.glue {V Color : Type} [DecidableEq V]
    {G : SimpleGraph V} {S T : Finset V} {L : V → Finset Color} {c d : V → Color}
    (hc : ValidOn G S L c) (hd : ValidOn G T L d)
    (hst : Disjoint S T) (hcross : ∀ v ∈ S, ∀ w ∈ T, G.Adj v w → c v ≠ d w) :
    ValidOn G (S ∪ T) L (fun v => if v ∈ S then c v else d v) := by
  classical
  constructor
  · intro v hv
    by_cases hs : v ∈ S
    · simpa [hs] using hc.1 v hs
    · have ht : v ∈ T := (Finset.mem_union.mp hv).resolve_left hs
      simpa [hs] using hd.1 v ht
  · intro v hv w hw hadj
    by_cases hs : v ∈ S <;> by_cases hs' : w ∈ S
    · simpa only [ite_eq_left hs, ite_eq_left hs'] using hc.2 hs hs' hadj
    · have hwT := (Finset.mem_union.mp hw).resolve_left hs'
      simpa only [ite_eq_left hs, ite_eq_right (Finset.disjoint_right.mp hst hwT)] using
        hcross v hs w hwT hadj
    · simpa only [ite_eq_right hs, ite_eq_left hs'] using
        (hcross w hs' v ((Finset.mem_union.mp hv).resolve_left hs) hadj.symm).symm
    · simpa only [ite_eq_right hs, ite_eq_right hs'] using
        hd.2 ((Finset.mem_union.mp hv).resolve_left hs)
          ((Finset.mem_union.mp hw).resolve_left hs') hadj

noncomputable def prune {V Color : Type} (G : SimpleGraph V) (S : Finset V)
    (L : V → Finset Color) (c : V → Color) (v : V) : Finset Color :=
  L v \ (S.filter (G.Adj v)).image c

lemma prune_card_loss {V Color : Type} (G : SimpleGraph V) (S : Finset V)
    (L : V → Finset Color) (c : V → Color) (v : V) :
    (L v).card ≤ (prune G S L c v).card + (S.filter (G.Adj v)).card := by
  have hh := Finset.card_le_card_sdiff_add_card (s := L v)
    (t := (S.filter (G.Adj v)).image c)
  have hh' := Finset.card_image_le (s := S.filter (G.Adj v)) (f := c)
  dsimp [prune]
  omega

lemma prune_subset {V Color : Type} (G : SimpleGraph V) (S : Finset V)
    (L : V → Finset Color) (c : V → Color) (v : V) :
    prune G S L c v ⊆ L v := Finset.sdiff_subset

lemma prune_avoids {V Color : Type} {G : SimpleGraph V} {S : Finset V}
    {L : V → Finset Color} {c : V → Color} {v w : V} {a : Color}
    (ha : a ∈ prune G S L c w) (hv : v ∈ S) (hadj : G.Adj v w) : c v ≠ a := by
  intro heq
  exact (Finset.mem_sdiff.mp ha).2
    (Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hadj.symm⟩, heq⟩)

lemma prune_reserved_loss {V Color : Type} (G : SimpleGraph V) (S : Finset V)
    (L : V → Finset Color) (c : V → Color) (R : Finset Color)
    (hreserved : ∀ v ∈ S, c v ∈ R) (v : V) :
    (L v).card ≤ (prune G S L c v).card + (L v ∩ R).card := by
  classical
  have hsub : L v ∩ (S.filter (G.Adj v)).image c ⊆ L v ∩ R := by
    intro a ha
    obtain ⟨hla, hi⟩ := Finset.mem_inter.mp ha
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_inter.mpr ⟨hla, hreserved w (Finset.mem_filter.mp hw).1⟩
  have heq := Finset.card_sdiff_add_card_inter (L v) ((S.filter (G.Adj v)).image c)
  have hcard := Finset.card_le_card hsub
  dsimp [prune]
  omega

theorem additive_deletion_coloring {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X Y : Finset V) {t m d s : ℕ}
    (ht : 1 ≤ t) (hXY : Disjoint X Y)
    (hX : Choosable (G.induce (↑X : Set V)) m)
    (hY : DegenerateOn G Y (d * t))
    (hRY : ∀ v ∉ X ∪ Y, (Y.filter (G.Adj v)).card ≤ d * t)
    (hR : Choosable (G.induce (↑(Finset.univ \ (X ∪ Y)) : Set V)) s)
    (hsmall : ((X.card + (Finset.univ.filter
        (fun v => v ∉ X ∧ t ≤ (X.filter (G.Adj v)).card)).card : ℕ) : ℝ) *
        (3 / 4 : ℝ) ^ m < 1) :
    Choosable G (s + 4 * m + d * t + 5 * t) := by
  classical
  apply (choosable_iff_finite_colors G _).mpr
  intro Color _ L₀ hL₀
  let u := s + 4 * m + d * t + 5 * t
  have hu0 : 0 < u := by dsimp [u]; omega
  have hmu : 2 * m ≤ u := by dsimp [u]; omega
  have hex : ∀ v, ∃ L' ⊆ L₀ v, L'.card = u := fun v =>
    Finset.exists_subset_card_eq (hL₀ v)
  choose L hsub hcard using hex
  have hn : ∀ v, (L v).Nonempty := fun v => Finset.card_pos.mp (by rw [hcard]; exact hu0)
  choose φ hφ using hn
  let T := Finset.univ.filter fun v => v ∉ X ∧ t ≤ (X.filter (G.Adj v)).card
  obtain ⟨reserved, hresX, hresT⟩ := PaletteReservation.exists_reservation L X T
    hu0 hmu (fun v _ => hcard v) hsmall
  obtain ⟨cX, hcX⟩ := validOn_of_choosable G X (fun v => L v ∩ reserved) φ hX hresX
  have hcXL : ValidOn G X L cX :=
    ⟨fun v hv => (Finset.mem_inter.mp (hcX.1 v hv)).1, hcX.2⟩
  have hcXR : ∀ v ∈ X, cX v ∈ reserved :=
    fun v hv => (Finset.mem_inter.mp (hcX.1 v hv)).2
  let L₁ := prune G X L cX
  have hL₁ : ∀ v ∉ X, s + d * t + 4 * t ≤ (L₁ v).card := by
    intro v hv
    by_cases hT : v ∈ T
    · have hh := prune_reserved_loss G X L cX reserved hcXR v
      have hb := hresT v hT
      rw [hcard] at hh
      dsimp [u] at hh
      change _ ≤ (L₁ v).card + _ at hh
      omega
    · have hd : (X.filter (G.Adj v)).card < t := by
        have hh : ¬(v ∉ X ∧ t ≤ (X.filter (G.Adj v)).card) := by
          simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using hT
        exact lt_of_not_ge (fun hh' => hh ⟨hv, hh'⟩)
      have hh := prune_card_loss G X L cX v
      rw [hcard] at hh
      dsimp [u] at hh
      change _ ≤ (L₁ v).card + _ at hh
      omega
  have hYnotX : ∀ v ∈ Y, v ∉ X := fun v hv hx =>
    Finset.disjoint_left.mp hXY hx hv
  obtain ⟨cY, hcY⟩ := degenerate_coloring_on G Y L₁ φ hY (by
    intro v hv
    have hh := hL₁ v (hYnotX v hv)
    omega)
  have hcYL : ValidOn G Y L cY :=
    ⟨fun v hv => prune_subset G X L cX v (hcY.1 v hv), hcY.2⟩
  let cXY : V → Color := fun v => if v ∈ X then cX v else cY v
  have hcXY : ValidOn G (X ∪ Y) L cXY := hcXL.glue hcYL hXY
    (fun v hv w hw hadj => prune_avoids (hcY.1 w hw) hv hadj)
  let R := Finset.univ \ (X ∪ Y)
  let L₂ := prune G Y L₁ cY
  have hL₂ : ∀ v ∈ R, s ≤ (L₂ v).card := by
    intro v hv
    have hvXY : v ∉ X ∪ Y := (Finset.mem_sdiff.mp hv).2
    have hvX : v ∉ X := fun hx => hvXY (Finset.mem_union_left Y hx)
    have hh := hL₁ v hvX
    have hdrop := prune_card_loss G Y L₁ cY v
    have hdeg := hRY v hvXY
    change _ ≤ (L₂ v).card + _ at hdrop
    omega
  obtain ⟨cR, hcR⟩ := validOn_of_choosable G R L₂ φ hR hL₂
  have hcRL : ValidOn G R L cR :=
    ⟨fun v hv => prune_subset G X L cX v
      (prune_subset G Y L₁ cY v (hcR.1 v hv)), hcR.2⟩
  have hd : Disjoint (X ∪ Y) R := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (Finset.mem_sdiff.mp hw).2 hv
  have hcross : ∀ v ∈ X ∪ Y, ∀ w ∈ R, G.Adj v w → cXY v ≠ cR w := by
    intro v hv w hw hadj
    by_cases hvX : v ∈ X
    · dsimp [cXY]
      rw [ite_eq_left hvX]
      exact prune_avoids (prune_subset G Y L₁ cY w (hcR.1 w hw)) hvX hadj
    · have hvY : v ∈ Y := (Finset.mem_union.mp hv).resolve_left hvX
      dsimp [cXY]
      rw [ite_eq_right hvX]
      exact prune_avoids (hcR.1 w hw) hvY hadj
  have hfinal := hcXY.glue hcRL hd hcross
  have heq : (X ∪ Y) ∪ R = Finset.univ := by ext v; simp [R]
  rw [heq] at hfinal
  refine ⟨fun v => if v ∈ X ∪ Y then cXY v else cR v, ?_, ?_⟩
  · intro v
    exact hsub v (hfinal.1 v (Finset.mem_univ _))
  · intro v w hadj
    exact hfinal.2 (Finset.mem_univ _) (Finset.mem_univ _) hadj

theorem reservation_cutoff :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, ∀ m ≥ t, ∀ a b : ℕ,
      a ≤ t ^ 2 → b ≤ a.choose 2 →
      ((a + b : ℕ) : ℝ) * (3 / 4 : ℝ) ^ m < 1 := by
  have hlim := (tendsto_pow_const_mul_const_pow_of_lt_one 4
    (show (0 : ℝ) ≤ 3 / 4 by norm_num) (by norm_num)).const_mul 2
  have hev : ∀ᶠ t : ℕ in Filter.atTop,
      2 * ((t : ℝ) ^ 4 * (3 / 4 : ℝ) ^ t) < 1 := by
    exact hlim.eventually (p := fun x : ℝ => x < 1) (by
      simpa using (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)))
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max t₀ 1, ?_⟩
  intro t ht m hm a b ha hb
  have ht1 : 1 ≤ t := le_trans (le_max_right _ _) ht
  have htp : t ≤ t ^ 2 := by nlinarith
  have hap : a ≤ t ^ 4 := by nlinarith
  have hbp : b ≤ t ^ 4 := by
    have hh := Nat.choose_le_pow a 2
    have hh' : a ^ 2 ≤ (t ^ 2) ^ 2 := Nat.pow_le_pow_left ha 2
    nlinarith
  have hab : ((a + b : ℕ) : ℝ) ≤ 2 * (t : ℝ) ^ 4 := by
    exact_mod_cast (show a + b ≤ 2 * t ^ 4 by omega)
  have hp : (3 / 4 : ℝ) ^ m ≤ (3 / 4 : ℝ) ^ t :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
  calc
    ((a + b : ℕ) : ℝ) * (3 / 4 : ℝ) ^ m
      ≤ (2 * (t : ℝ) ^ 4) * (3 / 4 : ℝ) ^ t :=
        mul_le_mul hab hp (by positivity) (by positivity)
    _ = 2 * ((t : ℝ) ^ 4 * (3 / 4 : ℝ) ^ t) := by ring
    _ < 1 := ht₀ t ((le_max_left _ _).trans ht)

lemma small_order_le_square {a t : ℕ} (ht : 1 ≤ t)
    (ha : (a : ℝ) ≤ (t : ℝ) ^ (11 / 10 : ℝ)) : a ≤ t ^ 2 := by
  have hh := Real.rpow_le_rpow_of_exponent_le
    (show (1 : ℝ) ≤ t by exact_mod_cast ht) (show (11 / 10 : ℝ) ≤ (2 : ℕ) by norm_num)
  rw [Real.rpow_natCast] at hh
  exact_mod_cast ha.trans hh

theorem reservation_cutoff_minor :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (X : Finset V) (m : ℕ),
      t ≤ m → hadwigerNumber G < t →
      (X.card : ℝ) ≤ (t : ℝ) ^ (11 / 10 : ℝ) →
      ((X.card + (Finset.univ.filter
        (fun v => v ∉ X ∧ t ≤ (X.filter (G.Adj v)).card)).card : ℕ) : ℝ) *
          (3 / 4 : ℝ) ^ m < 1 := by
  obtain ⟨t₀, ht₀⟩ := reservation_cutoff
  refine ⟨max t₀ 2, ?_⟩
  intro t ht V _ _ G X m hm hminor hsize
  have ht2 : 2 ≤ t := (le_max_right _ _).trans ht
  exact ht₀ t ((le_max_left _ _).trans ht) m hm X.card _
    (small_order_le_square (by omega) hsize) (high_neighbor_count G ht2 hminor X)

end LinearListHadwiger

end OAI
