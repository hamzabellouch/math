import OAI.Combinatorics.TreeEdit.FiniteProbability
import OAI.Combinatorics.TreeEdit.CyclicWords
import OAI.Combinatorics.TreeEdit.TreeArithmetic

namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical

noncomputable def point (n : ℕ) : UnitAddCircle := ↑((n : ℝ)⁻¹)

lemma point_period {n : ℕ} (hn : 0 < n) : n • point n = 0 := by
  simp only [point, ← AddCircle.coe_nsmul, nsmul_eq_mul]
  rw [mul_inv_cancel₀ (by exact_mod_cast hn.ne')]
  exact AddCircle.coe_period (1 : ℝ)

lemma point_mul {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (h : d ∣ n) :
    (n / d) • point n = point d := by
  simp only [point, ← AddCircle.coe_nsmul, nsmul_eq_mul]
  congr 1
  rw [Nat.cast_div h (by exact_mod_cast hd.ne')]
  field_simp

lemma nsmul_point_eq (n a : ℕ) : a • point n = ↑((a : ℝ) / n) := by
  simp only [point, ← AddCircle.coe_nsmul, nsmul_eq_mul, div_eq_mul_inv]

lemma point_toAddCircle {n : ℕ} [NeZero n] (a : ZMod n) :
    a.val • point n = ZMod.toAddCircle a := by
  rw [nsmul_point_eq, ZMod.toAddCircle_apply]

lemma circle_period_lower {x : UnitAddCircle} {d : ℕ} (hd : 0 < d)
    (hx : d • x = 0) (hx0 : x ≠ 0) : 1 ≤ (d : ℝ) * ‖x‖ := by
  let : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have hf : IsOfFinAddOrder x := isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨d, hd, hx⟩
  have hh := AddCircle.le_add_order_smul_norm_of_isOfFinAddOrder hf hx0
  simp only [nsmul_eq_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast addOrderOf_le_of_nsmul_eq_zero hd hx) (norm_nonneg _))

lemma nearby_unique {t x y : UnitAddCircle} {d e K : ℕ} {ε : ℝ}
    (hd : 0 < d) (he : 0 < e) (hdK : d ≤ K) (heK : e ≤ K)
    (hx : d • x = 0) (hy : e • y = 0) (hε : 2 * ε * (K : ℝ) ^ 2 < 1)
    (htx : ‖t + x‖ < ε) (hty : ‖t + y‖ < ε) : x = y := by
  by_contra hn
  have hperiod : (d * e) • (x - y) = 0 := by
    rw [nsmul_sub]
    rw [show d * e = e * d by ring, mul_smul, hx, smul_zero,
      show e * d = d * e by ring, mul_smul, hy, smul_zero, sub_self]
  have hh := circle_period_lower (Nat.mul_pos hd he) hperiod (sub_ne_zero.mpr hn)
  have hnorm : ‖x - y‖ < 2 * ε := by
    calc
      _ = ‖(t + x) - (t + y)‖ := by congr 1; abel
      _ ≤ ‖t + x‖ + ‖t + y‖ := norm_sub_le _ _
      _ < _ := by linarith
  have hK : 0 < (K : ℝ) := by exact_mod_cast hd.trans_le hdK
  have hde : (d : ℝ) * e ≤ (K : ℝ) ^ 2 := by
    have hd' : (d : ℝ) ≤ K := by exact_mod_cast hdK
    have he' : (e : ℝ) ≤ K := by exact_mod_cast heK
    nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d), (Nat.cast_nonneg e : (0 : ℝ) ≤ e)]
  push_cast at hh
  have hh' := mul_le_mul_of_nonneg_right hde (norm_nonneg (x - y))
  have hh'' := mul_lt_mul_of_pos_left hnorm (sq_pos_of_pos hK)
  nlinarith

lemma grid_nearby_unique {r : ℕ} [NeZero r] {t : UnitAddCircle} {ε : ℝ}
    (hε : 2 * ε * (r : ℝ) < 1) {a b : ZMod r}
    (ha : ‖t + ZMod.toAddCircle a‖ < ε) (hb : ‖t + ZMod.toAddCircle b‖ < ε) : a = b := by
  apply ZMod.toAddCircle_injective r
  by_contra hn
  have hp : r • (ZMod.toAddCircle a - ZMod.toAddCircle b) = 0 := by
    rw [← map_sub, ← map_nsmul]
    simp [nsmul_eq_mul]
  have hh := circle_period_lower (NeZero.pos _) hp (sub_ne_zero.mpr hn)
  have hnorm : ‖ZMod.toAddCircle a - ZMod.toAddCircle b‖ < 2 * ε := by
    calc
      _ = ‖(t + ZMod.toAddCircle a) - (t + ZMod.toAddCircle b)‖ := by congr 1; abel
      _ ≤ ‖t + ZMod.toAddCircle a‖ + ‖t + ZMod.toAddCircle b‖ := norm_sub_le _ _
      _ < _ := by linarith
  have hr : (0 : ℝ) < r := by exact_mod_cast NeZero.pos r
  nlinarith

lemma product_positive {I : Type*} [Fintype I] (r : I → ℕ) (hr : ∀ i, 0 < r i) :
    0 < ∏ i, r i := Finset.prod_pos (fun i _ => hr i)

lemma sparse_order {I : Type*} [Fintype I] (r : I → ℕ)
    (hr : ∀ i, Nat.Prime (r i)) (hinj : Function.Injective r)
    {U k a : ℕ} (hU : 1 ≤ U) (hrU : ∀ i, r i ≤ U)
    (hcard : (Finset.univ.filter (fun i => ¬ r i ∣ a)).card ≤ k) :
    addOrderOf (a • point (∏ i, r i)) ≤ U ^ k := by
  let s := Finset.univ.filter (fun i => ¬ r i ∣ a)
  let t := Finset.univ.filter (fun i => r i ∣ a)
  let D := ∏ i ∈ s, r i
  let P := ∏ i, r i
  have hP : 0 < P := product_positive r (fun i => (hr i).pos)
  have hD : 0 < D := Finset.prod_pos (fun i _ => (hr i).pos)
  have ht : (∏ i ∈ t, r i) ∣ a := by
    have hcop : (↑t : Set I).Pairwise (fun i j => IsCoprime (r i : ℤ) (r j : ℤ)) := by
      intro i _ j _ hij
      exact ((Nat.coprime_primes (hr i) (hr j)).mpr (fun h => hij (hinj h))).isCoprime
    have hd : (∏ i ∈ t, (r i : ℤ)) ∣ (a : ℤ) := Finset.prod_dvd_of_coprime hcop
      (fun i hi => by exact_mod_cast (Finset.mem_filter.mp hi).2)
    exact_mod_cast hd
  have he : D * (∏ i ∈ t, r i) = P := by
    simpa [D, s, t, P] using Finset.prod_filter_mul_prod_filter_not (s := Finset.univ) (p := fun i => ¬ r i ∣ a) r
  have hPD : P ∣ D * a := by
    obtain ⟨b, hb⟩ := ht
    exact ⟨b, by rw [hb, ← he]; ring⟩
  have hz : D • (a • point P) = 0 := by
    rw [← mul_smul]
    obtain ⟨b, hb⟩ := hPD
    rw [hb, mul_smul, smul_comm, point_period hP, smul_zero]
  calc
    _ ≤ D := addOrderOf_le_of_nsmul_eq_zero hD hz
    _ ≤ U ^ s.card := by
      calc
        _ ≤ ∏ _i ∈ s, U := Finset.prod_le_prod (fun i _ => hrU i)
        _ = _ := Finset.prod_const U
    _ ≤ U ^ k := pow_le_pow_right₀ hU hcard

lemma sparse_bad_prime {t : UnitAddCircle} {ε : ℝ} {U k : ℕ}
    (ht : ε ≤ ‖t‖) (hε : 2 * ε * ((U ^ k : ℕ) : ℝ) ^ 2 < 1) :
    ∃ p : ℕ, Nat.Prime p ∧ ∀ {I : Type*} [Fintype I] (r : I → ℕ),
      (∀ i, Nat.Prime (r i)) → Function.Injective r → 1 ≤ U → (∀ i, r i ≤ U) →
      ∀ a : ℕ, (Finset.univ.filter (fun i => ¬ r i ∣ a)).card ≤ k →
        ‖t + a • point (∏ i, r i)‖ < ε → ∃ i, r i = p := by
  let E (x : UnitAddCircle) := IsOfFinAddOrder x ∧ addOrderOf x ≤ U ^ k ∧ ‖t + x‖ < ε
  by_cases hex : ∃ x, E x
  · obtain ⟨x, hxfin, hxK, hxnorm⟩ := hex
    have hx0 : x ≠ 0 := by intro hz; rw [hz, add_zero] at hxnorm; exact hxnorm.not_ge ht
    have ho : addOrderOf x ≠ 1 := by simpa using hx0
    let p := (addOrderOf x).minFac
    have hp : Nat.Prime p := Nat.minFac_prime ho
    refine ⟨p, hp, ?_⟩
    intro I _ r hr hi hU hrU a hcard hbad
    have hP : 0 < ∏ i, r i := product_positive r (fun i => (hr i).pos)
    have hyper : (∏ i, r i) • (a • point (∏ i, r i)) = 0 := by
      rw [smul_comm, point_period hP, smul_zero]
    have hyfin : IsOfFinAddOrder (a • point (∏ i, r i)) :=
      isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨_, hP, hyper⟩
    have hxy : x = a • point (∏ i, r i) := nearby_unique
      (addOrderOf_pos_iff.mpr hxfin) (addOrderOf_pos_iff.mpr hyfin)
      hxK (sparse_order r hr hi hU hrU hcard)
      (addOrderOf_nsmul_eq_zero x) (addOrderOf_nsmul_eq_zero _) hε hxnorm hbad
    have hdiv : p ∣ ∏ i, r i := (Nat.minFac_dvd _).trans
      (by rw [hxy]; exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hyper)
    obtain ⟨i, _, hpi⟩ := (hp.prime.dvd_finsetProd_iff r).mp hdiv
    exact ⟨i, ((hr i).eq_one_or_self_of_dvd p hpi).resolve_left hp.ne_one |>.symm⟩
  · refine ⟨2, Nat.prime_two, ?_⟩
    intro I _ r hr hi hU hrU a hcard hbad
    exfalso
    apply hex
    have hP : 0 < ∏ i, r i := product_positive r (fun i => (hr i).pos)
    refine ⟨a • point (∏ i, r i), ?_, sparse_order r hr hi hU hrU hcard, hbad⟩
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨_, hP, by rw [smul_comm, point_period hP, smul_zero]⟩

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability

lemma prime_list_event {I : Type*} [Fintype I] (r : I → ℕ)
    (hr : ∀ i, Nat.Prime (r i)) (hi : Function.Injective r)
    {U k g : ℕ} (hU : 1 ≤ U) (hrU : ∀ i, r i ≤ U) (j : Fin g ↪ I)
    {t : UnitAddCircle} {ε : ℝ} (ht : ε ≤ ‖t‖)
    (hε : 2 * ε * ((U ^ k : ℕ) : ℝ) ^ 2 < 1) :
    probability (fun σ : Equiv.Perm I => ¬ ∀ a : ℕ,
      (Finset.univ.filter (fun i => ¬ r (σ (j i)) ∣ a)).card ≤ k →
      ε ≤ ‖t + a • point (∏ i : Fin g, r (σ (j i)))‖) ≤
      (g : ℝ) / Fintype.card I := by
  obtain ⟨p, _, hp⟩ := sparse_bad_prime ht hε
  have himpl (σ : Equiv.Perm I) (hbad : ¬ ∀ a : ℕ,
      (Finset.univ.filter (fun i => ¬ r (σ (j i)) ∣ a)).card ≤ k →
      ε ≤ ‖t + a • point (∏ i : Fin g, r (σ (j i)))‖) :
      ∃ i : Fin g, r (σ (j i)) = p := by
    push Not at hbad
    obtain ⟨a, ha, hna⟩ := hbad
    exact hp (fun i : Fin g => r (σ (j i))) (fun _ => hr _) (hi.comp (σ.injective.comp j.injective))
      hU (fun _ => hrU _) a ha hna
  by_cases hex : ∃ v, r v = p
  · obtain ⟨v, hv⟩ := hex
    calc
      _ ≤ probability (fun σ : Equiv.Perm I => ∃ i : Fin g, σ (j i) = v) := probability_mono (by
        intro σ hσ
        obtain ⟨i, hh⟩ := himpl σ hσ
        exact ⟨i, hi (hh.trans hv.symm)⟩)
      _ ≤ _ := by simpa using permutation_avoidance j v
  · have hz : probability (fun σ : Equiv.Perm I => ¬ ∀ a : ℕ,
        (Finset.univ.filter (fun i => ¬ r (σ (j i)) ∣ a)).card ≤ k →
        ε ≤ ‖t + a • point (∏ i : Fin g, r (σ (j i)))‖) = 0 := by
      apply le_antisymm _ (probability_nonneg _)
      calc
        _ ≤ probability (fun _ : Equiv.Perm I => False) := probability_mono (by
          intro σ hσ
          obtain ⟨i, hh⟩ := himpl σ hσ
          exact hex ⟨_, hh⟩)
        _ = 0 := by simp [probability, mean]
    rw [hz]
    positivity

lemma dense_grid_bad {L r a : ℕ} [NeZero L] [NeZero r] (hr : Nat.Prime r) (hrL : r ∣ L)
    (ha : ¬ r ∣ a) {t : UnitAddCircle} {ε : ℝ} (hε : 2 * ε * r < 1) :
    probability (fun z : ZMod L =>
      ‖t + ZMod.toAddCircle ((a : ZMod r) * ZMod.castHom hrL (ZMod r) z)‖ < ε) ≤ (r : ℝ)⁻¹ := by
  let : Fact (Nat.Prime r) := ⟨hr⟩
  let f : ZMod L →+ ZMod r := (AddMonoidHom.mulLeft (a : ZMod r)).comp
    (ZMod.castHom hrL (ZMod r)).toAddMonoidHom
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨z, hz⟩ := ZMod.castHom_surjective hrL ((a : ZMod r)⁻¹ * b)
    refine ⟨z, ?_⟩
    change (a : ZMod r) * ZMod.castHom hrL (ZMod r) z = b
    rw [hz, ← mul_assoc, mul_inv_cancel₀ ((ZMod.natCast_eq_zero_iff a r).not.mpr ha), one_mul]
  calc
    _ = probability (fun b : ZMod r => ‖t + ZMod.toAddCircle b‖ < ε) :=
      probability_comp_uniform f (hom_uniform f hf) _
    _ ≤ (Fintype.card (ZMod r) : ℝ)⁻¹ := probability_subsingleton _ (fun _ _ => grid_nearby_unique hε)
    _ = _ := by rw [ZMod.card]

lemma dense_grid_eligible {L r a : ℕ} [NeZero L] [NeZero r] (hr : Nat.Prime r) (hrL : r ∣ L)
    (ha : ¬ r ∣ a) {t : UnitAddCircle} {ε : ℝ} (hε : 2 * ε * r < 1)
    (hr10 : 10 ≤ r) :
    9 / 10 ≤ probability (fun z : ZMod L =>
      ε ≤ ‖t + ZMod.toAddCircle ((a : ZMod r) * ZMod.castHom hrL (ZMod r) z)‖) := by
  have hh := dense_grid_bad (t := t) hr hrL ha hε
  have hn := probability_not (fun z : ZMod L =>
      ‖t + ZMod.toAddCircle ((a : ZMod r) * ZMod.castHom hrL (ZMod r) z)‖ < ε)
  simp only [not_lt] at hn
  rw [hn]
  have hi : (r : ℝ)⁻¹ ≤ (10 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by exact_mod_cast hr10)
  norm_num at hi
  linarith

lemma coefficient_circle {P r : ℕ} [NeZero r] (hP : 0 < P) (hr : 0 < r) (hd : r ∣ P)
    (a : ℕ) (z : ZMod r) :
    (a * (1 + z.val * (P / r))) • point P =
      a • point P + ZMod.toAddCircle ((a : ZMod r) * z) := by
  rw [Nat.mul_add, Nat.mul_one, add_smul]
  congr 1
  rw [mul_smul, mul_smul, point_mul hP hr hd, point_toAddCircle]
  rw [← map_nsmul]
  congr 1
  simp only [nsmul_eq_mul]

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability

def group {g s : ℕ} (i : Fin (g * s)) : Fin g := (finProdFinEquiv.symm i).1

lemma group_card {g s : ℕ} (S : Finset (Fin g)) :
    (Finset.univ.filter (fun i : Fin (g * s) => group i ∈ S)).card = S.card * s := by
  rw [Finset.card_filter, ← (finProdFinEquiv (m := g) (n := s)).sum_comp]
  simp only [group, Equiv.symm_apply_apply, Fintype.sum_prod_type]
  calc
    _ = ∑ x : Fin g, s * (if x ∈ S then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ S <;> simp [hx]
    _ = s * S.card := by rw [← Finset.mul_sum, Finset.sum_boole]; simp
    _ = _ := Nat.mul_comm _ _

@[reducible] def Config (I : Type) (L m : ℕ) : ℕ → Type _
  | 0 => Unit
  | h + 1 => Equiv.Perm I × (Fin m → ZMod L × Config I L m h)

noncomputable instance configFintype {I : Type} [Fintype I] {L m : ℕ} [NeZero L] (h : ℕ) :
    Fintype (Config I L m h) := by
  induction h with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ h ih => exact inferInstanceAs (Fintype (Equiv.Perm I × (Fin m → ZMod L × Config I L m h)))

instance configNonempty {I : Type} {L m : ℕ} (h : ℕ) : Nonempty (Config I L m h) := by
  induction h with
  | zero => exact inferInstanceAs (Nonempty Unit)
  | succ h ih => exact inferInstanceAs (Nonempty (Equiv.Perm I × (Fin m → ZMod L × Config I L m h)))

noncomputable def period {I : Type} {g : ℕ} (r : I → ℕ) (j : Fin g → I) (σ : Equiv.Perm I) : ℕ :=
  ∏ i, r (σ (j i))

noncomputable def coefficient {I : Type} {g s L : ℕ} (r : I → ℕ) (j : Fin g → I)
    (σ : Equiv.Perm I) (z : ZMod L) (i : Fin (g * s)) : ℕ :=
  1 + (z.val % r (σ (j (group i)))) * (period r j σ / r (σ (j (group i))))

noncomputable def Good {I : Type} {g s L : ℕ} (ε : ℝ) (r : I → ℕ) (j : Fin g → I) :
    (h : ℕ) → Config I L (g * s) h → UnitAddCircle → Prop
  | 0, _, t => ε ≤ ‖t‖
  | h + 1, C, t => ∀ a : Fin (period r j C.1), g * s ≤ 64 *
    (Finset.univ.filter (fun i : Fin (g * s) =>
      Good ε r j h (C.2 i).2 (t + (a.val * coefficient r j C.1 (C.2 i).1 i) • point (period r j C.1)))).card

lemma period_pos {I : Type} {g : ℕ} {r : I → ℕ} (hr : ∀ i, 0 < r i)
    (j : Fin g → I) (σ : Equiv.Perm I) : 0 < period r j σ := product_positive _ (fun _ => hr _)

lemma group_prime_dvd {I : Type} {g : ℕ} (r : I → ℕ) (j : Fin g → I)
    (σ : Equiv.Perm I) (v : Fin g) : r (σ (j v)) ∣ period r j σ :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ v)

lemma cast_hom_val {L r : ℕ} [NeZero L] (hrL : r ∣ L) (z : ZMod L) :
    ZMod.castHom hrL (ZMod r) z = (z.val : ZMod r) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val z]
  simp only [map_natCast]

lemma coefficient_shift {I : Type} [Fintype I] {g s : ℕ} (r : I → ℕ)
    (hr : ∀ i, 0 < r i) (j : Fin g → I) (σ : Equiv.Perm I)
    {L : ℕ} [NeZero L] (hL : ∀ i, r i ∣ L) (i : Fin (g * s))
    [NeZero (r (σ (j (group i))))] (a : ℕ) (z : ZMod L) :
    (a * coefficient r j σ z i) • point (period r j σ) =
      a • point (period r j σ) +
        ZMod.toAddCircle ((a : ZMod (r (σ (j (group i))))) *
          ZMod.castHom (hL _) (ZMod (r (σ (j (group i))))) z) := by
  have hv : (ZMod.castHom (hL _) (ZMod (r (σ (j (group i))))) z).val =
      z.val % r (σ (j (group i))) := by rw [cast_hom_val, ZMod.val_natCast]
  change (a * (1 + _ * _)) • _ = _
  rw [← hv]
  exact coefficient_circle (period_pos hr j σ) (hr _) (group_prime_dvd r j σ _) a _

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability

lemma fixed_residue_failure {I : Type} [Fintype I] {k s L h : ℕ} [NeZero L]
    (r : I → ℕ) (hr : ∀ i, Nat.Prime (r i)) (hr10 : ∀ i, 10 ≤ r i)
    (hL : ∀ i, r i ∣ L) (j : Fin (16 * k) ↪ I)
    {ε : ℝ} (hgrid : ∀ i, 2 * ε * r i < 1)
    (ih : ∀ t : UnitAddCircle, ε ≤ ‖t‖ → 9 / 10 ≤
      probability (fun C : Config I L (16 * k * s) h => Good ε r j h C t))
    (σ : Equiv.Perm I) (t : UnitAddCircle)
    (hlist : ∀ a : ℕ, (Finset.univ.filter (fun v : Fin (16 * k) => ¬ r (σ (j v)) ∣ a)).card ≤ k →
      ε ≤ ‖t + a • point (period r j σ)‖) (a : Fin (period r j σ)) :
    probability (fun C : Fin (16 * k * s) → ZMod L × Config I L (16 * k * s) h =>
      ¬ 16 * k * s ≤ 64 * (Finset.univ.filter (fun i =>
        Good ε r j h (C i).2 (t + (a.val * coefficient r j σ (C i).1 i) • point (period r j σ)))).card) ≤
      (4 / 5 : ℝ) ^ (k * s) := by
  let S := Finset.univ.filter (fun v : Fin (16 * k) => ¬ r (σ (j v)) ∣ a.val)
  let V := if S.card ≤ k then Sᶜ else S
  let J := Finset.univ.filter (fun i : Fin (16 * k * s) => group i ∈ V)
  let E (i : Fin (16 * k * s)) (C : ZMod L × Config I L (16 * k * s) h) : Prop :=
    Good ε r j h C.2 (t + (a.val * coefficient r j σ C.1 i) • point (period r j σ))
  have hn : k * s ≤ J.card := by
    have hv : k ≤ V.card := by
      dsimp [V]
      split_ifs with hs
      · rw [Finset.card_compl, Fintype.card_fin]
        omega
      · omega
    have hc := group_card (s := s) V
    exact (Nat.mul_le_mul_right s hv).trans_eq hc.symm
  have hE (i : Fin (16 * k * s)) (hi : i ∈ J) : 4 / 5 ≤ probability (E i) := by
    let p := r (σ (j (group i)))
    have hp : Nat.Prime p := hr _
    let : NeZero p := ⟨hp.ne_zero⟩
    have hg : group i ∈ V := (Finset.mem_filter.mp hi).2
    let sh (z : ZMod L) : UnitAddCircle := t + (a.val * coefficient r j σ z i) • point (period r j σ)
    have hsh (z : ZMod L) : sh z = t + a.val • point (period r j σ) +
        ZMod.toAddCircle ((a.val : ZMod p) * ZMod.castHom (hL _) (ZMod p) z) := by
      dsimp [sh]
      rw [coefficient_shift r (fun v => (hr v).pos) j σ hL i, ← add_assoc]
      simp only [ZMod.castHom_apply]
    have helig : 9 / 10 ≤ probability (fun z : ZMod L => ε ≤ ‖sh z‖) := by
      by_cases hs : S.card ≤ k
      · have hd : p ∣ a.val := by
          have hnot : group i ∉ S := Finset.mem_compl.mp (by simpa [V, hs] using hg)
          simpa [S, p] using hnot
        have he : ∀ z : ZMod L, ε ≤ ‖sh z‖ := by
          intro z
          rw [hsh, (ZMod.natCast_eq_zero_iff a.val p).mpr hd, zero_mul, map_zero, add_zero]
          exact hlist a.val hs
        have hh : probability (fun z : ZMod L => ε ≤ ‖sh z‖) = 1 := by simp [probability, he, mean_const]
        rw [hh]
        norm_num
      · have hd : ¬ p ∣ a.val := by
          have hin : group i ∈ S := by simpa [V, hs] using hg
          exact (Finset.mem_filter.mp hin).2
        have hh := dense_grid_eligible (t := t + a.val • point (period r j σ))
          hp (hL _) hd (hgrid _) (hr10 _)
        simpa only [hsh] using hh
    have hh := pair_success_lower (fun z : ZMod L => ε ≤ ‖sh z‖)
      (fun z (C : Config I L (16 * k * s) h) => Good ε r j h C (sh z))
      (p := (9 : ℝ) / 10) (fun z hz => ih (sh z) hz)
    change 9 / 10 * probability (fun z : ZMod L => ε ≤ ‖sh z‖) ≤ probability (E i) at hh
    nlinarith
  have hh := independent_lower_tail_subset E J hn hE
  calc
    _ ≤ probability (fun C : Fin (16 * k * s) → ZMod L × Config I L (16 * k * s) h =>
      4 * (Finset.univ.filter (fun i => E i (C i))).card < k * s) := probability_mono (by
        intro C hC
        change ¬ 16 * k * s ≤ 64 * (Finset.univ.filter (fun i => E i (C i))).card at hC
        have hh : 16 * k * s = 16 * (k * s) := by ring
        omega)
    _ ≤ _ := by
      convert hh using 1
      congr 1
      exact Subsingleton.elim _ _

lemma conditional_good_failure {I : Type} [Fintype I] {k s L U h : ℕ} [NeZero L]
    (r : I → ℕ) (hr : ∀ i, Nat.Prime (r i)) (hr10 : ∀ i, 10 ≤ r i)
    (hrU : ∀ i, r i ≤ U) (hL : ∀ i, r i ∣ L) (j : Fin (16 * k) ↪ I)
    {ε : ℝ} (hgrid : ∀ i, 2 * ε * r i < 1)
    (ih : ∀ t : UnitAddCircle, ε ≤ ‖t‖ → 9 / 10 ≤
      probability (fun C : Config I L (16 * k * s) h => Good ε r j h C t))
    (σ : Equiv.Perm I) (t : UnitAddCircle)
    (hlist : ∀ a : ℕ, (Finset.univ.filter (fun v : Fin (16 * k) => ¬ r (σ (j v)) ∣ a)).card ≤ k →
      ε ≤ ‖t + a • point (period r j σ)‖) :
    probability (fun C : Fin (16 * k * s) → ZMod L × Config I L (16 * k * s) h =>
      ¬ Good ε r j (h + 1) (σ, C) t) ≤ (U : ℝ) ^ (16 * k) * (4 / 5 : ℝ) ^ (k * s) := by
  let E (a : Fin (period r j σ)) (C : Fin (16 * k * s) → ZMod L × Config I L (16 * k * s) h) :=
    ¬ 16 * k * s ≤ 64 * (Finset.univ.filter (fun i =>
      Good ε r j h (C i).2 (t + (a.val * coefficient r j σ (C i).1 i) • point (period r j σ)))).card
  have he : (fun C : Fin (16 * k * s) → ZMod L × Config I L (16 * k * s) h =>
      ¬ Good ε r j (h + 1) (σ, C) t) = (fun C => ∃ a ∈ Finset.univ, E a C) := by
    funext C
    simp only [Good, E, Finset.mem_univ, true_and, not_forall]
  rw [he]
  calc
    _ ≤ ∑ a, probability (E a) := probability_union_bound Finset.univ E
    _ ≤ ∑ _a : Fin (period r j σ), (4 / 5 : ℝ) ^ (k * s) := Finset.sum_le_sum (fun a _ =>
      fixed_residue_failure r hr hr10 hL j hgrid ih σ t hlist a)
    _ = (period r j σ : ℝ) * (4 / 5 : ℝ) ^ (k * s) := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hP : period r j σ ≤ U ^ (16 * k) := by
        calc
          _ ≤ ∏ _v : Fin (16 * k), U := Finset.prod_le_prod (fun _ _ => hrU _)
          _ = _ := by simp
      exact_mod_cast hP

theorem good_probability {I : Type} [Fintype I] {k s L U : ℕ} [NeZero L]
    (r : I → ℕ) (hr : ∀ i, Nat.Prime (r i)) (hi : Function.Injective r)
    (hr10 : ∀ i, 10 ≤ r i) (hU : 1 ≤ U) (hrU : ∀ i, r i ≤ U)
    (hL : ∀ i, r i ∣ L) (j : Fin (16 * k) ↪ I)
    {ε : ℝ} (hgrid : ∀ i, 2 * ε * r i < 1)
    (hε : 2 * ε * ((U ^ k : ℕ) : ℝ) ^ 2 < 1)
    (herr : (16 * k : ℝ) / Fintype.card I + (U : ℝ) ^ (16 * k) * (4 / 5 : ℝ) ^ (k * s) ≤ 1 / 10)
    (h : ℕ) (t : UnitAddCircle) (ht : ε ≤ ‖t‖) :
    9 / 10 ≤ probability (fun C : Config I L (16 * k * s) h => Good ε r j h C t) := by
  induction h generalizing t with
  | zero => norm_num [Good, ht, probability, mean_const]
  | succ h ih =>
    let bad (σ : Equiv.Perm I) := ¬ ∀ a : ℕ,
      (Finset.univ.filter (fun v : Fin (16 * k) => ¬ r (σ (j v)) ∣ a)).card ≤ k →
      ε ≤ ‖t + a • point (period r j σ)‖
    have hbad : probability bad ≤ (16 * k : ℝ) / Fintype.card I := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, bad, period] using prime_list_event r hr hi hU hrU j ht hε
    have hh := pair_failure_bound bad (fun σ C => ¬ Good ε r j (h + 1) (σ, C) t)
      (δ := (U : ℝ) ^ (16 * k) * (4 / 5 : ℝ) ^ (k * s)) (by positivity)
      (fun σ hσ => conditional_good_failure r hr hr10 hrU hL j hgrid ih σ t (not_not.mp hσ))
    have he : probability (fun C : Config I L (16 * k * s) (h + 1) => ¬ Good ε r j (h + 1) C t) ≤ 1 / 10 := by
      exact hh.trans (by linarith)
    rw [probability_not] at he
    linarith

end TreeEdit.TorusTree

end OAI
