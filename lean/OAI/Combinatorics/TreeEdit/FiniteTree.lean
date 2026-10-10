import OAI.Combinatorics.TreeEdit.CyclicWords
import OAI.Combinatorics.TreeEdit.TreeArithmetic

namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

namespace FiniteTree

@[reducible] def State (m : ℕ) (p : ℕ → Fin m → ℕ) : ℕ → ℕ → Type
  | 0, q => ZMod q
  | h + 1, q => ∀ i : Fin m, State m p h (q * p h i)

noncomputable instance stateAddCommGroup (m : ℕ) (p : ℕ → Fin m → ℕ) (h q : ℕ) :
    AddCommGroup (State m p h q) := by
  induction h generalizing q with
  | zero => exact inferInstanceAs (AddCommGroup (ZMod q))
  | succ h ih =>
    letI : ∀ i : Fin m, AddCommGroup (State m p h (q * p h i)) := fun i => ih _
    exact inferInstanceAs (AddCommGroup (∀ i : Fin m, State m p h (q * p h i)))

@[reducible] def Symbol (m : ℕ) (p : ℕ → Fin m → ℕ) : ℕ → ℕ → Type
  | 0, q => ZMod q
  | h + 1, q => Σ i : Fin m, Symbol m p h (q * p h i)

@[instance_reducible] noncomputable def stateFintype {m : ℕ} (p : ℕ → Fin m → ℕ) (hp : ∀ h i, 0 < p h i)
    (h q : ℕ) (hq : 0 < q) : Fintype (State m p h q) := by
  induction h generalizing q with
  | zero =>
    letI : NeZero q := ⟨ne_of_gt hq⟩
    exact inferInstanceAs (Fintype (ZMod q))
  | succ h ih =>
    letI : ∀ i : Fin m, Fintype (State m p h (q * p h i)) := fun i =>
      ih _ (Nat.mul_pos hq (hp h i))
    exact inferInstanceAs (Fintype (∀ i : Fin m, State m p h (q * p h i)))

@[instance_reducible] noncomputable def symbolFintype {m : ℕ} (p : ℕ → Fin m → ℕ) (hp : ∀ h i, 0 < p h i)
    (h q : ℕ) (hq : 0 < q) : Fintype (Symbol m p h q) := by
  induction h generalizing q with
  | zero =>
    letI : NeZero q := ⟨ne_of_gt hq⟩
    exact inferInstanceAs (Fintype (ZMod q))
  | succ h ih =>
    letI : ∀ i : Fin m, Fintype (Symbol m p h (q * p h i)) := fun i =>
      ih _ (Nat.mul_pos hq (hp h i))
    exact inferInstanceAs (Fintype (Σ i : Fin m, Symbol m p h (q * p h i)))

noncomputable def w {m : ℕ} (p : ℕ → Fin m → ℕ) : (h q : ℕ) → State m p h q
  | 0, q => (1 : ZMod q)
  | h + 1, q => (∏ i : Fin m, p h i) • (fun i => w p h (q * p h i))

noncomputable def u {m : ℕ} (p : ℕ → Fin m → ℕ) (h q : ℕ) : State m p (h + 1) q :=
  fun i => w p h (q * p h i)

noncomputable def word {m : ℕ} (p : ℕ → Fin m → ℕ) (T : ℕ) :
    (h q : ℕ) → State m p h q → Word (Symbol m p h q) (length m T h)
  | 0, _, x => Words.ofFn (fun _ => x)
  | h + 1, q, x => Words.cycles fun a i =>
      word p T h (q * p h i) (x i + a.val • w p h (q * p h i))

lemma many_shifted_children {m b s T q : ℕ} (p : Fin m → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (hb : 1 ≤ b) (hpb : ∀ i, b ≤ p i) (hT : T ≤ b ^ s) (hsm : 2 * s ≤ m)
    (hcop : Nat.Coprime q (∏ i, p i))
    (t d : ℤ) (ht : ¬ (q : ℤ) ∣ t) (hdT : d.natAbs < T) :
    s ≤ (Finset.univ.filter (fun i => ¬ ((q * p i : ℕ) : ℤ) ∣
      d + t * (∏ j, p j : ℕ))).card := by
  classical
  let R := ∏ j, p j
  let bad := Finset.univ.filter (fun i => ((q * p i : ℕ) : ℤ) ∣ d + t * R)
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m))) (fun i => ((q * p i : ℕ) : ℤ) ∣ d + t * R)
  simp only [Finset.card_univ, Fintype.card_fin] at hpartition
  by_cases hd : d = 0
  · have he : bad = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hh := (Finset.mem_filter.mp hi).2
      have hq : (q : ℤ) ∣ t * R := by
        apply dvd_trans (show (q : ℤ) ∣ ((q * p i : ℕ) : ℤ) by
          exact_mod_cast dvd_mul_right q (p i))
        simpa only [hd, zero_add] using hh
      exact ht (hcop.isCoprime.dvd_of_dvd_mul_right hq)
    have hz : bad.card = 0 := by rw [he]; rfl
    change bad.card + _ = m at hpartition
    change s ≤ (Finset.univ.filter (fun i => ¬ ((q * p i : ℕ) : ℤ) ∣ d + t * R)).card
    omega
  · have hsub : bad ⊆ Finset.univ.filter (fun i => (p i : ℤ) ∣ d) := by
      intro i hi
      have hpR : (p i : ℤ) ∣ (R : ℤ) := by
        exact_mod_cast Finset.dvd_prod_of_mem p (Finset.mem_univ i)
      have hh : (p i : ℤ) ∣ d + t * R := by
        apply dvd_trans (show (p i : ℤ) ∣ ((q * p i : ℕ) : ℤ) by
          exact_mod_cast dvd_mul_left (p i) q)
        exact (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        by simpa using dvd_sub hh (dvd_mul_of_dvd_right hpR t)⟩
    have hlt := (Finset.card_le_card hsub).trans_lt (few_prime_divisors p hp hinj hb hpb hT d hd hdT)
    change bad.card + _ = m at hpartition
    change s ≤ (Finset.univ.filter (fun i => ¬ ((q * p i : ℕ) : ℤ) ∣ d + t * R)).card
    omega

structure Admissible {m : ℕ} (p : ℕ → Fin m → ℕ) (b h q : ℕ) : Prop where
  prime : ∀ j, j < h → ∀ i, Nat.Prime (p j i)
  lower : ∀ j, j < h → ∀ i, b ≤ p j i
  distinct : ∀ j, j < h → ∀ l, l < h → ∀ i i',
    p j i = p l i' → j = l ∧ i = i'
  coprime : ∀ j, j < h → ∀ i, Nat.Coprime q (p j i)

lemma Admissible.child {m b h q : ℕ} {p : ℕ → Fin m → ℕ}
    (H : Admissible p b (h + 1) q) (i : Fin m) : Admissible p b h (q * p h i) where
  prime j hj := H.prime j (by omega)
  lower j hj := H.lower j (by omega)
  distinct j hj l hl := H.distinct j (by omega) l (by omega)
  coprime j hj i' := (H.coprime j (by omega) i').mul_left
    ((Nat.coprime_primes (H.prime h (by omega) i) (H.prime j (by omega) i')).mpr (by
      intro he
      have hh := (H.distinct h (by omega) j (by omega) i i' he).1
      omega))

lemma Admissible.many {m b h q s T : ℕ} {p : ℕ → Fin m → ℕ}
    (H : Admissible p b (h + 1) q)
    (hb : 1 ≤ b) (hT : T ≤ b ^ s) (hsm : 2 * s ≤ m)
    (t : ℤ) (ht : ¬ (q : ℤ) ∣ t) (a a' : Fin T) :
    s ≤ (Finset.univ.filter (fun i => ¬ ((q * p h i : ℕ) : ℤ) ∣
      (a'.val : ℤ) - a.val + t * (∏ j, p h j : ℕ))).card := by
  apply many_shifted_children (p h) (H.prime h (by omega))
    (fun i j he => (H.distinct h (by omega) h (by omega) i j he).2)
    hb (H.lower h (by omega)) hT hsm
    (Nat.Coprime.prod_right (fun i _ => H.coprime h (by omega) i)) t _ ht
  rw [← Int.ofNat_lt]
  rw [Int.natCast_natAbs]
  have ha := a.isLt
  have ha' := a'.isLt
  rw [abs_lt]
  constructor <;> omega

theorem separation {m T b s h q : ℕ} {p : ℕ → Fin m → ℕ}
    (hm : m = 2 * s) (hs : 2 ≤ s) (hT0 : 0 < T) (hb : 1 ≤ b)
    (hT : T ≤ b ^ s) (H : Admissible p b h q)
    (x : State m p h q) (t : ℤ) (ht : ¬ (q : ℤ) ∣ t) :
    (length m T h : ℝ) ≤ (4 : ℝ) ^ h *
      (deficit (word p T h q x).val (word p T h q (x + t • w p h q)).val : ℝ) := by
  induction h generalizing q t with
  | zero =>
    let y : ZMod q := x
    have hne : y ≠ y + t • (1 : ZMod q) := by
      intro he
      have hz : t • (1 : ZMod q) = 0 := add_left_cancel (he.symm.trans (add_zero y).symm)
      have hh : (t : ZMod q) = 0 := by simpa only [zsmul_eq_mul, mul_one] using hz
      exact ht ((ZMod.intCast_zmod_eq_zero_iff_dvd t q).mp hh)
    have hw (z : State m p 0 q) : (word p T 0 q z).val = [z] := by
      change List.ofFn (fun _ : Fin 1 => z) = [z]
      simp [List.ofFn_succ]
    have hne' : x ≠ x + t • w p 0 q := hne
    rw [hw x, hw (x + t • w p 0 q), deficit_singleton hne']
    norm_num [length]
  | succ h ih =>
    have hm4 : 4 ≤ m := by omega
    let B := length m T h
    have hB : 0 < B := by dsimp [B]; rw [length_eq]; positivity
    let X : Fin T → ∀ i : Fin m, Word (Symbol m p h (q * p h i)) B :=
      fun a i => word p T h (q * p h i) (x i + a.val • w p h (q * p h i))
    let Y : Fin T → ∀ i : Fin m, Word (Symbol m p h (q * p h i)) B :=
      fun a i => word p T h (q * p h i) ((x + t • w p (h + 1) q) i +
        a.val • w p h (q * p h i))
    let δ : ℝ := (s : ℝ) * B / (4 : ℝ) ^ h
    have hpow : 0 < (4 : ℝ) ^ h := by positivity
    have hpow1 : 1 ≤ (4 : ℝ) ^ h := one_le_pow₀ (by norm_num)
    have hδ : δ ≤ ((m - 2) * B : ℕ) := by
      have hs' : (s : ℝ) ≤ (m - 2 : ℕ) := by exact_mod_cast (show s ≤ m - 2 by omega)
      have hB' : (0 : ℝ) ≤ B := Nat.cast_nonneg _
      dsimp [δ]
      rw [div_le_iff₀ hpow]
      push_cast
      calc
        (s : ℝ) * B ≤ (m - 2 : ℕ) * (B : ℝ) := mul_le_mul_of_nonneg_right hs' hB'
        _ ≤ ((m - 2 : ℕ) : ℝ) * B * 4 ^ h := le_mul_of_one_le_right (by positivity) hpow1
    have hblocks (a a' : Fin T) : δ ≤ ∑ i : Fin m, (deficit (X a i).val (Y a' i).val : ℝ) := by
      let d : ℤ := (a'.val : ℤ) - a.val + t * (∏ j, p h j : ℕ)
      let good := Finset.univ.filter (fun i : Fin m => ¬ ((q * p h i : ℕ) : ℤ) ∣ d)
      have hgood : s ≤ good.card := H.many hb hT (by omega) t ht a a'
      have hlocal (i : Fin m) (hi : i ∈ good) :
          (B : ℝ) ≤ (4 : ℝ) ^ h * (deficit (X a i).val (Y a' i).val : ℝ) := by
        have hi' : ¬ ((q * p h i : ℕ) : ℤ) ∣ d := (Finset.mem_filter.mp hi).2
        have hh := ih (H.child i) (x i + a.val • w p h (q * p h i)) d hi'
        have he : (x + t • w p (h + 1) q) i + a'.val • w p h (q * p h i) =
            (x i + a.val • w p h (q * p h i)) + d • w p h (q * p h i) := by
          change x i + t • ((∏ j, p h j) • w p h (q * p h i)) +
            a'.val • w p h (q * p h i) = _
          exact translation_cycle _ _ _ _ _ _
        change (B : ℝ) ≤ (4 : ℝ) ^ h * (deficit
          (word p T h (q * p h i) (x i + a.val • w p h (q * p h i))).val
          (word p T h (q * p h i) ((x + t • w p (h + 1) q) i +
            a'.val • w p h (q * p h i))).val : ℝ)
        rw [he]
        exact hh
      have hsum := Finset.sum_le_sum (s := good) hlocal
      simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hsum
      have hsub : (∑ i ∈ good, (deficit (X a i).val (Y a' i).val : ℝ)) ≤
          ∑ i : Fin m, (deficit (X a i).val (Y a' i).val : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.cast_nonneg _)
      have hgood' : (s : ℝ) ≤ good.card := by exact_mod_cast hgood
      apply (div_le_iff₀ hpow).mpr
      nlinarith [mul_le_mul_of_nonneg_right hgood' (Nat.cast_nonneg B),
        mul_le_mul_of_nonneg_left hsub (le_of_lt hpow)]
    have hh := Words.cycles_deficit (by omega) hB X Y δ hδ hblocks
    change (T : ℝ) * δ ≤ 2 *
      (deficit (word p T (h + 1) q x).val (word p T (h + 1) q (x + t • w p (h + 1) q)).val : ℝ) at hh
    have hh' := mul_le_mul_of_nonneg_right hh (le_of_lt hpow)
    dsimp [δ] at hh'
    rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hpow)] at hh'
    simp only [length, Nat.cast_mul, pow_succ]
    have hm' : (m : ℝ) = 2 * s := by exact_mod_cast hm
    change (T : ℝ) * ((m : ℝ) * B) ≤ _
    rw [hm']
    nlinarith only [hh']

end FiniteTree

end TreeEdit

end OAI
