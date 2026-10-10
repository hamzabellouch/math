import OAI.Computability.StarHeight.RobustClock

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uAlphabet uAlphabet2 uM

namespace LocalMarkers

variable {Alphabet : Type uAlphabet} {K d : ℕ}

def Period (v : Fin K → Alphabet) (a : ℕ) : Prop :=
  ∀ i j : Fin K, i.val + a = j.val → v i = v j

def Aperiodic (d : ℕ) (v : Fin K → Alphabet) : Prop :=
  ∀ a, 0 < a → a < d → ¬ Period v a

def Occurs (w : ℤ → Alphabet) (v : Fin K → Alphabet) (x : ℤ) : Prop :=
  ∀ i : Fin K, w (x + i.val) = v i

def markers (d : ℕ) (w : ℤ → Alphabet) : List (Fin K → Alphabet) → Set ℤ
  | [] => ∅
  | v :: vs => markers d w vs ∪
      {x | Occurs w v x ∧ ∀ y ∈ markers d w vs, (d : ℤ) ≤ |x - y|}

lemma overlap_period {w : ℤ → Alphabet} {v : Fin K → Alphabet} {x y : ℤ}
    (hx : Occurs w v x) (hy : Occurs w v y) (hxy : x < y) :
    Period v (y - x).toNat := by
  intro i j hij
  have hn : ((y - x).toNat : ℤ) = y - x := Int.toNat_of_nonneg (by omega)
  have he : x + j.val = y + i.val := by omega
  rw [← hx j, he, hy i]

lemma occurrence_separated {w : ℤ → Alphabet} {v : Fin K → Alphabet} (hv : Aperiodic d v)
    {x y : ℤ} (hx : Occurs w v x) (hy : Occurs w v y) (hne : x ≠ y) :
    (d : ℤ) ≤ |x - y| := by
  by_contra hn
  have hsmall : |x - y| < (d : ℤ) := lt_of_not_ge hn
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · have hp := overlap_period hx hy hxy
    have hcast : ((y - x).toNat : ℤ) = y - x := Int.toNat_of_nonneg (by omega)
    have habs : |x - y| = y - x := abs_of_neg (by omega) |>.trans (by omega)
    exact hv _ (by omega) (by omega) hp
  · have hp := overlap_period hy hx hyx
    have hcast : ((x - y).toNat : ℤ) = x - y := Int.toNat_of_nonneg (by omega)
    have habs : |x - y| = x - y := abs_of_pos (by omega)
    exact hv _ (by omega) (by omega) hp

lemma separated (vs : List (Fin K → Alphabet)) (hv : ∀ v ∈ vs, Aperiodic d v)
    (w : ℤ → Alphabet) : ∀ x ∈ markers d w vs, ∀ y ∈ markers d w vs,
      x ≠ y → (d : ℤ) ≤ |x - y| := by
  induction vs with
  | nil => simp [markers]
  | cons v vs ih =>
    have hi := ih (fun u hu => hv u (List.mem_cons_of_mem _ hu))
    intro x hx y hy hne
    rcases hx with hx | ⟨hx, hxold⟩ <;> rcases hy with hy | ⟨hy, hyold⟩
    · exact hi x hx y hy hne
    · simpa only [abs_sub_comm] using hyold x hx
    · exact hxold y hy
    · exact occurrence_separated (hv v (List.mem_cons_self)) hx hy hne

lemma occurrence_near (hd : 0 < d) (vs : List (Fin K → Alphabet)) (w : ℤ → Alphabet)
    {v : Fin K → Alphabet} (hv : v ∈ vs) {x : ℤ} (hx : Occurs w v x) :
    ∃ y ∈ markers d w vs, |x - y| < (d : ℤ) := by
  induction vs with
  | nil => simp at hv
  | cons u vs ih =>
    classical
    rcases List.mem_cons.mp hv with rfl | hv
    · by_cases h : ∃ y ∈ markers d w vs, |x - y| < (d : ℤ)
      · obtain ⟨y, hy, hdist⟩ := h
        exact ⟨y, Or.inl hy, hdist⟩
      · refine ⟨x, Or.inr ⟨hx, ?_⟩, ?_⟩
        · intro y hy
          exact le_of_not_gt (fun hlt => h ⟨y, hy, hlt⟩)
        · simpa using hd
    · obtain ⟨y, hy, hdist⟩ := ih hv
      exact ⟨y, Or.inl hy, hdist⟩

def radius (d K : ℕ) (n : ℕ) : ℤ := (K : ℤ) + n * ((d : ℤ) - 1)

lemma radius_ge (hd : 0 < d) (n : ℕ) : (K : ℤ) ≤ radius d K n := by
  have hm : 0 ≤ (n : ℤ) * ((d : ℤ) - 1) := mul_nonneg (by omega) (by omega)
  unfold radius
  omega

lemma locality (hd : 0 < d) (hK : 0 < K) (vs : List (Fin K → Alphabet)) (w w' : ℤ → Alphabet)
    (x : ℤ) (hw : ∀ i, x - radius d K vs.length ≤ i →
      i < x + radius d K vs.length → w i = w' i) :
    x ∈ markers d w vs ↔ x ∈ markers d w' vs := by
  induction vs generalizing x with
  | nil => simp [markers]
  | cons v vs ih =>
    have hr : radius d K (v :: vs).length = radius d K vs.length + (d : ℤ) - 1 := by
      simp only [radius, List.length_cons, Nat.cast_add, Nat.cast_one]
      ring
    have hk := radius_ge (K := K) hd vs.length
    have hold (y : ℤ) (hy : |x - y| < (d : ℤ)) :
        y ∈ markers d w vs ↔ y ∈ markers d w' vs := by
      apply ih
      intro i hi hi'
      have hxy := abs_lt.mp hy
      apply hw i <;> rw [hr] <;> omega
    have hxold : x ∈ markers d w vs ↔ x ∈ markers d w' vs :=
      hold x (by simpa using hd)
    have hoc : Occurs w v x ↔ Occurs w' v x := by
      apply forall_congr'
      intro i
      have he := hw (x + i.val) (by rw [hr]; omega) (by rw [hr]; omega)
      rw [he]
    have hnear : (∀ y ∈ markers d w vs, (d : ℤ) ≤ |x - y|) ↔
        (∀ y ∈ markers d w' vs, (d : ℤ) ≤ |x - y|) := by
      constructor <;> intro h y hy <;> by_contra hn
      · exact hn (h y ((hold y (lt_of_not_ge hn)).mpr hy))
      · exact hn (h y ((hold y (lt_of_not_ge hn)).mp hy))
    exact or_congr hxold (and_congr hoc hnear)

lemma translate (vs : List (Fin K → Alphabet)) (w : ℤ → Alphabet) (a x : ℤ) :
    x ∈ markers d (fun i => w (i + a)) vs ↔ x + a ∈ markers d w vs := by
  induction vs generalizing x with
  | nil => simp [markers]
  | cons v vs ih =>
    have hoc : Occurs (fun i => w (i + a)) v x ↔ Occurs w v (x + a) := by
      unfold Occurs
      apply forall_congr'
      intro i
      have he : x + i.val + a = x + a + i.val := by omega
      dsimp only
      rw [he]
    have hn : (∀ y ∈ markers d (fun i => w (i + a)) vs, (d : ℤ) ≤ |x - y|) ↔
        (∀ y ∈ markers d w vs, (d : ℤ) ≤ |x + a - y|) := by
      constructor
      · intro h y hy
        have he : x - (y - a) = x + a - y := by omega
        exact he ▸ h (y - a) ((ih (y - a)).mpr (by simpa using hy))
      · intro h y hy
        have he : x + a - (y + a) = x - y := by omega
        exact he ▸ h (y + a) ((ih y).mp hy)
    exact or_congr (ih x) (and_congr hoc hn)

noncomputable def priorityList [Fintype Alphabet] (d K : ℕ) : List (Fin K → Alphabet) := by
  classical
  exact (Finset.univ.filter (Aperiodic d)).toList

lemma mem_priorityList [Fintype Alphabet] (v : Fin K → Alphabet) :
    v ∈ priorityList d K ↔ Aperiodic d v := by
  classical
  simp [priorityList]

theorem exists_markers [Fintype Alphabet] (hd : 2 ≤ d) (hK : 3 * d ^ 2 < K) :
    ∃ r : ℤ, (K : ℤ) ≤ r ∧ ∃ rule : (ℤ → Alphabet) → Set ℤ,
      (∀ w x, x ∈ rule w → ∀ y, y ∈ rule w → x ≠ y → (d : ℤ) ≤ |x - y|) ∧
      (∀ w w' x, (∀ i, x - r ≤ i → i < x + r → w i = w' i) →
        (x ∈ rule w ↔ x ∈ rule w')) ∧
      (∀ w a x, x ∈ rule (fun i => w (i + a)) ↔ x + a ∈ rule w) ∧
      (∀ w (z : ℤ), (∀ x : ℤ, z - d ≤ x → x ≤ z + d → x ∉ rule w) →
        ∃ a : ℕ, 0 < a ∧ a < d ∧ Period (fun i : Fin K => w (z + i.val)) a) := by
  classical
  let vs := priorityList (Alphabet := Alphabet) d K
  have hd0 : 0 < d := by omega
  have hK0 : 0 < K := by omega
  refine ⟨radius d K vs.length, radius_ge hd0 _, (fun w => markers d w vs), ?_, ?_, ?_, ?_⟩
  · exact fun w => separated vs (fun v hv => mem_priorityList v |>.mp hv) w
  · exact fun w w' x hw => locality hd0 hK0 vs w w' x hw
  · exact fun w a x => translate vs w a x
  · intro w z hz
    by_contra hn
    have hv : Aperiodic d (fun i : Fin K => w (z + i.val)) := by
      intro a ha had hp
      exact hn ⟨a, ha, had, hp⟩
    obtain ⟨x, hx, hdist⟩ := occurrence_near hd0 vs w
      ((mem_priorityList _).mpr hv) (fun _ => rfl)
    have hb := abs_lt.mp hdist
    exact hz x (by omega) (by omega) hx

end LocalMarkers

namespace LocalMarkers

variable {Alphabet : Type uAlphabet2} {K : ℕ}

lemma periodic_remainder {w : ℤ → Alphabet} {a : ℤ} (hw : Function.Periodic w a)
    (z x : ℤ) : w x = w (z + (x - z) % a) := by
  have he := Int.emod_add_mul_ediv (x - z) a
  have hx : x = z + (x - z) % a + ((x - z) / a) * a := by
    rw [mul_comm] at he
    omega
  calc
    w x = w (z + (x - z) % a + ((x - z) / a) * a) := congrArg w hx
    _ = w (z + (x - z) % a) := hw.int_mul ((x - z) / a) _

lemma periodic_agree {w w' : ℤ → Alphabet} {a b : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hw : Function.Periodic w a)
    (hw' : Function.Periodic w' b) (z : ℤ)
    (he : ∀ i : ℤ, z ≤ i → i < z + a * b → w i = w' i) : w = w' := by
  have hp : Function.Periodic w (a * b) := by simpa [mul_comm] using hw.int_mul b
  have hp' : Function.Periodic w' (a * b) := by simpa using hw'.int_mul a
  funext x
  rw [periodic_remainder hp z x, periodic_remainder hp' z x]
  have h₀ := Int.emod_nonneg (x - z) (ne_of_gt (mul_pos ha hb))
  have h₁ := Int.emod_lt_of_pos (x - z) (mul_pos ha hb)
  exact he _ (by omega) (by omega)

lemma period_mod {v : Fin K → Alphabet} {a : ℕ} (ha : 0 < a) (haK : a ≤ K)
    (hp : Period v a) (i : Fin K) :
    v i = v ⟨i.val % a, (Nat.mod_lt _ ha).trans_le haK⟩ := by
  have aux (n : ℕ) : ∀ hn : n < K,
      v ⟨n, hn⟩ = v ⟨n % a, (Nat.mod_lt _ ha).trans_le haK⟩ := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hna : n < a
      · congr 1
        apply Fin.ext
        exact (Nat.mod_eq_of_lt hna).symm
      · have hle : a ≤ n := Nat.le_of_not_gt hna
        have hsub : n - a < n := Nat.sub_lt (by omega) ha
        have hsubK : n - a < K := hsub.trans hn
        have he := hp ⟨n - a, hsubK⟩ ⟨n, hn⟩ (by simpa using Nat.sub_add_cancel hle)
        have hm : (n - a) % a = n % a := by
          conv_rhs => rw [← Nat.sub_add_cancel hle]
          exact (Nat.add_mod_right (n - a) a).symm
        rw [← he, ih (n - a) hsub hsubK]
        congr 1
        exact Fin.ext hm
  exact aux i.val i.isLt

noncomputable def continuation (v : Fin K → Alphabet) (z : ℤ) (a : ℕ)
    (ha : 0 < a) (haK : a ≤ K) : ℤ → Alphabet := fun x =>
  v ⟨((x - z) % (a : ℤ)).toNat, by
    have h₀ := Int.emod_nonneg (x - z) (by omega : (a : ℤ) ≠ 0)
    have h₁ := Int.emod_lt_of_pos (x - z) (by omega : 0 < (a : ℤ))
    have hcast := Int.toNat_of_nonneg h₀
    omega⟩

lemma continuation_periodic (v : Fin K → Alphabet) (z : ℤ) (a : ℕ)
    (ha : 0 < a) (haK : a ≤ K) :
    Function.Periodic (continuation v z a ha haK) (a : ℤ) := by
  intro x
  unfold continuation
  congr 2
  have he : x + (a : ℤ) - z = (x - z) + a := by omega
  rw [he, Int.add_emod_right]

lemma continuation_agrees {v : Fin K → Alphabet} (z : ℤ) {a : ℕ}
    (ha : 0 < a) (haK : a ≤ K) (hp : Period v a) (i : Fin K) :
    continuation v z a ha haK (z + i.val) = v i := by
  rw [period_mod ha haK hp i]
  unfold continuation
  congr 2
  simp only [add_sub_cancel_left]
  rw [← Int.natCast_emod, Int.toNat_natCast]

lemma exists_continuation {v : Fin K → Alphabet} (z : ℤ) {a : ℕ}
    (ha : 0 < a) (haK : a ≤ K) (hp : Period v a) :
    ∃ w : ℤ → Alphabet, Function.Periodic w (a : ℤ) ∧ Occurs w v z :=
  ⟨continuation v z a ha haK, continuation_periodic v z a ha haK,
    continuation_agrees z ha haK hp⟩

lemma continuation_unique {d : ℕ} (hd : 2 ≤ d) (hK : d ^ 2 ≤ K)
    {v : Fin K → Alphabet} {z : ℤ} {w w' : ℤ → Alphabet}
    {a b : ℕ} (ha : 0 < a) (had : a < d) (hb : 0 < b) (hbd : b < d)
    (hw : Function.Periodic w (a : ℤ)) (hw' : Function.Periodic w' (b : ℤ))
    (he : Occurs w v z) (he' : Occurs w' v z) : w = w' := by
  have hab : a * b ≤ K := by nlinarith
  apply periodic_agree (by exact_mod_cast ha) (by exact_mod_cast hb) hw hw' z
  intro i hi hi'
  have habZ : (a : ℤ) * b ≤ K := by exact_mod_cast hab
  have hn : ((i - z).toNat : ℤ) = i - z := Int.toNat_of_nonneg (by omega)
  let j : Fin K := ⟨(i - z).toNat, by omega⟩
  have hj : z + (j.val : ℤ) = i := by dsimp [j]; omega
  rw [← hj, he j, he' j]

end LocalMarkers

namespace FiniteMonoidPeriod

variable {M : Type uM} [Monoid M]

lemma pow_add_of_repeat (c : M) {i v k : ℕ} (h : c ^ (i + v) = c ^ i) (hik : i ≤ k) :
    c ^ (k + v) = c ^ k := by
  have hk : k + v = (i + v) + (k - i) := by omega
  rw [hk, pow_add, h, ← pow_add, Nat.add_sub_of_le hik]

lemma pow_add_multiple (c : M) {i v k : ℕ} (h : c ^ (i + v) = c ^ i) (hik : i ≤ k)
    (q : ℕ) : c ^ (k + q * v) = c ^ k := by
  induction q with
  | zero => simp
  | succ q ih =>
    have he : k + (q + 1) * v = k + q * v + v := by ring
    rw [he, pow_add_of_repeat c h (by omega), ih]

lemma exists_repeat [Fintype M] (c : M) :
    ∃ i v : ℕ, i < Fintype.card M ∧ 0 < v ∧ v ≤ Fintype.card M ∧
      c ^ (i + v) = c ^ i := by
  obtain ⟨i, j, hne, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun n : Fin (Fintype.card M + 1) => c ^ n.val) (by simp)
  have hvne : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hvne with hij | hji
  · refine ⟨i.val, j.val - i.val, by omega, by omega, by omega, ?_⟩
    rw [Nat.add_sub_of_le (le_of_lt hij)]
    exact he.symm
  · refine ⟨j.val, i.val - j.val, by omega, by omega, by omega, ?_⟩
    rw [Nat.add_sub_of_le (le_of_lt hji)]
    exact he

theorem pow_factorial [Fintype M] (c : M) {k : ℕ} (hk : Fintype.card M ≤ k) (q : ℕ) :
    c ^ (k + q * (Fintype.card M).factorial) = c ^ k := by
  obtain ⟨i, v, hi, hv, hvN, he⟩ := exists_repeat c
  obtain ⟨r, hr⟩ := Nat.dvd_factorial hv hvN
  rw [hr]
  have ha : q * (v * r) = (q * r) * v := by ring
  rw [ha]
  exact pow_add_multiple c he (by omega) _

end FiniteMonoidPeriod

end GeneralizedStarHeight

end OAI
