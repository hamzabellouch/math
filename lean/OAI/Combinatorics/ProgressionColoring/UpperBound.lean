import OAI.Combinatorics.ProgressionColoring.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

namespace OAI

universe uAlpha u

namespace QuantitativeVanDerWaerden

/-- The inner recursion, with the bound for the preceding length supplied. -/
def focusSize (previous : ℕ → ℕ) (r : ℕ) : ℕ → ℕ
  | 0 => 1
  | t + 1 => 2 * focusSize previous r t * previous (r ^ focusSize previous r t)

/-- Length is the recursion argument; all color counts at the previous
length are available before the next length is constructed. -/
def Fcore : ℕ → ℕ → ℕ
  | 0, _ => 1
  | 1, _ => 1
  | 2, r => r + 1
  | k + 3, r => focusSize (Fcore (k + 2)) r r

def F (r k : ℕ) : ℕ := Fcore k r

@[simp] theorem F_one (r : ℕ) : F r 1 = 1 := rfl
@[simp] theorem F_two (r : ℕ) : F r 2 = r + 1 := rfl
theorem F_recursion (r k : ℕ) :
    F r (k + 3) = focusSize (fun q => F q (k + 2)) r r := rfl

theorem focusSize_pos {previous : ℕ → ℕ} {r : ℕ}
    (hp : ∀ q, 0 < q → 0 < previous q) (hr : 0 < r) (t : ℕ) :
    0 < focusSize previous r t := by
  induction t with
  | zero => exact Nat.zero_lt_one
  | succ t ih =>
    exact Nat.mul_pos (Nat.mul_pos (by decide) ih) (hp _ (pow_pos hr _))

theorem Fcore_pos (k : ℕ) : ∀ r, 0 < r → 0 < Fcore k r := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | _ | _ | k
    · intro r hr; exact Nat.zero_lt_one
    · intro r hr; exact Nat.zero_lt_one
    · intro r hr; exact Nat.zero_lt_succ r
    · intro r hr
      exact focusSize_pos (ih (k + 2) (by omega)) hr r

theorem F_pos {r k : ℕ} (hr : 0 < r) : 0 < F r k := Fcore_pos k r hr

private theorem hasMonoAP_two_of_lt {α : Type uAlpha} {c : ℕ → α} {a b N : ℕ}
    (hab : a < b) (hb : b < N) (hc : c a = c b) : HasMonoAP c 2 N := by
  refine ⟨a, b - a, by omega, by simpa [Nat.add_sub_of_le (Nat.le_of_lt hab)] using hb, ?_⟩
  intro j hj
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hj' with rfl | rfl
  · simp
  · simpa [Nat.add_sub_of_le (Nat.le_of_lt hab)] using hc.symm

theorem isRamsey_two (α : Type uAlpha) [Fintype α] :
    IsRamsey α 2 (Fintype.card α + 1) := by
  classical
  intro c
  obtain ⟨a, b, hab, hc⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun n : Fin (Fintype.card α + 1) => c n.val) (by simp)
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hasMonoAP_two_of_lt hlt b.isLt hc
  · exact hasMonoAP_two_of_lt hlt a.isLt hc.symm

/-- A focus with distinct arm colors. The arms have length `k - 1`, and
adding their common next point would give a progression of length `k`. -/
structure Focus {α : Type uAlpha} (c : ℕ → α) (k N t : ℕ) where
  point : ℕ
  point_lt : point < N
  start : Fin t → ℕ
  step : Fin t → ℕ
  step_pos : ∀ i, 0 < step i
  ends : ∀ i, start i + (k - 1) * step i = point
  mono : ∀ i, MonoAP c (k - 1) (start i) (step i)
  colors_injective : Function.Injective (fun i => c (start i))

theorem Focus.color_ne {α : Type uAlpha} {c : ℕ → α} {k N t : ℕ}
    (f : Focus c k N t) (ha : ¬ HasMonoAP c k N) (i : Fin t) :
    c f.point ≠ c (f.start i) := by
  intro he
  apply ha
  refine ⟨f.start i, f.step i, f.step_pos i, ?_, ?_⟩
  · rw [f.ends i]; exact f.point_lt
  · intro j hj
    by_cases h : j < k - 1
    · exact f.mono i j h
    · have hj' : j = k - 1 := by omega
      rw [hj', f.ends i]
      exact he

private theorem fin_cases_injective {α : Type uAlpha} {t : ℕ} {a : α} {g : Fin t → α}
    (hg : Function.Injective g) (ha : ∀ i, a ≠ g i) :
    Function.Injective (Fin.cases a g) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro _; rfl
    · intro hij; exact False.elim (ha j hij)
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hij; exact False.elim (ha i hij.symm)
    · intro hij; exact congrArg Fin.succ (hg hij)

theorem Focus.impossible {α : Type uAlpha} [Fintype α] {c : ℕ → α} {k N : ℕ}
    (f : Focus c k N (Fintype.card α)) (ha : ¬ HasMonoAP c k N) : False := by
  have h := Fintype.card_le_of_injective
    (Fin.cases (c f.point) (fun i => c (f.start i)))
    (fin_cases_injective f.colors_injective (f.color_ne ha))
  simp only [Fintype.card_fin] at h
  omega

def blockWord {α : Type uAlpha} (c : ℕ → α) (m b : ℕ) : Fin m → α :=
  fun x => c (b * m + x.val)

private theorem matching_point {α : Type uAlpha} {c : ℕ → α} {m k b d j x : ℕ}
    (h : MonoAP (blockWord c m) k b d) (hj : j < k) (hx : x < m) :
    c ((b + j * d) * m + x) = c (b * m + x) :=
  congrFun (h j hj) ⟨x, hx⟩

/-- The next block is allocated, even though its word need not match. -/
private theorem next_block_lt {k b d B : ℕ} (hk : 3 ≤ k)
    (hb : b + (k - 2) * d < B) : b + (k - 1) * d < 2 * B := by
  have hpred : k - 1 = (k - 2) + 1 := by omega
  have hd : d ≤ (k - 2) * d := by
    simpa using Nat.mul_le_mul_right d (show 1 ≤ k - 2 by omega)
  rw [hpred, Nat.add_mul, one_mul]
  omega

/-- Copy the old arms into matching blocks and add the arm supplied by
the old focus. All positions and differences are kept explicitly. -/
theorem focus_lift {α : Type uAlpha} {c : ℕ → α} {k m B b d t : ℕ}
    (hk : 3 ≤ k) (hm : 0 < m) (hd : 0 < d)
    (hb : b + (k - 2) * d < B)
    (hw : MonoAP (blockWord c m) (k - 1) b d)
    (old : Focus (fun x => c (b * m + x)) k m t)
    (ha : ¬ HasMonoAP (fun x => c (b * m + x)) k m) :
    Nonempty (Focus c k (2 * m * B) (t + 1)) := by
  let q := b + (k - 1) * d
  have hq : q < 2 * B := next_block_lt hk hb
  have hpoint : q * m + old.point < 2 * m * B := by
    calc
      q * m + old.point < q * m + m := Nat.add_lt_add_left old.point_lt _
      _ = (q + 1) * m := by ring
      _ ≤ (2 * B) * m := Nat.mul_le_mul_right m (by omega)
      _ = 2 * m * B := by ring
  let starts : Fin (t + 1) → ℕ :=
    Fin.cases (b * m + old.point) (fun i => b * m + old.start i)
  let steps : Fin (t + 1) → ℕ :=
    Fin.cases (m * d) (fun i => m * d + old.step i)
  refine ⟨{
    point := q * m + old.point
    point_lt := hpoint
    start := starts
    step := steps
    step_pos := ?_
    ends := ?_
    mono := ?_
    colors_injective := ?_ }⟩
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact Nat.mul_pos hm hd
    · exact Nat.lt_of_lt_of_le (old.step_pos i) (Nat.le_add_left _ _)
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · dsimp [starts, steps, q]; ring
    · change b * m + old.start i + (k - 1) * (m * d + old.step i) = _
      calc
        _ = q * m + (old.start i + (k - 1) * old.step i) := by dsimp [q]; ring
        _ = q * m + old.point := by rw [old.ends i]
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j hj
      change c (b * m + old.point + j * (m * d)) = c (b * m + old.point)
      rw [show b * m + old.point + j * (m * d) =
        (b + j * d) * m + old.point by ring]
      exact matching_point hw hj old.point_lt
    · intro j hj
      have hx : old.start i + j * old.step i < m := by
        have hle := Nat.mul_le_mul_right (old.step i) (show j ≤ k - 1 by omega)
        have he := old.ends i
        have hp := old.point_lt
        omega
      change c (b * m + old.start i + j * (m * d + old.step i)) =
        c (b * m + old.start i)
      rw [show b * m + old.start i + j * (m * d + old.step i) =
        (b + j * d) * m + (old.start i + j * old.step i) by ring]
      exact (matching_point hw hj hx).trans (old.mono i j hj)
  · have hi := fin_cases_injective old.colors_injective (old.color_ne ha)
    have he (i : Fin (t + 1)) : c (starts i) =
        Fin.cases (c (b * m + old.point)) (fun i => c (b * m + old.start i)) i := by
      refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
    intro i j hij
    exact hi ((he i).symm.trans (hij.trans (he j)))

/-- The inner focusing induction, simultaneously for every finite color
type so that complete block words can themselves serve as colors. -/
theorem focusing {α : Type u} [Fintype α] {previous : ℕ → ℕ} {k : ℕ}
    (hk : 3 ≤ k) (hr : 0 < Fintype.card α)
    (hp : ∀ r, 0 < r → 0 < previous r)
    (hprevious : ∀ (β : Type u) [Fintype β], 0 < Fintype.card β →
      IsRamsey β (k - 1) (previous (Fintype.card β))) :
    ∀ (t : ℕ) (c : ℕ → α),
      ¬ HasMonoAP c k (focusSize previous (Fintype.card α) t) →
      Nonempty (Focus c k (focusSize previous (Fintype.card α) t) t) := by
  classical
  intro t
  induction t with
  | zero =>
    intro c ha
    exact ⟨{
      point := 0
      point_lt := Nat.zero_lt_one
      start := Fin.elim0
      step := Fin.elim0
      step_pos := fun i => Fin.elim0 i
      ends := fun i => Fin.elim0 i
      mono := fun i => Fin.elim0 i
      colors_injective := fun i => Fin.elim0 i }⟩
  | succ t ih =>
    intro c ha
    let m := focusSize previous (Fintype.card α) t
    let B := previous (Fintype.card α ^ m)
    have hm : 0 < m := focusSize_pos hp hr t
    have hcard : Fintype.card (Fin m → α) = Fintype.card α ^ m := by
      simp only [Fintype.card_fun, Fintype.card_fin]
    have hwc := hprevious (Fin m → α) (by rw [hcard]; exact pow_pos hr m)
    rw [hcard] at hwc
    obtain ⟨b, d, hd, hb, hw⟩ := hwc (blockWord c m)
    have hb' : b + (k - 2) * d < B := by
      simpa only [Nat.sub_sub] using hb
    have hstart : b < B := by omega
    have hinside : b * m + m ≤ 2 * m * B := by
      calc
        b * m + m = (b + 1) * m := by ring
        _ ≤ B * m := Nat.mul_le_mul_right m (by omega)
        _ ≤ (2 * B) * m := Nat.mul_le_mul_right m (by omega)
        _ = 2 * m * B := by ring
    have havoid : ¬ HasMonoAP (fun x => c (b * m + x)) k m := by
      intro h
      apply ha
      exact h.translate.mono hinside
    obtain ⟨old⟩ := ih (fun x => c (b * m + x)) havoid
    exact focus_lift hk hm hd hb' hw old havoid

theorem isRamsey_Fcore (k : ℕ) (hk : 0 < k) :
    ∀ (α : Type u) [Fintype α], 0 < Fintype.card α →
      IsRamsey α k (Fcore k (Fintype.card α)) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | _ | _ | k
    · omega
    · intro α _ hr; exact isRamsey_one α
    · intro α _ hr; exact isRamsey_two α
    · intro α _ hr c
      classical
      by_contra ha
      have hprev : ∀ (β : Type u) [Fintype β], 0 < Fintype.card β →
          IsRamsey β (k + 3 - 1) (Fcore (k + 2) (Fintype.card β)) := by
        intro β _ hβ
        simpa using ih (k + 2) (by omega) (by omega) β hβ
      obtain ⟨f⟩ := focusing (k := k + 3) (by omega) hr
        (Fcore_pos (k + 2)) hprev (Fintype.card α) c ha
      exact f.impossible ha

theorem isRamsey_F (α : Type uAlpha) [Fintype α] {k : ℕ}
    (hk : 0 < k) (hr : 0 < Fintype.card α) :
    IsRamsey α k (F (Fintype.card α) k) := isRamsey_Fcore k hk α hr

/-- Unconditional finiteness for every positive color count and length. -/
theorem finite_ramsey {r k : ℕ} (hr : 0 < r) (hk : 0 < k) :
    ∃ N, 0 < N ∧ IsRamsey (Fin r) k N := by
  refine ⟨F r k, F_pos hr, ?_⟩
  simpa only [Fintype.card_fin] using isRamsey_F (Fin r) hk (by simpa using hr)

theorem W_le_F {r k : ℕ} (hr : 0 < r) (hk : 0 < k) : W r k ≤ F r k := by
  apply W_le_of_isRamsey (F_pos hr)
  simpa only [Fintype.card_fin] using isRamsey_F (Fin r) hk (by simpa using hr)

theorem W_spec {r k : ℕ} (hr : 0 < r) (hk : 0 < k) :
    0 < W r k ∧ IsRamsey (Fin r) k (W r k) := W_spec_of_finite (finite_ramsey hr hk)

theorem W_two {r : ℕ} (hr : 0 < r) : W r 2 = r + 1 := by
  let c : ℕ → Fin r := fun n => ⟨n % r, Nat.mod_lt n hr⟩
  have ha : ¬ HasMonoAP c 2 r := by
    rintro ⟨a, d, hd, hb, hm⟩
    have hb' : a + d < r := by simpa using hb
    have ha' : a < r := by omega
    have he := congrArg Fin.val (hm 1 (by omega))
    dsimp [c] at he
    simp only [one_mul, Nat.mod_eq_of_lt hb', Nat.mod_eq_of_lt ha'] at he
    omega
  have hl := lt_W_of_avoiding (finite_ramsey hr (by omega : 0 < 2)) c ha
  have hu := W_le_F hr (by omega : 0 < 2)
  rw [F_two] at hu
  omega

end QuantitativeVanDerWaerden

end OAI
