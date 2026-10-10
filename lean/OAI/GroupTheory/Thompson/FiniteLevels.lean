import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace OAI

/-!
# Finite scalar levels

The distinct values of a nonnegative function on a finite set, together with
zero, give a finite subdivision. Its positive gaps reconstruct every value
and every absolute difference by strict superlevel indicators. These are
finite sums, including when the only level is zero.
-/

open scoped BigOperators

universe uG

namespace ThompsonNonamenability

variable {G : Type uG}

/-- The actual ordered levels of `p` on `K`, with zero included. -/
structure FiniteLevelChain (K : Finset G) (p : G → ℝ) where
  n : ℕ
  value : Fin (n + 1) → ℝ
  value_zero : value 0 = 0
  strictMono_value : StrictMono value
  image_value_eq : Finset.univ.image value = insert 0 (K.image p)

namespace FiniteLevelChain

/-- Construct the level chain by sorting the actual finite image. -/
noncomputable def ofNonneg (K : Finset G) (p : G → ℝ)
    (hp : ∀ x ∈ K, 0 ≤ p x) : FiniteLevelChain K p := by
  classical
  let L : Finset ℝ := insert 0 (K.image p)
  have hpos : 0 < L.card := Finset.card_pos.mpr ⟨0, by simp [L]⟩
  let n := L.card - 1
  have hcard : L.card = n + 1 := by dsimp [n]; omega
  let e : Fin (n + 1) ↪o ℝ := L.orderEmbOfFin hcard
  have heimage : Finset.univ.image e = L :=
    Finset.image_orderEmbOfFin_univ L hcard
  have hnonneg : ∀ a ∈ L, 0 ≤ a := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact le_rfl
    · rcases Finset.mem_image.mp ha with ⟨x, hx, rfl⟩
      exact hp x hx
  have hezero : e 0 = 0 := by
    have hz : (0 : ℝ) ∈ Finset.univ.image e := by
      rw [heimage]
      simp [L]
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hz
    apply le_antisymm
    · calc
        e 0 ≤ e j := e.monotone (Fin.zero_le j)
        _ = 0 := hj
    · exact hnonneg (e 0) (Finset.orderEmbOfFin_mem L hcard 0)
  exact ⟨n, e, hezero, e.strictMono, heimage⟩

theorem exists_chain (K : Finset G) (p : G → ℝ)
    (hp : ∀ x ∈ K, 0 ≤ p x) : Nonempty (FiniteLevelChain K p) :=
  ⟨ofNonneg K p hp⟩

variable {K : Finset G} {p : G → ℝ} (c : FiniteLevelChain K p)

/-- Width of the interval immediately above the indexed level. -/
def gap (i : Fin c.n) : ℝ := c.value i.succ - c.value i.castSucc

theorem gap_pos (i : Fin c.n) : 0 < c.gap i := by
  apply sub_pos.mpr
  exact c.strictMono_value (show i.castSucc < i.succ from Nat.lt_succ_self i.val)

theorem value_nonneg (j : Fin (c.n + 1)) : 0 ≤ c.value j := by
  rw [← c.value_zero]
  exact c.strictMono_value.monotone (Fin.zero_le j)

theorem value_mem (j : Fin (c.n + 1)) : c.value j ∈ insert 0 (K.image p) := by
  rw [← c.image_value_eq]
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

/-- Telescoping below any selected value of a strictly increasing finite list. -/
private theorem telescope : ∀ (n : ℕ) (f : Fin (n + 1) → ℝ),
    StrictMono f → ∀ k : Fin (n + 1),
      f k - f 0 = ∑ i : Fin n,
        (f i.succ - f i.castSucc) * (if f i.castSucc < f k then 1 else 0) := by
  intro n
  induction n with
  | zero =>
      intro f hf k
      have hk : k = 0 := by
        apply Fin.ext
        have hklt := k.isLt
        omega
      subst k
      simp
  | succ n ih =>
      intro f hf k
      refine Fin.cases ?_ (fun k => ?_) k
      · have hnot : ∀ i : Fin (n + 1), ¬ f i.castSucc < f 0 := by
          intro i
          exact not_lt_of_ge (hf.monotone (Fin.zero_le i.castSucc))
        simp [hnot]
      · have hs := ih (fun j : Fin (n + 1) => f j.succ)
          (by intro a b hab; exact hf (Nat.succ_lt_succ hab)) k
        have hfirst : f 0 < f k.succ := hf (Fin.succ_pos k)
        rw [Fin.sum_univ_succ]
        change f k.succ - f 0 =
          (f (0 : Fin (n + 1)).succ - f 0) * (if f 0 < f k.succ then 1 else 0) +
            ∑ i : Fin n, (f i.succ.succ - f i.castSucc.succ) *
              (if f i.castSucc.succ < f k.succ then 1 else 0)
        rw [ite_eq_left hfirst, mul_one, ← hs]
        ring

/-- The finite layer decomposition of each value in the actual level set. -/
theorem reconstruct (a : ℝ) (ha : a ∈ insert 0 (K.image p)) :
    a = ∑ i : Fin c.n, c.gap i *
      (if c.value i.castSucc < a then (1 : ℝ) else 0) := by
  classical
  have ha' : a ∈ Finset.univ.image c.value := by
    rw [c.image_value_eq]
    exact ha
  rcases Finset.mem_image.mp ha' with ⟨k, _, rfl⟩
  simpa only [gap, c.value_zero, sub_zero] using
    telescope c.n c.value c.strictMono_value k

private theorem abs_sub_eq_sum_of_le (a b : ℝ)
    (ha : a ∈ insert 0 (K.image p)) (hb : b ∈ insert 0 (K.image p))
    (hab : a ≤ b) :
    |a - b| = ∑ i : Fin c.n, c.gap i *
      |(if c.value i.castSucc < a then (1 : ℝ) else 0) -
        (if c.value i.castSucc < b then (1 : ℝ) else 0)| := by
  classical
  have hi : ∀ i : Fin c.n,
      (if c.value i.castSucc < a then (1 : ℝ) else 0) ≤
        (if c.value i.castSucc < b then (1 : ℝ) else 0) := by
    intro i
    by_cases hai : c.value i.castSucc < a
    · have hbi : c.value i.castSucc < b := lt_of_lt_of_le hai hab
      simp [hai, hbi]
    · simp only [ite_eq_right hai]
      by_cases hbi : c.value i.castSucc < b <;> simp [hbi]
  calc
    |a - b| = b - a := by rw [abs_of_nonpos (sub_nonpos.mpr hab)]; ring
    _ = (∑ i : Fin c.n, c.gap i * (if c.value i.castSucc < b then (1 : ℝ) else 0)) -
        (∑ i : Fin c.n, c.gap i * (if c.value i.castSucc < a then (1 : ℝ) else 0)) :=
      congrArg₂ (fun x y : ℝ => x - y) (c.reconstruct b hb) (c.reconstruct a ha)
    _ = ∑ i : Fin c.n, c.gap i *
        |(if c.value i.castSucc < a then (1 : ℝ) else 0) -
          (if c.value i.castSucc < b then (1 : ℝ) else 0)| := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_of_nonpos (sub_nonpos.mpr (hi i))]
      ring

/-- The finite coarea identity for a scalar absolute difference. -/
theorem abs_sub_eq_sum (a b : ℝ)
    (ha : a ∈ insert 0 (K.image p)) (hb : b ∈ insert 0 (K.image p)) :
    |a - b| = ∑ i : Fin c.n, c.gap i *
      |(if c.value i.castSucc < a then (1 : ℝ) else 0) -
        (if c.value i.castSucc < b then (1 : ℝ) else 0)| := by
  rcases le_total a b with hab | hba
  · exact c.abs_sub_eq_sum_of_le a b ha hb hab
  · simpa only [abs_sub_comm] using c.abs_sub_eq_sum_of_le b a hb ha hba

end FiniteLevelChain

end ThompsonNonamenability

end OAI
