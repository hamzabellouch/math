import OAI.Geometry.PeriodicTiling.FiniteMasks
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Factorial.Basic
import Lean.Elab.Tactic.Omega

namespace OAI

universe uG uι

noncomputable section

open scoped BigOperators Classical

namespace PeriodicTilingThree

section ArbitraryGroup

variable {G : Type uG} [AddCommGroup G]

theorem sum_tileIndicator_nat_le_card
    {G : Type uG} [AddCommGroup G]
    {ι : Type uι} (s : Finset ι)
    (A : Set G) (v : ι → G) :
    (∑ i ∈ s, tileIndicator ℕ A (v i)) ≤ s.card := by
  calc
    (∑ i ∈ s, tileIndicator ℕ A (v i)) ≤ ∑ _i ∈ s, (1 : ℕ) :=
      Finset.sum_le_sum fun i _hi => tileIndicator_nat_le_one A (v i)
    _ = s.card := by simp

theorem familyMask_pow_prime {ι : Type uι} (s : Finset ι) (v : ι → G)
    {p : ℕ} (hp : p.Prime) :
    familyMask (ZMod p) s v ^ p = familyMask (ZMod p) s (fun i => p • v i) := by
  let : Fact p.Prime := ⟨hp⟩
  let : CharP (AddMonoidAlgebra (ZMod p) G) p :=
    ⟨fun n => by
      rw [AddMonoidAlgebra.natCast_def, AddMonoidAlgebra.single_eq_zero,
        CharP.cast_eq_zero_iff (ZMod p) p]⟩
  unfold familyMask
  rw [sum_pow_char]
  apply Finset.sum_congr rfl
  intro i hi
  rw [AddMonoidAlgebra.single_pow, one_pow]

theorem sum_tileIndicator_dilate_prime {ι : Type uι} (s : Finset ι)
    (v : ι → G) (A : Set G)
    (h : ∀ x, (∑ i ∈ s, tileIndicator ℕ A (x - v i)) = 1)
    {p : ℕ} (hp : p.Prime) (hcard : s.card < p) (x : G) :
    (∑ i ∈ s, tileIndicator ℕ A (x - p • v i)) = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hpos : 0 < s.card := by
    have hb := sum_tileIndicator_nat_le_card s A (fun i => (0 : G) - v i)
    rw [h 0] at hb
    exact lt_of_lt_of_le Nat.zero_lt_one hb
  have hne : (s.card : ZMod p) ≠ 0 := by
    intro hz
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt hcard, ZMod.val_zero] at hv
    exact (Nat.ne_of_gt hpos) hv
  have hfermat : (s.card : ZMod p) ^ (p - 1) = 1 := by
    simpa only [ZMod.card] using
      (FiniteField.pow_card_sub_one_eq_one (s.card : ZMod p) hne)
  have hmod : ∀ y, (∑ i ∈ s, tileIndicator (ZMod p) A (y - v i)) = 1 := by
    intro y
    rw [← sum_tileIndicator_cast, h y, Nat.cast_one]
  have hpower : maskAction (familyMask (ZMod p) s v ^ p)
      (tileIndicator (ZMod p) A) x = (s.card : ZMod p) ^ (p - 1) := by
    simpa only [Nat.sub_add_cancel hp.one_lt.le] using
      (maskAction_familyMask_pow_succ s v (tileIndicator (ZMod p) A) hmod (p - 1) x)
  have hmod_dilate :
      (∑ i ∈ s, tileIndicator (ZMod p) A (x - p • v i)) = 1 := by
    rw [← maskAction_familyMask, ← familyMask_pow_prime s v hp, hpower, hfermat]
  have hc :
      ((∑ i ∈ s, tileIndicator ℕ A (x - p • v i) : ℕ) : ZMod p) = 1 := by
    rw [sum_tileIndicator_cast]
    exact hmod_dilate
  have hv := congrArg ZMod.val hc
  have hbound : (∑ i ∈ s, tileIndicator ℕ A (x - p • v i)) < p :=
    lt_of_le_of_lt (sum_tileIndicator_nat_le_card s A _) hcard
  rwa [ZMod.val_natCast_of_lt hbound, ZMod.val_one_eq_one_mod,
    Nat.mod_eq_of_lt hp.one_lt] at hv

theorem sum_tileIndicator_dilate_of_prime_factors {ι : Type uι} (s : Finset ι)
    (v : ι → G) (A : Set G)
    (h : ∀ x, (∑ i ∈ s, tileIndicator ℕ A (x - v i)) = 1)
    (r : ℕ) (hr : r ≠ 0)
    (hlarge : ∀ p : ℕ, p.Prime → p ∣ r → s.card < p) (x : G) :
    (∑ i ∈ s, tileIndicator ℕ A (x - r • v i)) = 1 := by
  have hall : ∀ n : ℕ, n ≠ 0 →
      (∀ p : ℕ, p.Prime → p ∣ n → s.card < p) →
      ∀ y, (∑ i ∈ s, tileIndicator ℕ A (y - n • v i)) = 1 := by
    apply induction_on_primes
    · intro hn
      exact (hn rfl).elim
    · intro _hn _hpr y
      simpa only [one_nsmul] using h y
    · intro p n hp ih hpn hpr y
      have hn : n ≠ 0 := by
        intro hn
        apply hpn
        simp [hn]
      have hprn : ∀ q : ℕ, q.Prime → q ∣ n → s.card < q := by
        intro q hq hqn
        exact hpr q hq (dvd_mul_of_dvd_right hqn p)
      have hpp : s.card < p := hpr p hp (dvd_mul_right p n)
      simpa only [mul_smul] using
        (sum_tileIndicator_dilate_prime s (fun i => n • v i) A
          (ih hn hprn) hp hpp y)
  exact hall r hr hlarge x

theorem prime_factor_factorial_mul_add_one_gt (N k p : ℕ)
    (hp : p.Prime) (hd : p ∣ 1 + N.factorial * k) : N < p := by
  by_contra hnp
  have hpf : p ∣ N.factorial := Nat.dvd_factorial hp.pos (Nat.le_of_not_gt hnp)
  have hpm : p ∣ N.factorial * k := dvd_mul_of_dvd_left hpf k
  have hpone : p ∣ 1 := (Nat.dvd_add_left hpm).mp hd
  exact hp.ne_one (Nat.dvd_one.mp hpone)

theorem Tiles.sum_tileIndicator_nat_dilate_factorial {F : Finset G} {A : Set G}
    (h : Tiles F A) (k : ℕ) (x : G) :
    (∑ f ∈ F, tileIndicator ℕ A (x - (1 + F.card.factorial * k) • f)) = 1 := by
  apply sum_tileIndicator_dilate_of_prime_factors F id A
    (fun y => h.tileCount_eq_one y) (1 + F.card.factorial * k)
  · omega
  · intro p hp hd
    exact prime_factor_factorial_mul_add_one_gt F.card k p hp hd

theorem Tiles.sum_tileIndicator_dilate_factorial {F : Finset G} {A : Set G}
    (h : Tiles F A) (k : ℕ) (x : G) :
    (∑ f ∈ F, tileIndicator ℝ A (x - (1 + F.card.factorial * k) • f)) = 1 := by
  rw [← sum_tileIndicator_cast, h.sum_tileIndicator_nat_dilate_factorial k x,
    Nat.cast_one]

def dilateTile (r : ℕ) (F : Finset G) : Finset G :=
  F.image (fun f => r • f)

end ArbitraryGroup

theorem plane_nsmul_injective {r : ℕ} (hr : r ≠ 0) :
    Function.Injective (fun x : Plane => r • x) := by
  intro x y hxy
  have hrz : (r : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hr
  apply Prod.ext
  · apply mul_left_cancel₀ hrz
    have hx : r • x.1 = r • y.1 := congrArg Prod.fst hxy
    simpa only [nsmul_eq_mul] using hx
  · apply mul_left_cancel₀ hrz
    have hy : r • x.2 = r • y.2 := congrArg Prod.snd hxy
    simpa only [nsmul_eq_mul] using hy

theorem dilateTile_card (r : ℕ) (hr : r ≠ 0) (F : Finset Plane) :
    (dilateTile r F).card = F.card := by
  let : DecidableEq Plane := fun a b => Classical.propDecidable (a = b)
  exact Finset.card_image_of_injective F (plane_nsmul_injective hr)

theorem tileCount_dilateTile (r : ℕ) (hr : r ≠ 0)
    (F : Finset Plane) (A : Set Plane) (x : Plane) :
    tileCount (dilateTile r F) A x = ∑ f ∈ F, tileIndicator ℕ A (x - r • f) := by
  let : DecidableEq Plane := fun a b => Classical.propDecidable (a = b)
  unfold tileCount dilateTile
  apply Finset.sum_image
  intro f hf g hg hfg
  exact plane_nsmul_injective hr hfg

theorem Tiles.dilate_prime {F : Finset Plane} {A : Set Plane} (h : Tiles F A)
    {p : ℕ} (hp : p.Prime) (hcard : F.card < p) : Tiles (dilateTile p F) A := by
  apply tiles_iff_tileCount_eq_one.mpr
  intro x
  rw [tileCount_dilateTile p hp.ne_zero]
  exact sum_tileIndicator_dilate_prime F id A (fun y => h.tileCount_eq_one y) hp hcard x

theorem Tiles.dilate_of_prime_factors {F : Finset Plane} {A : Set Plane}
    (h : Tiles F A) (r : ℕ) (hr : r ≠ 0)
    (hlarge : ∀ p : ℕ, p.Prime → p ∣ r → F.card < p) :
    Tiles (dilateTile r F) A := by
  apply tiles_iff_tileCount_eq_one.mpr
  intro x
  rw [tileCount_dilateTile r hr]
  exact sum_tileIndicator_dilate_of_prime_factors F id A
    (fun y => h.tileCount_eq_one y) r hr hlarge x

theorem Tiles.dilate_factorial {F : Finset Plane} {A : Set Plane}
    (h : Tiles F A) (k : ℕ) : Tiles (dilateTile (1 + F.card.factorial * k) F) A := by
  apply h.dilate_of_prime_factors (1 + F.card.factorial * k)
  · omega
  · intro p hp hd
    exact prime_factor_factorial_mul_add_one_gt F.card k p hp hd

end PeriodicTilingThree

end

end OAI
