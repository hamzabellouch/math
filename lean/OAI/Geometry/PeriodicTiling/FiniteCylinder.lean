import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace OAI

universe uA

namespace PeriodicTilingThree.FiniteCylinder

def wrap (i L n : ℤ) : ℤ := i + (n - i) % L

theorem wrap_bounds (i n : ℤ) {L : ℤ} (hL : 0 < L) :
    i ≤ wrap i L n ∧ wrap i L n < i + L := by
  have hnonneg := Int.emod_nonneg (n - i) (ne_of_gt hL)
  have hlt := Int.emod_lt_of_pos (n - i) hL
  dsimp [wrap]
  omega

theorem wrap_eq_self {i L n : ℤ} (hi : i ≤ n) (hn : n < i + L) :
    wrap i L n = n := by
  unfold wrap
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  omega

theorem wrap_add_period (i L n : ℤ) : wrap i L (n + L) = wrap i L n := by
  unfold wrap
  rw [show n + L - i = (n - i) + L by omega]
  simp

theorem wrap_dvd (i L n : ℤ) : L ∣ n - wrap i L n := by
  refine ⟨(n - i) / L, ?_⟩
  have h := Int.emod_add_mul_ediv (n - i) L
  dsimp [wrap]
  omega

theorem wrap_shift (i L n k : ℤ) :
    wrap i L (n + k) = wrap i L (wrap i L n + k) := by
  unfold wrap
  congr 1
  rw [show n + k - i = (n - i) + k by omega,
    show i + (n - i) % L + k - i = (n - i) % L + k by omega]
  exact (Int.emod_add_emod (n - i) L k).symm

theorem window_at_wrap {A : Type uA} (a : ℤ → A) (H : ℕ) (i L : ℤ)
    (hL : (H : ℤ) < L)
    (hrows : ∀ c : Fin H, a (i + (c : ℕ)) = a (i + L + (c : ℕ)))
    (n k : ℤ) (hk0 : 0 ≤ k) (hkH : k ≤ H) :
    a (wrap i L (n + k)) = a (wrap i L n + k) := by
  have hL0 : 0 < L := by omega
  obtain ⟨hb0, hbL⟩ := wrap_bounds i n hL0
  rw [wrap_shift]
  by_cases hcross : wrap i L n + k < i + L
  · exact congrArg a (wrap_eq_self (by omega) hcross)
  · let c : ℤ := wrap i L n + k - (i + L)
    have hc0 : 0 ≤ c := by dsimp [c]; omega
    have hcH : c < H := by dsimp [c]; omega
    have hcL : c < L := by omega
    let cN : Fin H := ⟨c.toNat, by omega⟩
    have hcN : ((cN : ℕ) : ℤ) = c := by dsimp [cN]; omega
    have heq : wrap i L n + k = (i + c) + L := by dsimp [c]; omega
    have h := hrows cN
    rw [hcN] at h
    calc
      a (wrap i L (wrap i L n + k)) = a (wrap i L ((i + c) + L)) :=
        congrArg (fun z => a (wrap i L z)) heq
      _ = a (i + c) := congrArg a
        ((wrap_add_period i L (i + c)).trans (wrap_eq_self (by omega) (by omega)))
      _ = a (i + L + c) := h
      _ = a (wrap i L n + k) := congrArg a (by dsimp [c]; omega)

theorem exists_periodic_windows {A : Type uA} [Fintype A]
    (a : ℤ → A) (q H : ℕ) (hq : 0 < q) :
    ∃ (b : ℤ → A) (L : ℤ), 0 < L ∧ (q : ℤ) ∣ L ∧
      (∀ n : ℤ, b (n + L) = b n) ∧
      (∀ n : ℤ, ∃ t : ℤ, (q : ℤ) ∣ t - n ∧
        ∀ k : ℤ, 0 ≤ k → k ≤ H → b (n + k) = a (t + k)) := by
  classical
  let : NeZero q := ⟨Nat.ne_of_gt hq⟩
  let State := ZMod q × (Fin H → A)
  let time (k : ℕ) : ℤ := (k : ℤ) * ((H : ℤ) + 1)
  let state (k : ℕ) : State :=
    ((time k : ZMod q), fun c => a (time k + (c : ℕ)))
  let N := Fintype.card State
  obtain ⟨x, y, hxy, hs⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Fin (N + 1) => state k.val) (by simp [N])
  have hvals : x.val ≠ y.val := fun h => hxy (Fin.ext h)
  have ordered : ∃ x y : ℕ, x < y ∧ state x = state y := by
    rcases lt_or_gt_of_ne hvals with hlt | hgt
    · exact ⟨x.val, y.val, hlt, hs⟩
    · exact ⟨y.val, x.val, hgt, hs.symm⟩
  obtain ⟨x, y, hxy, hs⟩ := ordered
  let i := time x
  let L := time y - time x
  have hxyZ : (x : ℤ) + 1 ≤ (y : ℤ) := by omega
  have hL : (H : ℤ) < L := by
    dsimp [L, time]
    have hH : (0 : ℤ) ≤ H := by omega
    nlinarith
  have hL0 : 0 < L := by omega
  have hphase : (q : ℤ) ∣ L := by
    have heq : (time x : ZMod q) = (time y : ZMod q) := congrArg Prod.fst hs
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub (time x) (time y) q).mp heq
  have hrows : ∀ c : Fin H, a (i + (c : ℕ)) = a (i + L + (c : ℕ)) := by
    intro c
    have heq := congrFun (congrArg Prod.snd hs) c
    change a (time x + (c : ℕ)) = a (time y + (c : ℕ)) at heq
    have htime : i + L = time y := by dsimp [i, L]; omega
    rw [htime]
    exact heq
  let b : ℤ → A := fun n => a (wrap i L n)
  refine ⟨b, L, hL0, hphase, ?_, ?_⟩
  · intro n
    exact congrArg a (wrap_add_period i L n)
  · intro n
    refine ⟨wrap i L n, ?_, ?_⟩
    · have hd : (q : ℤ) ∣ n - wrap i L n := hphase.trans (wrap_dvd i L n)
      simpa only [neg_sub] using (dvd_neg.mpr hd)
    · intro k hk0 hkH
      exact window_at_wrap a H i L hL hrows n k hk0 hkH

end PeriodicTilingThree.FiniteCylinder

end OAI
