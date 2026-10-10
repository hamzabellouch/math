import OAI.Geometry.PeriodicTiling.ChannelDigitBlocks
import OAI.Geometry.PeriodicTiling.LastDigit
import OAI.Geometry.PeriodicTiling.ActivationOffsets
import OAI.Geometry.PeriodicTiling.SharedSeedRegions
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

namespace PeriodicTilingThree.CommonModel

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

def ordinarySymbol (n : Column p) (x : Plane) : Symbol p :=
  lastDigit p E.p_prime (lineValue n x)

def ordinaryUseful (n : Column p) (x : Plane) (w : K E (.inl n)) : P E (.inl n) :=
  (channelDigitBlocks E (.inl n) (ordinarySymbol E n x)).C w

def ordinaryHigh (n : Column p) (x : Plane) (w : K E (.inl n)) : K E (.inl n) :=
  (channelDigitBlocks E (.inl n) (ordinarySymbol E n x)).T x.1 w

def ordinaryWord (x : Plane) : Word p := fun n => ordinarySymbol E n x

theorem ordinaryWord_allowed
    {p : ℕ} [NeZero p] (E : EncodingParameters p)
    (x : Plane) : Allowed p (ordinaryWord E x) := by
  have hword : ordinaryWord E x =
      (fun n : Column p => lastDigit p E.p_prime (x.1 * (n.val : ℤ) + x.2)) := by
    funext n
    change lastDigit p E.p_prime (lineValue n x) = _
    congr 1
    unfold lineValue
    ring
  rw [hword]
  exact lastDigit_affine_allowed p E.p_prime x.1 x.2

theorem ordinaryUseful_eq_of_lineValue_eq (n : Column p) {x y : Plane}
    (hxy : lineValue n x = lineValue n y) (w : K E (.inl n)) :
    ordinaryUseful E n x w = ordinaryUseful E n y w := by
  exact congrArg
    (fun t : ℤ => (channelDigitBlocks E (.inl n) (lastDigit p E.p_prime t)).C w) hxy

theorem ordinaryUseful_active_iff (n : Column p) (x : Plane) (j : Symbol p) :
    (∃ w w' : K E (.inl n), w - w' ∈ digitSubgroup E (.inl n) j ∧
      ordinaryUseful E n x w ≠ ordinaryUseful E n x w') ↔
        j = ordinarySymbol E n x :=
  channelDigitBlocks_active_iff E (.inl n) (ordinarySymbol E n x) j

theorem ordinarySymbol_offset (n : Column p) (x : Plane)
    (j : ActivationIndex E (.inl n)) :
    ordinarySymbol E n (x - ordinaryOffset E n j) = ordinarySymbol E n x := by
  unfold ordinarySymbol
  congr 1
  simp only [lineValue, ordinaryOffset, Prod.fst_sub, Prod.snd_sub]
  ring

theorem ordinaryUseful_offset (n : Column p) (x : Plane)
    (j : ActivationIndex E (.inl n)) (w : K E (.inl n)) :
    ordinaryUseful E n (x - ordinaryOffset E n j) w = ordinaryUseful E n x w := by
  exact congrArg (fun s : Symbol p => (channelDigitBlocks E (.inl n) s).C w)
    (ordinarySymbol_offset E n x j)

theorem ordinaryHigh_offset (n : Column p) (x : Plane)
    (j : ActivationIndex E (.inl n)) (w : K E (.inl n)) :
    ordinaryHigh E n (x - ordinaryOffset E n j) w =
      (channelDigitBlocks E (.inl n) (ordinarySymbol E n x)).T
        (x.1 - (ordinaryOffset E n j).1) w := by
  exact congrArg (fun s : Symbol p => (channelDigitBlocks E (.inl n) s).T
    (x.1 - (ordinaryOffset E n j).1) w) (ordinarySymbol_offset E n x j)

theorem ordinarySymbol_val_of_residue
    {p : ℕ} [NeZero p] (E : EncodingParameters p)
    (n : Column p) (x : Plane)
    (t : ZMod p) (ht : t ≠ 0)
    (hx₁ : (x.1 : ZMod p) = 0) (hx₂ : (x.2 : ZMod p) = t) :
    (ordinarySymbol E n x : ZMod p) = t := by
  have hv : (lineValue n x : ZMod p) = t := by
    simp [lineValue, hx₁, hx₂]
  have hnot : ¬ (p : ℤ) ∣ lineValue n x := by
    intro h
    have hz : (lineValue n x : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    exact ht (hv.symm.trans hz)
  exact (lastDigit_eq_of_not_dvd p E.p_prime hnot).trans hv

theorem reduce_residue
    {p : ℕ} [NeZero p]
    (x : Plane) :
    SharedSeed.reduce p (SharedSeed.residue p x) =
      ((x.1 : ZMod p), (x.2 : ZMod p)) := by
  simp [SharedSeed.reduce, SharedSeed.residue]

theorem ordinarySymbol_firstRegion (n : Column p) (x : Plane)
    (hx : SharedSeed.residue p x ∈ SharedSeed.firstRegion p) :
    ordinarySymbol E n x = 1 := by
  let : Fact (1 < p) := ⟨E.p_prime.one_lt⟩
  have h := SharedSeed.reduce_of_firstRegion hx
  rw [reduce_residue (p := p) x] at h
  apply Units.ext
  exact ordinarySymbol_val_of_residue E n x 1 one_ne_zero
    (congrArg Prod.fst h) (congrArg Prod.snd h)

theorem ordinarySymbol_secondRegion (n : Column p) (x : Plane)
    (hx : SharedSeed.residue p x ∈ SharedSeed.secondRegion p) :
    ordinarySymbol E n x = lastDigit p E.p_prime 2 := by
  have h := SharedSeed.reduce_of_secondRegion hx
  rw [reduce_residue (p := p) x] at h
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
    have hlarge := E.p_large
    omega
  apply Units.ext
  rw [lastDigit_two p E.p_prime (by have h := E.p_large; omega)]
  exact ordinarySymbol_val_of_residue E n x 2 htwo
    (congrArg Prod.fst h) (congrArg Prod.snd h)

end PeriodicTilingThree.CommonModel

end

end OAI
