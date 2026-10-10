import OAI.Geometry.PeriodicTiling.SharedSeedSizeTransport
import OAI.Geometry.PeriodicTiling.ChannelDigitBlocks
import OAI.Geometry.PeriodicTiling.ActivationOffsets

namespace OAI

noncomputable section

namespace PeriodicTilingThree

open SharedSeed

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

theorem seedOneSize
    {p : ℕ} [NeZero p] (E : EncodingParameters p)
    : E.a (.inr (0 : Fin 2)) = 2 := by
  simpa using E.seed_a (0 : Fin 2)

theorem seedTwoSize
    {p : ℕ} [NeZero p] (E : EncodingParameters p)
    : E.a (.inr (1 : Fin 2)) = 3 := by
  simpa using E.seed_a (1 : Fin 2)

def seedUseful (t : Fin 2) : Residues p → K E (.inr t) → P E (.inr t) :=
  Fin.cases
    (fun s u => usefulOneOfEq (seedOneSize E) (channelDigitBlocks E (.inr 0) ()) u
      (residueEquiv E.p_prime E.p_large s))
    (fun j => by
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact fun s u => usefulTwoOfEq (seedTwoSize E) (channelDigitBlocks E (.inr 1) ()) u
        (residueEquiv E.p_prime E.p_large s)) t

def seedHigh (t : Fin 2) : ℤ → Residues p → K E (.inr t) → K E (.inr t) :=
  Fin.cases
    (fun x s u => highOneOfEq (seedOneSize E) (channelDigitBlocks E (.inr 0) ()) x u
      (residueEquiv E.p_prime E.p_large s))
    (fun j => by
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact fun x s u => highTwoOfEq (seedTwoSize E) (channelDigitBlocks E (.inr 1) ()) x u
        (residueEquiv E.p_prime E.p_large s)) t

@[simp] theorem seedUseful_zero (s : Residues p) (u : K E (.inr (0 : Fin 2))) :
    seedUseful E 0 s u =
      usefulOneOfEq (seedOneSize E) (channelDigitBlocks E (.inr 0) ()) u
        (residueEquiv E.p_prime E.p_large s) := rfl

@[simp] theorem seedUseful_one (s : Residues p) (u : K E (.inr (1 : Fin 2))) :
    seedUseful E 1 s u =
      usefulTwoOfEq (seedTwoSize E) (channelDigitBlocks E (.inr 1) ()) u
        (residueEquiv E.p_prime E.p_large s) := rfl

@[simp] theorem seedHigh_zero (x : ℤ) (s : Residues p) (u : K E (.inr (0 : Fin 2))) :
    seedHigh E 0 x s u =
      highOneOfEq (seedOneSize E) (channelDigitBlocks E (.inr 0) ()) x u
        (residueEquiv E.p_prime E.p_large s) := rfl

@[simp] theorem seedHigh_one (x : ℤ) (s : Residues p) (u : K E (.inr (1 : Fin 2))) :
    seedHigh E 1 x s u =
      highTwoOfEq (seedTwoSize E) (channelDigitBlocks E (.inr 1) ()) x u
        (residueEquiv E.p_prime E.p_large s) := rfl

def seedC (t : Fin 2) (x : Plane) (k : Input E) : P E (.inr t) :=
  seedUseful E t (residue p x) (k (.inr t))

def seedBeta (t : Fin 2) (x : Plane) (k : Input E) : K E (.inr t) :=
  seedHigh E t x.1 (residue p x) (k (.inr t))

theorem seedC_eq_of_residue_low (t : Fin 2) {x y : Plane} {k l : Input E}
    (hx : residue p x = residue p y) (hk : k (.inr t) = l (.inr t)) :
    seedC E t x k = seedC E t y l := by
  simp only [seedC, hx, hk]

def seedSourceInput (t : Fin 2) (k : Input E) (j : SeedActivationIndex E t) : Input E :=
  Function.update k (.inr t) (k (.inr t) - j.1.1)

@[simp] theorem seedSourceInput_same (t : Fin 2) (k : Input E)
    (j : SeedActivationIndex E t) :
    seedSourceInput E t k j (.inr t) = k (.inr t) - j.1.1 := by
  simp [seedSourceInput]

theorem seedSourceInput_low (t : Fin 2) (k : Input E) (j : SeedActivationIndex E t) :
    seedSourceInput E t k j (.inr t) =
      k (.inr t) - ((seedOffset E t j).1 : K E (.inr t)) := by
  rw [seedSourceInput_same, seedOffset_low]

theorem seed_source_residue (t : Fin 2) (x : Plane) (j : SeedActivationIndex E t) :
    residue p (x - seedOffset E t j) = residue p x - j.2 := by
  have hs : residue p (seedOffset E t j) = j.2 := seedOffset_residue E t j
  have hfirst : ((seedOffset E t j).1 : ZMod (p ^ 2)) = j.2.1 := congrArg Prod.fst hs
  have hsecond : ((seedOffset E t j).2 : ZMod (p ^ 2)) = j.2.2 := congrArg Prod.snd hs
  apply Prod.ext
  · change ((x.1 - (seedOffset E t j).1 : ℤ) : ZMod (p ^ 2)) =
      (x.1 : ZMod (p ^ 2)) - j.2.1
    rw [Int.cast_sub, hfirst]
  · change ((x.2 - (seedOffset E t j).2 : ℤ) : ZMod (p ^ 2)) =
      (x.2 : ZMod (p ^ 2)) - j.2.2
    rw [Int.cast_sub, hsecond]

def seedActualForward (t : Fin 2) (x : Plane) (k : Input E)
    (j : SeedActivationIndex E t) : (P E (.inr t) × K E (.inr t)) × ZMod (D p) :=
  let x' := x - seedOffset E t j
  let k' := seedSourceInput E t k j
  ((seedC E t x' k' + shift (E.a (.inr t)) (E.b (.inr t)) j.1.2,
    seedBeta E t x' k'), commonZ E.p_prime E.p_large x' k')

theorem seedActualForward_zero_eq (x : Plane) (k : Input E) :
    seedActualForward E 0 x k =
      oneForwardOfEq (seedOneSize E) (channelDigitBlocks E (.inr 0) ())
        (BlockShiftData.ofMultiplicity (E.a_two_le (.inr 0)) (E.b_two_le (.inr 0)))
        (residueEquiv E.p_prime E.p_large) (outputEquiv E.p_large)
        (fun j => (seedOffset E 0 j).1) x.1 (residue p x) (k (.inr 0)) := by
  funext j
  simp only [seedActualForward, seedC, seedBeta, seedSourceInput_same,
    seed_source_residue, seedUseful_zero, seedHigh_zero, commonZ,
    oneForwardOfEq, BlockShiftData.ofMultiplicity, Prod.fst_sub]

theorem seedActualForward_one_eq (x : Plane) (k : Input E) :
    seedActualForward E 1 x k =
      twoForwardOfEq (seedTwoSize E) (channelDigitBlocks E (.inr 1) ())
        (BlockShiftData.ofMultiplicity (E.a_two_le (.inr 1)) (E.b_two_le (.inr 1)))
        (residueEquiv E.p_prime E.p_large) (outputEquiv E.p_large)
        (fun j => (seedOffset E 1 j).1) x.1 (residue p x) (k (.inr 1)) := by
  funext j
  simp only [seedActualForward, seedC, seedBeta, seedSourceInput_same,
    seed_source_residue, seedUseful_one, seedHigh_one, commonZ,
    twoForwardOfEq, BlockShiftData.ofMultiplicity, Prod.fst_sub]

theorem seedActualForward_bijective (t : Fin 2) (x : Plane) (k : Input E) :
    Function.Bijective (seedActualForward E t x k) := by
  fin_cases t
  · change Function.Bijective (seedActualForward E (0 : Fin 2) x k)
    rw [seedActualForward_zero_eq]
    apply oneForwardOfEq_bijective
    · intro j
      exact seedOffset_rhoA E 0 j
    · intro j
      exact seedOffset_rhoB E 0 j
    · intro j
      have h := seedOffset_other E (0 : Fin 2) j
      have ha : E.a (.inr (otherSeed (0 : Fin 2))) = 3 := by
        change E.a (.inr (1 : Fin 2)) = 3
        exact seedTwoSize E
      exact Eq.mp (congrArg (fun modulus : ℕ =>
        ((seedOffset E (0 : Fin 2) j).1 : ZMod modulus) = 0) ha) h
  · change Function.Bijective (seedActualForward E (1 : Fin 2) x k)
    rw [seedActualForward_one_eq]
    apply twoForwardOfEq_bijective
    · intro j
      exact seedOffset_rhoA E 1 j
    · intro j
      exact seedOffset_rhoB E 1 j
    · intro j
      have h := seedOffset_other E (1 : Fin 2) j
      have ha : E.a (.inr (otherSeed (1 : Fin 2))) = 2 := by
        change E.a (.inr (0 : Fin 2)) = 2
        exact seedOneSize E
      exact Eq.mp (congrArg (fun modulus : ℕ =>
        ((seedOffset E (1 : Fin 2) j).1 : ZMod modulus) = 0) ha) h

theorem both_seed_tests (x : Plane) (k : Input E) :
    Function.Bijective (seedActualForward E 0 x k) ∧
      Function.Bijective (seedActualForward E 1 x k) :=
  ⟨seedActualForward_bijective E 0 x k, seedActualForward_bijective E 1 x k⟩

def seedActiveRegion (p : ℕ) (t : Fin 2) : Set (Residues p) :=
  if t = 0 then firstRegion p else secondRegion p

theorem seedUseful_active_iff (t : Fin 2) (s : Residues p) :
    (∃ u v : K E (.inr t), u - v ∈ digitSubgroup E (.inr t) () ∧
      seedUseful E t s u ≠ seedUseful E t s v) ↔ s ∈ seedActiveRegion p t := by
  classical
  fin_cases t
  · change (∃ u v : K E (.inr (0 : Fin 2)),
        u - v ∈ digitSubgroup E (.inr (0 : Fin 2)) () ∧
        seedUseful E 0 s u ≠ seedUseful E 0 s v) ↔
          s ∈ seedActiveRegion p (0 : Fin 2)
    have hC := (channelDigitBlocks_active_iff E (.inr (0 : Fin 2)) () ()).mpr rfl
    have hlabel : ActiveOne (residueEquiv E.p_prime E.p_large s) ↔ s ∈ firstRegion p := by
      rw [← residueEquiv_first_iff E.p_prime E.p_large s]
      cases hs : residueEquiv E.p_prime E.p_large s <;> simp [ActiveOne]
    have h := usefulOneOfEq_activity_iff (seedOneSize E) (channelDigitBlocks E (.inr 0) ())
      (fun u v => u - v ∈ digitSubgroup E (.inr 0) ()) hC
      (residueEquiv E.p_prime E.p_large s)
    rw [seedActiveRegion, ite_eq_left (rfl : (0 : Fin 2) = 0)]
    simpa only [seedUseful_zero] using h.trans hlabel
  · change (∃ u v : K E (.inr (1 : Fin 2)),
        u - v ∈ digitSubgroup E (.inr (1 : Fin 2)) () ∧
        seedUseful E 1 s u ≠ seedUseful E 1 s v) ↔
          s ∈ seedActiveRegion p (1 : Fin 2)
    have hC := (channelDigitBlocks_active_iff E (.inr (1 : Fin 2)) () ()).mpr rfl
    have hlabel : ActiveTwo (residueEquiv E.p_prime E.p_large s) ↔ s ∈ secondRegion p := by
      rw [← residueEquiv_second_iff E.p_prime E.p_large s]
      cases hs : residueEquiv E.p_prime E.p_large s with
      | inl y => simp [ActiveTwo]
      | inr u => cases u <;> simp [ActiveTwo]
    have h := usefulTwoOfEq_activity_iff (seedTwoSize E) (channelDigitBlocks E (.inr 1) ())
      (fun u v => u - v ∈ digitSubgroup E (.inr 1) ()) hC
      (residueEquiv E.p_prime E.p_large s)
    simpa only [seedUseful_one, seedActiveRegion, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
      using h.trans hlabel

end PeriodicTilingThree

end

end OAI
