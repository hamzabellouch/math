import OAI.NumberTheory.Ostmann.Arithmetic.FrequencyModelPairSupport
import OAI.NumberTheory.Ostmann.Arithmetic.FrozenMovingSamples

namespace OAI

/-! # Adaptive arithmetic data is fixed while the bulk residues vary -/

namespace Ostmann
open scoped Classical

theorem movingFrameConstants_congr {σ : Type*} (v w : σ → ℕ) (n : ℕ)
    (small : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n)
    (hsmall : movingSlotValues v n small = movingSlotValues w n small)
    (ha : a.values v = a.values w) (path : List Bool) :
    movingFrameConstants v n small a path = movingFrameConstants w n small a path := by
  induction a generalizing path with
  | leaf => rfl
  | @node n a l r ihL ihR =>
    have hsL := congrArg Prod.fst hsmall
    have hsR := congrArg Prod.snd hsmall
    dsimp only [movingSlotValues] at hsL hsR
    have hc : movingCompensationValues v n a = movingCompensationValues w n a := by
      injection ha
    have hl : l.values v = l.values w := by injection ha
    have hr : r.values v = r.values w := by injection ha
    have hu : movingSlotValues v n (movingCompensationSlots n a) =
        movingSlotValues w n (movingCompensationSlots n a) := by
      rw [movingCompensationValues_product, movingCompensationValues_product, hc]
    cases path with
    | nil =>
      simp only [movingFrameConstants, movingSlotValues_flatten, hsL, hsR, hu]
    | cons b path =>
      have hleft : movingSlotValues v n (appendMovingSlotLeaves n (movingCompensationSlots n a) small.1) =
          movingSlotValues w n (appendMovingSlotLeaves n (movingCompensationSlots n a) small.1) := by
        rw [movingSlotValues_append, movingSlotValues_append, hu, hsL]
      have hright : movingSlotValues v n (appendMovingSlotLeaves n (movingCompensationSlots n a) small.2) =
          movingSlotValues w n (appendMovingSlotLeaves n (movingCompensationSlots n a) small.2) := by
        rw [movingSlotValues_append, movingSlotValues_append, hu, hsR]
      cases b
      · exact ihL _ hleft hl path
      · exact ihR _ hright hr path

theorem frequencyModelAncestorScheme_congr {σ : Type*} (v w : σ → ℕ)
    (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (small : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (x y : ℤ)
    (hsmall : movingSlotValues v n small = movingSlotValues w n small)
    (ha : a.values v = a.values w) :
    frequencyModelAncestorScheme v S n t small a x y =
      frequencyModelAncestorScheme w S n t small a x y := by
  unfold frequencyModelAncestorScheme
  congr 1
  · funext path
    rw [movingFrameConstants_congr v w n small a hsmall ha path]
  · funext path
    rw [movingFrameConstants_congr v w n small a hsmall ha path]

theorem movingSampleCompensation_congr {σ : Type*} (v w : σ → ℕ) (n : ℕ)
    (small : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n)
    (hsmall : movingSlotValues v n small = movingSlotValues w n small)
    (ha : a.values v = a.values w) :
    movingSampleCompensation v n small a = movingSampleCompensation w n small a := by
  funext j
  unfold movingSampleCompensation
  rw [movingFrameConstants_congr v w n small a hsmall ha]

theorem frequencyModelAdaptiveData_congr {σ : Type*} (v w : σ → ℕ)
    (S : Finset ℤ) (n R : ℕ) (t : FrequencyTree S n)
    (hS : ∀ s ∈ S, s ≠ 0) (hR : ∀ j : Fin (2 ^ n - 1), (singleTreeNodeFrequencies S n t j.val).root.natAbs ∣ R)
    (small : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (x y : ℤ)
    (hsmall : movingSlotValues v n small = movingSlotValues w n small)
    (ha : a.values v = a.values w) :
    frequencyModelAdaptiveData v S n R t hS hR small a x y =
      frequencyModelAdaptiveData w S n R t hS hR small a x y := by
  unfold frequencyModelAdaptiveData
  have aux {D E : PivotDependencyScheme (2 ^ n - 1)}
      {U V : Fin (2 ^ n - 1) → ℤ} (he : D = E) (hu : U = V)
      (hsD : ∀ i, (D.frequencies i).root ≠ 0) (hsE : ∀ i, (E.frequencies i).root ≠ 0)
      (hrD : ∀ i, (D.frequencies i).root.natAbs ∣ R)
      (hrE : ∀ i, (E.frequencies i).root.natAbs ∣ R) :
      modularAdaptiveData n R (n - 1) D U hsD hrD =
        modularAdaptiveData n R (n - 1) E V hsE hrE := by
    subst E
    subst V
    rfl
  exact aux (frequencyModelAncestorScheme_congr v w S n t small a x y hsmall ha)
    (movingSampleCompensation_congr v w n small a hsmall ha) _ _ _ _

theorem frequencyModelPairData_congr {σ : Type*} (v w : σ → ℕ)
    (S : Finset ℤ) (n R : ℕ) (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0) (hR : ∀ b (j : Fin (2 ^ n - 1)),
    (singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j.val).root.natAbs ∣ R)
    (small : Bool → TreeLeafTuple (List σ) n) (a : Bool → MovingSampleSlots σ n) (x y : ℤ)
    (hsmall : ∀ b, movingSlotValues v n (small b) = movingSlotValues w n (small b))
    (ha : ∀ b, (a b).values v = (a b).values w) :
    frequencyModelPairData v S n R t hS hR small a x y =
      frequencyModelPairData w S n R t hS hR small a x y := by
  funext total past
  unfold frequencyModelPairData
  rw [frequencyModelAdaptiveData_congr v w S n R _ hS (hR false) (small false) (a false) x y
      (hsmall false) (ha false),
    frequencyModelAdaptiveData_congr v w S n R _ hS (hR true) (small true) (a true) x y
      (hsmall true) (ha true)]

end Ostmann

end OAI
