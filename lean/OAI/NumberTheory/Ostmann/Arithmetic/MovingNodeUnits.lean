import OAI.NumberTheory.Ostmann.Arithmetic.MovingCompensatedEquations
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRecursiveSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFrequencyResidues

namespace OAI

/-! # Coefficient units forced by the original local support masks -/

namespace Ostmann
open scoped Classical

theorem movingNodeAtPath_root {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (t : FrequencyTree ℤ n) (hT : T.Follows t) (XL XR : ℕ) (path : List Bool) :
    let z := transferNodeAtPath (movingSlotSystem value childBound pivotBound) n
      ⟨n, T, XL, XR⟩ t path
    z.state.data.frequency = z.root := by
  induction T generalizing XL XR path with
  | leaf s C => exact hT
  | node s CL CR U l r ihL ihR =>
    cases path with
    | nil => exact hT.1
    | cons b path =>
      cases b
      · exact ihL t.2.1 hT.2.1 _ XL path
      · exact ihR t.2.2 hT.2.2 _ XR path

theorem MovingSlotData.frequency_dvd_product {σ : Type*} {n : ℕ} (T : MovingSlotData σ n) :
    T.frequency ∣ T.frequencyProduct := by
  cases T with
  | leaf => exact dvd_refl _
  | node => exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _

theorem movingLocalSupport_products_units {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) (x : MovingSlotState σ) (s : ℤ)
    (hs : x.data.frequency = s) (hsmall : ∀ i, IsCoprime (value i : ℤ) s)
    (hx : movingLocalSupport value outside x) :
    IsCoprime (x.leftProduct value : ℤ) s ∧ IsCoprime (x.rightProduct value : ℤ) s := by
  have hL : IsCoprime (x.leftGiant : ℤ) s :=
    hs ▸ hx.2.1.of_isCoprime_of_dvd_right x.data.frequency_dvd_product
  have hR : IsCoprime (x.rightGiant : ℤ) s :=
    hs ▸ hx.2.2.1.of_isCoprime_of_dvd_right x.data.frequency_dvd_product
  rcases x with ⟨n, T, XL, XR⟩
  cases T with
  | leaf => exact ⟨isCoprime_one_left, isCoprime_one_left⟩
  | node f CL CR U l r =>
    constructor
    · exact_mod_cast hL.mul_left (movingNaturalProduct_coprime value CL s (fun i _ => hsmall i))
    · exact_mod_cast hR.mul_left (movingNaturalProduct_coprime value CR s (fun i _ => hsmall i))

theorem movingSlotWeight_node_localSupport {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (x : MovingSlotState σ) (t : FrequencyTree ℤ n)
    (hw : recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound (movingGuardedExtra value outside E)) n x t ≠ 0)
    (j : Fin (2 ^ n - 1)) :
    movingLocalSupport value outside
      (transferNodeArray (movingSlotSystem value childBound pivotBound) n x t j).state := by
  let sys := movingSlotSystem value childBound pivotBound
  let z := transferNodeArray sys n x t j
  have hz : z ∈ transferNodeList sys n x t := by
    unfold z transferNodeArray
    rw [List.getD_eq_getElem _ _ (by rw [transferNodeList_length]; exact j.isLt)]
    exact List.getElem_mem _
  have hc := recursiveTransferWeight_node_cutoff_ne_zero sys F
    (movingSlotCutoff value childBound pivotBound (movingGuardedExtra value outside E))
    n x t hw z hz
  rw [movingSlotCutoff_guarded] at hc
  by_contra hn
  exact hc (ite_eq_right hn)

theorem movingSample_coefficient_units {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (small bulk : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (XL XR : ℕ)
    (hsmall : ∀ i s, s ∈ S → IsCoprime (value i : ℤ) s)
    (hw : recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound (movingGuardedExtra value outside E)) n
      ⟨n, buildMovingSlotData n (frequencyTreeMap Subtype.val n t) small bulk a, XL, XR⟩
      (frequencyTreeMap Subtype.val n t) ≠ 0) (j : Fin (2 ^ n - 1)) :
    let D := movingSampleAncestorScheme value S n t small a XL XR
    let tz := frequencyTreeMap Subtype.val n t
    let p := movingGiantArray value childBound pivotBound n
      ⟨n, buildMovingSlotData n tz small bulk a, XL, XR⟩ tz
    IsCoprime (D.leftCoefficient p j) (D.frequencies j).root ∧
      IsCoprime (D.rightCoefficient p j) (D.frequencies j).root := by
  dsimp only
  let sys := movingSlotSystem value childBound pivotBound
  let tz := frequencyTreeMap Subtype.val n t
  let T := buildMovingSlotData n tz small bulk a
  let x : MovingSlotState σ := ⟨n, T, XL, XR⟩
  let z := transferNodeArray sys n x tz j
  have hlocal := movingSlotWeight_node_localSupport value outside childBound pivotBound F E n x tz hw j
  have hf := transferNodeArray_frequencies sys S n x t j
  have hroot := congrArg NodeFrequencies.root hf
  dsimp only [ReconstructedTransferNode.frequencies] at hroot
  have hr := movingNodeAtPath_root value childBound pivotBound T tz
    (buildMovingSlotData_follows n tz small bulk a) XL XR (preorderNodePath n j)
  rw [← transferNodeArray_path] at hr
  have hu := movingLocalSupport_products_units value outside z.state z.root hr
    (fun i => hroot.symm ▸ hsmall i _ (singleTreeNodeFrequencies_root_mem S n t j.val j.isLt)) hlocal
  have hp := movingSampleNode_products value childBound pivotBound S n t small bulk a XL XR j
  rw [hp.2.1, hp.2.2, hroot] at hu
  exact ⟨hu.2.of_mul_left_left, hu.1.of_mul_left_left⟩

end Ostmann

end OAI
