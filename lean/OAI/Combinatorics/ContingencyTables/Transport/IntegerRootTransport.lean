import OAI.Combinatorics.ContingencyTables.Transport.IntegerRecursivePotential
import OAI.Combinatorics.ContingencyTables.Transport.IntegerLeafEnergy
import OAI.Combinatorics.ContingencyTables.Transport.IntegerRootEstimate

namespace OAI

/-! # Root transport with the actual auxiliary defect sum

The auxiliary kernel gives one ordinary slot occupancy M+1 and all
others their balances. Removing the two special coordinates leaves the
special slot negative, exactly the root defects in the manuscript.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Matrix
open FactorialSignatures BalancedFamily BalancedEnumeration IntegerMarginal

universe u

noncomputable def auxiliaryKernel {I : Type u} : (Ms : List ℕ) →
    ((Coordinates I Ms → ℕ) → ℝ) → (I → ℕ) → ℝ
  | [], _ => fun _ => 0
  | U::Ms, F => fun z => marginal (exposedFamily Ms F) (U+1) z +
      auxiliaryKernel Ms (marginal F U) z

theorem auxiliaryKernel_nonnegative {I : Type u} (Ms : List ℕ)
    (F : (Coordinates I Ms → ℕ) → ℝ) (hF : ∀ x, 0 ≤ F x) (z : I → ℕ) :
    0 ≤ auxiliaryKernel Ms F z := by
  induction Ms with
  | nil => exact le_rfl
  | cons U Ms ih =>
    apply add_nonneg
    · apply Finset.sum_nonneg
      intro j _
      exact eliminate_nonnegative Ms _ (fun x => hF _) _
    · exact ih _ (fun x => Finset.sum_nonneg (fun j _ => hF _))

lemma weightedFuture_upper {I : Type u} (F : ((I ⊕ Bool) → ℕ) → ℝ)
    (M W : ℕ) (hM : M ≤ W+1) (hF : ∀ x, 0 ≤ F x) (z : I → ℕ) :
    weightedFuture F M z ≤ ((W:ℝ)+1)^2 * marginal F M z := by
  unfold weightedFuture marginal
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have haM : a ≤ M := by have := Finset.mem_range.mp ha; omega
  have haR : (a:ℝ) ≤ M := by exact_mod_cast haM
  have hMR : (M:ℝ) ≤ (W:ℝ)+1 := by exact_mod_cast hM
  apply mul_le_mul_of_nonneg_right _ (hF _)
  calc
    _ ≤ ((W:ℝ)+1)*((W:ℝ)+1) :=
      mul_le_mul (haR.trans hMR) (by linarith) (by linarith) (by positivity)
    _ = _ := by ring

theorem correctionKernel_upper {I : Type u} (Ms : List ℕ)
    (F : (Coordinates I Ms → ℕ) → ℝ) (W : ℕ)
    (hwidth : ∀ U ∈ Ms, U ≤ W) (hF : ∀ x, 0 ≤ F x) (z : I → ℕ) :
    correctionKernel Ms F z ≤ ((W:ℝ)+1)^2 * auxiliaryKernel Ms F z := by
  induction Ms with
  | nil => simp [correctionKernel,auxiliaryKernel]
  | cons U Ms ih =>
    have hcur := weightedFuture_upper (exposedFamily Ms F) (U+1) W
      (by have := hwidth U (by simp); omega)
      (fun x => eliminate_nonnegative Ms _ (fun p => hF _) _) z
    have htail := ih (marginal F U) (fun V hV => hwidth V (by simp [hV]))
      (fun x => Finset.sum_nonneg (fun j _ => hF _))
    change _+_ ≤ ((W:ℝ)+1)^2 * (_+_)
    linarith

lemma removal_nonnegative {C : Type*} [DecidableEq C] (F : (C → ℕ) → ℝ)
    (hF : ∀ x, 0 ≤ F x) (z : C → ℕ) (i j : C) :
    0 ≤ integerRemovalMatrix F z i j := by
  unfold integerRemovalMatrix
  split_ifs
  · exact hF _
  · exact le_rfl

lemma correction_offdiagonal_upper (Ms : List ℕ)
    (F : (Coordinates Bool Ms → ℕ) → ℝ) (W : ℕ)
    (hwidth : ∀ U ∈ Ms, U ≤ W) (hF : ∀ x, 0 ≤ F x) (z : Bool → ℕ) :
    integerRemovalMatrix (correctionKernel Ms F) z false true ≤
      ((W:ℝ)+1)^2 * integerRemovalMatrix (auxiliaryKernel Ms F) z false true := by
  unfold integerRemovalMatrix
  split_ifs
  · exact correctionKernel_upper Ms F W hwidth hF _
  · simp

lemma root_balance (f : (Bool → ℕ) → ℝ) (z : Bool → ℕ)
    (hs : 0 < oneHole f z false) (ht : 0 < oneHole f z true) :
    holeLinear f z (rootCoefficients (oneHole f z false) (oneHole f z true))=0 := by
  simp only [holeLinear,Fintype.sum_bool,rootCoefficients,Bool.false_eq_true,↓reduceIte]
  field_simp [ne_of_gt hs,ne_of_gt ht]
  ring

lemma root_holePotential (f : (Bool → ℕ) → ℝ) (z : Bool → ℕ)
    (hs : 0 < oneHole f z false) (ht : 0 < oneHole f z true) :
    holePotential f z (rootCoefficients (oneHole f z false) (oneHole f z true)) =
      1/oneHole f z false+1/oneHole f z true := by
  simpa only [holePotential,Fintype.sum_bool,rootCoefficients,
    Bool.false_eq_true,↓reduceIte] using root_potential _ _ hs ht

/-- The root potential estimate for the actual integer recursion. The
only weight-dependent denominators are its two positive endpoint masses. -/
theorem recursive_root_potential (Ms : List ℕ)
    (F : (Coordinates Bool Ms → ℕ) → ℝ) (m z : Bool → ℕ) (R W : ℕ)
    (hlower : ∀ U ∈ Ms, 2 ≤ U) (hupper : ∀ U ∈ Ms, U ≤ W)
    (hF : ∀ x, 0 ≤ F x)
    (hpos : BalancedBox.PositiveSlice F (bounds m Ms) (R+Ms.sum))
    (hsig : BalancedBox.RemovalSlice F (bounds m Ms) (R+Ms.sum))
    (hz : BalancedBox.InBox m z) (htotal : (∑ i, z i)=R+1)
    (hs : 0 < oneHole (eliminate Ms F) z false)
    (ht : 0 < oneHole (eliminate Ms F) z true) :
    let s := oneHole (eliminate Ms F) z false
    let t := oneHole (eliminate Ms F) z true
    let c := integerRemovalMatrix (auxiliaryKernel Ms F) z false true
    recursivePotential Ms F z (rootCoefficients s t) ≤
      1/s+1/t+2*((W:ℝ)+1)^2*c/(s*t) := by
  dsimp only
  have hp := recursivePotential_bound Ms F m z R
    (rootCoefficients _ _) hlower hF hpos hsig hz htotal (root_balance _ _ hs ht)
  rw [root_holePotential _ _ hs ht] at hp
  have hq := root_future_bound (integerRemovalMatrix (correctionKernel Ms F) z)
    (oneHole (eliminate Ms F) z false) (oneHole (eliminate Ms F) z true)
    (((W:ℝ)+1)^2) (integerRemovalMatrix (auxiliaryKernel Ms F) z false true)
    hs ht (integerRemoval_symm _ _ _ _)
    (removal_nonnegative _ (correctionKernel_nonnegative Ms F hF) _ _ _)
    (removal_nonnegative _ (correctionKernel_nonnegative Ms F hF) _ _ _)
    (correction_offdiagonal_upper Ms F W hupper hF z)
  linarith

/-- The softened integer transport on the actual exchange graph. All
recursive coefficients and future forms have been eliminated. -/
theorem integer_root_graph_transport (Ms : List ℕ)
    (F H : (Coordinates Bool Ms → ℕ) → ℝ) (m z : Bool → ℕ) (R W : ℕ)
    (hlower : ∀ U ∈ Ms, 2 ≤ U) (hupper : ∀ U ∈ Ms, U ≤ W)
    (hF : ∀ x, 0 ≤ F x)
    (hpos : BalancedBox.PositiveSlice F (bounds m Ms) (R+Ms.sum))
    (hsig : BalancedBox.RemovalSlice F (bounds m Ms) (R+Ms.sum))
    (hz : BalancedBox.InBox m z) (htotal : (∑ i, z i)=R+1)
    (hs : 0 < oneHole (eliminate Ms F) z false)
    (ht : 0 < oneHole (eliminate Ms F) z true)
    (V : Finset (Coordinates Bool Ms → ℕ)) (hV : leafVertices Ms z ⊆ V) :
    let s := oneHole (eliminate Ms F) z false
    let t := oneHole (eliminate Ms F) z true
    let c := integerRemovalMatrix (auxiliaryKernel Ms F) z false true
    (holeLinear (eliminate Ms (fun p => F p*H p)) z (rootCoefficients s t))^2 ≤
      (1/s+1/t+2*((W:ℝ)+1)^2*c/(s*t)) * integerGraphEnergy V F H := by
  dsimp only
  have hp := recursive_root_potential Ms F m z R W hlower hupper hF hpos hsig hz htotal hs ht
  have hb := integer_recursive_transport_of_slice Ms F H m z R (rootCoefficients _ _)
    hF hpos hz htotal (root_balance _ _ hs ht)
  have he := recursiveEnergy_le_graphEnergy Ms F H z (rootCoefficients
    (oneHole (eliminate Ms F) z false) (oneHole (eliminate Ms F) z true)) hF V hV
  have hpn := recursivePotential_nonnegative Ms F z (rootCoefficients
    (oneHole (eliminate Ms F) z false) (oneHole (eliminate Ms F) z true)) hF
  have hen := recursiveEnergy_nonnegative Ms F H z (rootCoefficients
    (oneHole (eliminate Ms F) z false) (oneHole (eliminate Ms F) z true)) hF
  exact hb.trans ((mul_le_mul_of_nonneg_right hp hen).trans
    (mul_le_mul_of_nonneg_left he (hpn.trans hp)))

end ContingencyTables.IntegerWeightedTransport

end OAI
