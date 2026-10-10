import OAI.Combinatorics.ContingencyTables.Transport.AuxiliaryRepairMass
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperContextBox
import OAI.Combinatorics.ContingencyTables.Transport.IntegerTransportCoefficient

namespace OAI

/-! # Adjacent physical exposure means with the repaired coefficient -/

namespace ContingencyTables.ExcessContextProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open BalancedEnumeration IntegerWeightedTransport FirstPaperProfiles
open FirstPaperContextTransport FirstPaperPhysicalMarginal IntegerBoxTruncation
open PaddedCompletions CompletionCounts FactorialSignatures

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

def rootDisplay (U l : ℕ) : Bool → ℕ := fun b => if b then U-l+1 else l

lemma rootDisplay_inBox (U l : ℕ) (hl0 : 1 ≤ l) (hlU : l ≤ U) :
    InBox (fun _ : Bool => U) (rootDisplay U l) := by
  intro b
  cases b
  · exact hlU
  · change U-l+1 ≤ U
    omega

lemma rootDisplay_total (U l : ℕ) (hlU : l ≤ U) :
    (∑ b, rootDisplay U l b)=U+1 := by
  simp only [rootDisplay,Fintype.sum_bool,Bool.false_eq_true,↓reduceIte]
  omega

lemma rootDisplay_remove_false (U l : ℕ) (hl0 : 1 ≤ l) (hlU : l ≤ U) :
    removeOne (rootDisplay U l) false=childProfile U (l-1) := by
  funext b
  cases b <;> simp only [removeOne,rootDisplay,childProfile,Bool.false_eq_true,Bool.true_eq_false,↓reduceIte]
  omega

lemma rootDisplay_remove_true (U l : ℕ) :
    removeOne (rootDisplay U l) true=childProfile U l := by
  funext b
  cases b <;> simp [removeOne,rootDisplay,childProfile]

lemma rootDisplay_remove_two (U l : ℕ) :
    removeTwo (rootDisplay U l) false true=auxRoot U l := by
  funext b
  cases b <;> simp [removeTwo,removeOne,rootDisplay,auxRoot]

lemma rootDisplay_oneHole_false (F : (Bool → ℕ) → ℝ) (U l : ℕ)
    (hl0 : 1 ≤ l) (hlU : l ≤ U) :
    oneHole F (rootDisplay U l) false=F (childProfile U (l-1)) := by
  rw [oneHole,ite_eq_left (show 0 < rootDisplay U l false by exact hl0),
    rootDisplay_remove_false U l hl0 hlU]

lemma rootDisplay_oneHole_true (F : (Bool → ℕ) → ℝ) (U l : ℕ) :
    oneHole F (rootDisplay U l) true=F (childProfile U l) := by
  rw [oneHole,ite_eq_left (show 0 < rootDisplay U l true by change 0 < U-l+1; omega),
    rootDisplay_remove_true]

lemma rootDisplay_removal (F : (Bool → ℕ) → ℝ) (U l : ℕ) (hl0 : 1 ≤ l) :
    integerRemovalMatrix F (rootDisplay U l) false true=F (auxRoot U l) := by
  have hv : ValidPair (rootDisplay U l) false true := by
    simp only [ValidPair,rootDisplay,Bool.false_eq_true,Bool.true_eq_false,↓reduceIte]
    omega
  rw [integerRemovalMatrix,ite_eq_left hv,rootDisplay_remove_two]

lemma widths_constant_mem (U : ℕ) {n : ℕ} (w : ℕ)
    (hw : w ∈ widths (fun _ : Fin n => U)) : w=U := by
  induction n with
  | zero => exact False.elim (List.not_mem_nil hw)
  | succ n ih =>
    simp only [widths,List.mem_cons] at hw
    exact hw.elim id ih

lemma prefixRaw_inBox (small : I → J → Bool) (s : I×J) (σ : I×J → ℕ) (U : ℕ)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) :
    InBox (fun _ : Earlier small s×Bool => U) (prefixRaw small s σ U) := by
  rintro ⟨a,b⟩
  cases b
  · exact hσ a
  · exact Nat.sub_le _ _

lemma graphEnergy_nonnegative {C : Type*} [DecidableEq C]
    (V : Finset (C → ℕ)) (f H : (C → ℕ) → ℝ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ integerGraphEnergy V f H := by
  unfold integerGraphEnergy
  apply div_nonneg _ (by norm_num)
  apply Finset.sum_nonneg
  intro e _
  exact mul_nonneg (le_min (hf _) (hf _)) (sq_nonneg _)

variable [Fintype I] [Fintype J]

/-- The actual adjacent conditional means satisfy the uniform repaired
transport estimate, with precisely the box-valid leaf exchange energy. -/
theorem adjacent_context_transport (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U l : ℕ) (hU : 2 ≤ U) (hl0 : 1 ≤ l) (hlU : l ≤ U)
    (hB : ∀ i j, small i j=true → B i j=U)
    (hlarge : ∀ i j, small i j=false → 2 ≤ B i j)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (hcap : ∀ T : ResidualTables small r c
      (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L),
      ∀ i j, T.val.val i j ≤ B i j)
    (H : (Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ) → ℝ)
    (hleft : 0 < eliminate (widths (fun _ : Fin n => U))
      (contextHard small B r c L _ (contextEquiv small s hs e U) (prefixRaw small s σ U))
      (childProfile U (l-1)))
    (hright : 0 < eliminate (widths (fun _ : Fin n => U))
      (contextHard small B r c L _ (contextEquiv small s hs e U) (prefixRaw small s σ U))
      (childProfile U l)) :
    let Ms := widths (fun _ : Fin n => U)
    let f := contextHard small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
    let a := eliminate Ms f (childProfile U (l-1))
    let b := eliminate Ms f (childProfile U l)
    let E := integerGraphEnergy
      ((leafVertices Ms (rootDisplay U l)).filter
        (fun x => InBox (bounds (fun _ : Bool => U) Ms) x ∧ (∑ i, x i)=U+Ms.sum)) f H
    min a b*(eliminate Ms (fun p => f p*H p) (childProfile U (l-1))/a-
      eliminate Ms (fun p => f p*H p) (childProfile U l)/b)^2 ≤
      (2+2*n*((U:ℝ)+1)^2)*E := by
  dsimp only
  have htransport := context_box_transport small B r c L (widths (fun _ : Fin n => U))
    (contextEquiv small s hs e U) (prefixRaw small s σ U) (fun _ => U)
    (fun _ => U) (rootDisplay U l) U U (prefixRaw_inBox small s σ U hσ) hlarge
    (fun w hw => by rw [widths_constant_mem U w hw]; exact hU)
    (fun w hw => le_of_eq (widths_constant_mem U w hw))
    (rootDisplay_inBox U l hl0 hlU) (rootDisplay_total U l hlU) H
    (leafVertices _ (rootDisplay U l)) (Finset.Subset.refl _)
    (by rw [rootDisplay_oneHole_false _ U l hl0 hlU]; exact hleft)
    (by rw [rootDisplay_oneHole_true]; exact hright)
  dsimp only at htransport
  simp only [rootDisplay_oneHole_false _ U l hl0 hlU,rootDisplay_oneHole_true,
    rootDisplay_removal _ U l hl0] at htransport
  have haux := auxiliary_mass_le_adjacent small B r c L s hs σ U l hl0 hlU hB hσ e hcap
  dsimp only at haux
  exact repaired_root_transport _ _ _ n U _ _ hleft hright
    (graphEnergy_nonnegative _ _ _ (contextHard_nonnegative small B r c L _ _ _)) haux htransport

end ContingencyTables.ExcessContextProfiles

end OAI
