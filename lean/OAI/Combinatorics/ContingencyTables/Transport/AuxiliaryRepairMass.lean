import OAI.Combinatorics.ContingencyTables.Transport.ExcessContextDefects
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperChildMass

namespace OAI

/-! # Conditional repair bounds the literal auxiliary kernel mass -/

namespace ContingencyTables.ExcessContextProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open BalancedEnumeration IntegerWeightedTransport FirstPaperProfiles
open FirstPaperContextTransport FirstPaperPhysicalMarginal IntegerBoxTruncation
open PaddedCompletions CompletionCounts

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

lemma rawExcess_injective (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U l : ℕ) {n : ℕ} (e : Fin n ≃ Later small s) :
    Function.Injective (rawExcess small s hs σ U l e) := by
  intro q q' he
  apply excessEmbedding_injective _ (auxRoot U l)
  funext a
  have hh := congrFun he (contextEquiv small s hs e U (.inr a))
  simpa only [rawExcess,assemble,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inr] using hh

abbrev ValidAssignments (U n : ℕ) :=
  {q : ExcessAssignments (widths (fun _ : Fin n => U)) // ValidExcess _ q}

noncomputable instance validAssignmentsFintype (U n : ℕ) : Fintype (ValidAssignments U n) :=
  inferInstanceAs (Fintype {q : ExcessAssignments (widths (fun _ : Fin n => U)) // ValidExcess _ q})

lemma finite_injective_sum_le {X Y : Type*} [Fintype X] [Fintype Y]
    (j : X → Y) (hj : Function.Injective j) (g : Y → ℝ) (hg : ∀ y, 0 ≤ g y) :
    (∑ x, g (j x)) ≤ ∑ y, g y := by
  calc
    _ = ∑ y ∈ Finset.univ.image j, g y :=
      (Finset.sum_image (fun x _ y _ he => hj he)).symm
    _ ≤ ∑ y, g y := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun y _ _ => hg y)

variable [Fintype I] [Fintype J]

/-- Every truncated auxiliary assignment maps injectively into one
actual conditional defect profile. The hard weights retain all completions. -/
theorem auxiliary_mass_le_defect_sum (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U l : ℕ) (hl0 : 1 ≤ l) (hlU : l ≤ U)
    (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s) :
    let Ms := widths (fun _ : Fin n => U)
    let f := contextHard small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
    auxiliaryKernel Ms (truncate f (bounds (fun _ : Bool => U) Ms) (U+Ms.sum)) (auxRoot U l) ≤
      ∑ t : Later small s, ∑ z : DefectProfiles small B s t.val.val σ l,
        hardMarginal small B r c L (naturalProfile z.val) := by
  dsimp only
  rw [auxiliaryKernel_truncate_eq_valid_sum _ _ _ _ _ (auxRoot_inBox U l hlU) (by
    simp only [auxRoot,Fintype.sum_bool,Bool.false_eq_true,↓reduceIte]
    omega)]
  rw [Finset.sum_subtype (p := ValidExcess (widths (fun _ : Fin n => U))) _ (by simp)]
  let j : ValidAssignments U n → (t : Later small s) × DefectProfiles small B s t.val.val σ l :=
    fun q => ⟨e (excessIndex (fun _ : Fin n => U) q.val),
      excessDefectProfile small B s hs σ U l hl0 hlU hB hσ e q.val q.property⟩
  have hj : Function.Injective j := by
    intro q q' he
    apply Subtype.ext
    apply rawExcess_injective small s hs σ U l e
    exact congrArg (fun a : (t : Later small s) × DefectProfiles small B s t.val.val σ l =>
      naturalProfile a.2.val) he
  have hg (a : (t : Later small s) × DefectProfiles small B s t.val.val σ l) :
      0 ≤ hardMarginal small B r c L (naturalProfile a.2.val) := by
    rw [hardMarginal_eq_fibre_card small B r c L _ (naturalProfile_bounded a.2.val)]
    positivity
  have hh := finite_injective_sum_le j hj
    (fun a => hardMarginal small B r c L (naturalProfile a.2.val)) hg
  rw [Fintype.sum_sigma] at hh
  exact hh

/-- Apply the completion-retaining repair injection and sum over actual
later cells. Each repair enters one of the two adjacent children. -/
theorem auxiliary_mass_le_adjacent (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U l : ℕ) (hl0 : 1 ≤ l) (hlU : l ≤ U)
    (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (hcap : ∀ T : ResidualTables small r c
      (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L),
      ∀ i j, T.val.val i j ≤ B i j) :
    let Ms := widths (fun _ : Fin n => U)
    let f := contextHard small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
    auxiliaryKernel Ms (truncate f (bounds (fun _ : Bool => U) Ms) (U+Ms.sum)) (auxRoot U l) ≤
      n*max (eliminate Ms f (childProfile U (l-1))) (eliminate Ms f (childProfile U l)) := by
  dsimp only
  let f := contextHard small B r c L (widths (fun _ : Fin n => U))
    (contextEquiv small s hs e U) (prefixRaw small s σ U)
  have hfirst := auxiliary_mass_le_defect_sum small B r c L s hs σ U l hl0 hlU hB hσ e
  dsimp only at hfirst
  refine hfirst.trans ?_
  have htbound (t : Later small s) :
      (∑ z : DefectProfiles small B s t.val.val σ l, hardMarginal small B r c L (naturalProfile z.val)) ≤
      max (eliminate _ f (childProfile U (l-1))) (eliminate _ f (childProfile U l)) := by
    have hrepair := conditional_defect_mass_le small B r c L s t.val.val σ l hs
      t.val.property t.property hcap
    have hk : l-1+(if t.val.val.1=s.1 then 1 else 0) ≤ U := by
      split_ifs <;> omega
    have he := eliminate_context_eq_balanced_mass small B r c L s hs σ U hB hσ
      ⟨l-1+(if t.val.val.1=s.1 then 1 else 0),Nat.lt_succ_of_le hk⟩ e
    have hb := hrepair.trans_eq he.symm
    by_cases hrow : t.val.val.1=s.1
    · simp only [hrow,↓reduceIte] at hb
      have hl : l-1+1=l := by omega
      rw [hl] at hb
      exact hb.trans (le_max_right _ _)
    · simp only [hrow,↓reduceIte,add_zero] at hb
      exact hb.trans (le_max_left _ _)
  calc
    _ ≤ ∑ _t : Later small s,
      max (eliminate _ f (childProfile U (l-1))) (eliminate _ f (childProfile U l)) :=
      Finset.sum_le_sum (fun t _ => htbound t)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rw [←Fintype.card_congr e,Fintype.card_fin]

end ContingencyTables.ExcessContextProfiles

end OAI
