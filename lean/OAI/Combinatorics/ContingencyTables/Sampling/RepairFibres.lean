import OAI.Combinatorics.ContingencyTables.Sampling.RepairResiduals

namespace OAI

/-! # Joint state-completion repair injections, including fixed contexts

Full row and column views retain the large completion explicitly. Their
finite fibre cardinalities therefore count states with the correct
completion multiplicity. The target repair is a balanced full table.
-/

namespace ContingencyTables

open scoped BigOperators Classical
open PaddedCompletions

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def RowColumnPair (r : I → ℕ) (c : J → ℕ) :=
  {Z : (I → J → ℕ) × (I → J → ℕ) //
    (∀ i, ∑ j, Z.1 i j=r i) ∧ (∀ j, ∑ i, Z.2 i j=c j)}

instance rowColumnPairFinite (r : I → ℕ) (c : J → ℕ) : Finite (RowColumnPair r c) := by
  let encode : RowColumnPair r c → ((i : I) → J → Fin (r i+1)) × ((j : J) → I → Fin (c j+1)) :=
    fun Z => (fun i j => ⟨Z.val.1 i j,Nat.lt_succ_of_le (by
      rw [←Z.property.1 i]
      exact Finset.single_le_sum (f := fun k => Z.val.1 i k)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))⟩,
      fun j i => ⟨Z.val.2 i j,Nat.lt_succ_of_le (by
        rw [←Z.property.2 j]
        exact Finset.single_le_sum (f := fun k => Z.val.2 k j)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))⟩)
  apply Finite.of_injective encode
  intro X Y he
  apply Subtype.ext
  apply Prod.ext
  · funext i j
    exact congrArg Fin.val (congrFun (congrFun (congrArg Prod.fst he) i) j)
  · funext i j
    exact congrArg Fin.val (congrFun (congrFun (congrArg Prod.snd he) j) i)

noncomputable instance rowColumnPairFintype (r : I → ℕ) (c : J → ℕ) : Fintype (RowColumnPair r c) :=
  Fintype.ofFinite _

def JointDefect (small : I → J → Bool) (r : I → ℕ) (c : J → ℕ)
    (rbar : I → ℕ) (cbar : J → ℕ) (s t : I×J) :=
  {Z : RowColumnPair rbar cbar // IsDefect Z.val.1 Z.val.2 s t ∧
    (∀ i, smallRow small Z.val.1 i ≤ r i) ∧
    (∀ j, smallColumnView small Z.val.2 j ≤ c j)}

def ResidualTables (small : I → J → Bool) (r : I → ℕ) (c : J → ℕ)
    (rbar : I → ℕ) (cbar : J → ℕ) :=
  {T : Table rbar cbar // (∀ i, smallRow small T.val i ≤ r i) ∧
    (∀ j, smallColumnView small T.val j ≤ c j)}

noncomputable instance jointDefectFintype (small : I → J → Bool) (r : I → ℕ) (c : J → ℕ)
    (rbar : I → ℕ) (cbar : J → ℕ) (s t : I×J) :
    Fintype (JointDefect small r c rbar cbar s t) := by unfold JointDefect; infer_instance

noncomputable instance residualTablesFintype (small : I → J → Bool) (r : I → ℕ) (c : J → ℕ)
    (rbar : I → ℕ) (cbar : J → ℕ) :
    Fintype (ResidualTables small r c rbar cbar) := by unfold ResidualTables; infer_instance

def jointRepair {small : I → J → Bool} {r : I → ℕ} {c : J → ℕ}
    {rbar : I → ℕ} {cbar : J → ℕ} {s t : I×J}
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true)
    (Z : JointDefect small r c rbar cbar s t) : ResidualTables small r c rbar cbar := by
  have hd := Z.property.1
  have hm := repairMatrix_margins hd rbar cbar Z.val.property.1 Z.val.property.2
  have hsmall := repairMatrix_small_sums hd hs ht
  exact ⟨⟨repairMatrix Z.val.val.1 s t,hm⟩,
    fun i => (hsmall.1 i).trans (Z.property.2.1 i),
    fun j => (hsmall.2 j).trans (Z.property.2.2 j)⟩

theorem jointRepair_injective {small : I → J → Bool} {r : I → ℕ} {c : J → ℕ}
    {rbar : I → ℕ} {cbar : J → ℕ} {s t : I×J}
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true) :
    Function.Injective (jointRepair (r := r) (c := c) (rbar := rbar) (cbar := cbar) hs ht) := by
  intro X Y he
  have hmatrix := congrArg (fun T => T.val.val) he
  have hviews := repairMatrix_injective X.property.1 Y.property.1 hmatrix
  exact Subtype.ext (Subtype.ext (Prod.ext hviews.1 hviews.2))

/-- Global typewise repair domination, retaining the large completion. -/
theorem jointDefect_card_le (small : I → J → Bool) (r : I → ℕ) (c : J → ℕ)
    (rbar : I → ℕ) (cbar : J → ℕ) (s t : I×J)
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true) :
    Fintype.card (JointDefect small r c rbar cbar s t) ≤
      Fintype.card (ResidualTables small r c rbar cbar) :=
  Fintype.card_le_of_injective (jointRepair hs ht) (jointRepair_injective hs ht)

def JointDefectContext [LT I] [LT J]
    (small : I → J → Bool) (r : I → ℕ) (c : J → ℕ)
    (rbar : I → ℕ) (cbar : J → ℕ) (s t : I×J) (σ : I×J → ℕ) (l : ℕ) :=
  {Z : JointDefect small r c rbar cbar s t //
    (∀ w, RowMajorBefore w s → Z.val.val.1 w.1 w.2=σ w) ∧ Z.val.val.1 s.1 s.2=l-1}

def ResidualChild [LT I] [LT J]
    (small : I → J → Bool) (r : I → ℕ) (c : J → ℕ)
    (rbar : I → ℕ) (cbar : J → ℕ) (s : I×J) (σ : I×J → ℕ) (l : ℕ) :=
  {T : ResidualTables small r c rbar cbar //
    (∀ w, RowMajorBefore w s → T.val.val w.1 w.2=σ w) ∧ T.val.val s.1 s.2=l}

noncomputable instance jointDefectContextFintype [LT I] [LT J]
    (small : I → J → Bool) (r : I → ℕ) (c : J → ℕ)
    (rbar : I → ℕ) (cbar : J → ℕ) (s t : I×J) (σ : I×J → ℕ) (l : ℕ) :
    Fintype (JointDefectContext small r c rbar cbar s t σ l) := by
  unfold JointDefectContext; infer_instance

noncomputable instance residualChildFintype [LT I] [LT J]
    (small : I → J → Bool) (r : I → ℕ) (c : J → ℕ)
    (rbar : I → ℕ) (cbar : J → ℕ) (s : I×J) (σ : I×J → ℕ) (l : ℕ) :
    Fintype (ResidualChild small r c rbar cbar s σ l) := by
  unfold ResidualChild; infer_instance

/-- The entire fixed-prefix defect fibre maps into one fixed child.
The child choice depends only on the ordered defect type. -/
theorem conditional_jointDefect_card_le [LinearOrder I] [LinearOrder J]
    (small : I → J → Bool) (r : I → ℕ) (c : J → ℕ)
    (rbar : I → ℕ) (cbar : J → ℕ) (s t : I×J) (σ : I×J → ℕ) (l : ℕ)
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true) (hst : RowMajorBefore s t) :
    Fintype.card (JointDefectContext small r c rbar cbar s t σ l) ≤
      Fintype.card (ResidualChild small r c rbar cbar s σ (l-1+if t.1=s.1 then 1 else 0)) := by
  let f : JointDefectContext small r c rbar cbar s t σ l →
      ResidualChild small r c rbar cbar s σ (l-1+if t.1=s.1 then 1 else 0) := fun Z =>
    ⟨jointRepair hs ht Z.val, (fun w hw => by
      rw [show (jointRepair hs ht Z.val).val.val w.1 w.2=
        repairMatrix Z.val.val.val.1 s t w.1 w.2 from rfl]
      rw [repairMatrix_prefix Z.val.property.1 hst hw]
      exact Z.property.1 w hw), by
      change repairMatrix Z.val.val.val.1 s t s.1 s.2=_
      rw [repairMatrix_special Z.val.property.1,Z.property.2]⟩
  apply Fintype.card_le_of_injective f
  intro X Y he
  apply Subtype.ext
  apply jointRepair_injective hs ht
  exact congrArg Subtype.val he

end ContingencyTables

end OAI
