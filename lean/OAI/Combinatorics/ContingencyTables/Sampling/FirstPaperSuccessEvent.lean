import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperJointLaw
import OAI.Combinatorics.ContingencyTables.Transport.CompletionFibreTransport
import OAI.Combinatorics.ContingencyTables.Transport.SuccessfulJointBijection

namespace OAI

/-! # The actual joint-law success event counts every original table once -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal FirstPaperProfiles
open SmallContextFibres SmallContextCoordinates SmallContextEnumeration RowMajorEnumeration
open PaddedCompletions CompletionCounts

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)

local notation "d" => dimensionAllowance (I := I) (J := J)
local notation "small" => paperSmall r c
local notation "B" => stateCapacity r c

/-- Forget the redundant small-profile coordinate while retaining both
full margin views. This projection is injective on all actual joint pairs. -/
def stateJointProjection (a : PaperStateJoint r c) := a.2.val

lemma stateJointProjection_injective : Function.Injective (stateJointProjection r c) :=
  fibre_projection_injective small B r _ c _ (physicalProfile small B r c (d^12))
    (physicalProfile_injective small B r c (d^12))
    (fun z => naturalProfile_bounded z.val.val)

def paperJointState (a : PaperJoint r c) : PaperStates r c := by
  have hp : 0 < hardMarginal small B r c (d^12)
      (rawChoice small (d^20) (wordChoices small (d^20) a.1)) := by
    rw [hardMarginal_eq_fibre_card small B r c (d^12) _
      (rawChoice_bounded small B (d^20) (stateCapacity_small r c) _)]
    exact_mod_cast Fintype.card_pos_iff.mpr (⟨a.2⟩ : Nonempty _)
  exact ⟨encodeProfile small B r c (d^12) (d^20) (stateCapacity_small r c) (.inl a.1),hp⟩

def paperJointEmbedding (a : PaperJoint r c) : PaperStateJoint r c :=
  ⟨paperJointState r c a,a.2⟩

lemma paperJointEmbedding_injective : Function.Injective (paperJointEmbedding r c) := by
  intro a b hab
  apply balancedJointTable_injective small B r c (d^12) (d^20) (stateCapacity_small r c)
  apply Subtype.ext
  exact congrArg (fun z : PaperStateJoint r c => z.2.val.val.1) hab

lemma paperJointEmbedding_balanced (a : PaperJoint r c) :
    Balanced small B (physicalProfile small B r c (d^12) (paperJointEmbedding r c a).1) :=
  rawChoice_balanced small B (d^20) (stateCapacity_small r c) _

def balancedJointFromState (a : PaperStateJoint r c)
    (hb : Balanced small B (physicalProfile small B r c (d^12) a.1)) : PaperJoint r c :=
  ⟨balancedWord small B (d^20) (stateCapacity_small r c) a.1.val.val,
    withProfile (balancedWord_profile small B (d^20) (stateCapacity_small r c) a.1.val.val hb).symm a.2⟩

lemma balancedJointFromState_projection (a : PaperStateJoint r c)
    (hb : Balanced small B (physicalProfile small B r c (d^12) a.1)) :
    (balancedJointFromState r c a hb).2.val=a.2.val := by
  exact withProfile_val
    (balancedWord_profile small B (d^20) (stateCapacity_small r c) a.1.val.val hb).symm a.2

lemma embedding_fromState (a : PaperStateJoint r c)
    (hb : Balanced small B (physicalProfile small B r c (d^12) a.1)) :
    paperJointEmbedding r c (balancedJointFromState r c a hb)=a := by
  apply stateJointProjection_injective r c
  exact balancedJointFromState_projection r c a hb

lemma fromState_embedding (a : PaperJoint r c) :
    balancedJointFromState r c (paperJointEmbedding r c a) (paperJointEmbedding_balanced r c a)=a := by
  apply paperJointEmbedding_injective r c
  exact embedding_fromState r c _ _

/-- The success test reads precisely balance and the lower padding bound. -/
def StateJointSuccess (a : PaperStateJoint r c) : Prop :=
  Balanced small B (physicalProfile small B r c (d^12) a.1) ∧
    ∀ i j,small i j=false → d^12 ≤ a.2.val.val.1 i j

abbrev SuccessfulStateJoint := {a : PaperStateJoint r c // StateJointSuccess r c a}

def successStateEquiv : SuccessfulJoint r c ≃ SuccessfulStateJoint r c where
  toFun a := ⟨paperJointEmbedding r c a.val,paperJointEmbedding_balanced r c a.val,a.property⟩
  invFun a := ⟨balancedJointFromState r c a.val a.property.1,a.property.2⟩
  left_inv a := by
    apply Subtype.ext
    exact fromState_embedding r c a.val
  right_inv a := by
    apply Subtype.ext
    exact embedding_fromState r c a.val a.property.1

/-- Every accepted actual state/completion pair unpads to one original
table, and every original table has one such pair. -/
def originalStateSuccessEquiv : Table r c ≃ SuccessfulStateJoint r c :=
  (successfulJointEquiv r c).trans (successStateEquiv r c)

end
end ContingencyTables.SmallGraphProfiles

end OAI
