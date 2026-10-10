import OAI.Combinatorics.ContingencyTables.Sampling.AllSmallRational
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperBooleanProposal
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordWalk
import OAI.Combinatorics.ContingencyTables.Dense.DenseBooleanWalk
import OAI.Combinatorics.ContingencyTables.Transport.FiniteDeterministicJoint
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperIdealRejection

namespace OAI

/-! # Boolean implementation when all cells are retained -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open ResidualMixture FirstSuccess FairBits CompletionTranslation CompletionCounts

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)
local notation "s" => smallProposalBits (I := I) (J := J)
local instance : DecidableEq (PaperStates r c) := Classical.decEq _

def unitBitStep (x : PaperStates r c) (bits : Fin s → Bool) : PaperStates r c :=
  (smallBitProposal r c x bits).getD x

lemma unitBitStep_law (x : PaperStates r c) :
    mapLaw (uniformLaw (α := Fin s → Bool)) (unitBitStep r c x)=unitSmallStep r c x := by
  unfold unitBitStep
  calc
    _ = mapLaw (mapLaw (uniformLaw (α := Fin s → Bool)) (smallBitProposal r c x))
        (fun z : Option (PaperStates r c) => z.getD x) :=
      (mapLaw_comp _ (smallBitProposal r c x)
        (fun z : Option (PaperStates r c) => z.getD x)).symm
    _ = _ := by rw [smallBitProposal_law_decidableEq r c _ x]; rfl

def flatUnitWalk (x : PaperStates r c) (n : ℕ) (bits : Fin (n*s) → Bool) : PaperStates r c :=
  wordWalk (unitBitStep r c) x n (GridBoundary.gridWordEquiv n s bits)

lemma flatUnitWalk_law (x : PaperStates r c) (n : ℕ) :
    mapLaw (uniformLaw (α := Fin (n*s) → Bool)) (flatUnitWalk r c x n)=
      walkLaw (unitSmallStep r c) x n := by
  unfold flatUnitWalk
  rw [←map_equiv (GridBoundary.gridWordEquiv n s),uniform_equiv]
  change wordWalkLaw _ _ _=_
  rw [wordWalkLaw_eq]
  exact congrArg (fun K => walkLaw K x n) (funext (unitBitStep_law r c))

lemma uniform_singleton_joint [Nonempty (PaperStates r c)]
    (hsmall : ∀ i j,FirstPaperPhysicalMarginal.paperSmall r c i j=true)
    (fallback : (z : PaperStates r c) → PaperFibre r c z) :
    mapLaw (uniformLaw (α := PaperStates r c))
      (fun z => (⟨z,fallback z⟩ : PaperStateJoint r c))=
        uniformLaw (α := PaperStateJoint r c) := by
  rw [mapLaw_deterministicJoint]
  have he (z : PaperStates r c) : pointLaw (fallback z)=uniformLaw (α := PaperFibre r c z) := by
    let : Subsingleton (PaperFibre r c z) :=
      PhysicalCompletionFibres.completionFibre_subsingleton _ _ _ _ _ _ _ hsmall
    exact pointLaw_eq_uniform _
  simp_rw [he]
  apply dependentJointLaw_uniform
  intro z
  simp only [uniformLaw,uniformMass,paperFibre_card_allSmall r c hsmall,
    Nat.cast_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]


def unitJointDraw (fallback : (z : PaperStates r c) → PaperFibre r c z)
    (x : PaperStates r c) (n : ℕ) (bits : Fin (n*s) → Bool) : PaperStateJoint r c :=
  let z := flatUnitWalk r c x n bits
  ⟨z,fallback z⟩

lemma unitJointDraw_law (fallback : (z : PaperStates r c) → PaperFibre r c z)
    (x : PaperStates r c) (n : ℕ) :
    mapLaw (uniformLaw (α := Fin (n*s) → Bool)) (unitJointDraw r c fallback x n)=
      mapLaw (walkLaw (unitSmallStep r c) x n)
        (fun z => (⟨z,fallback z⟩ : PaperStateJoint r c)) := by
  unfold unitJointDraw
  calc
    _ = mapLaw (mapLaw (uniformLaw (α := Fin (n*s) → Bool)) (flatUnitWalk r c x n))
        (fun z => (⟨z,fallback z⟩ : PaperStateJoint r c)) :=
      (mapLaw_comp _ (flatUnitWalk r c x n)
        (fun z => (⟨z,fallback z⟩ : PaperStateJoint r c))).symm
    _ = _ := by rw [flatUnitWalk_law]

theorem unitJointDraw_variation [Nonempty I] [Nonempty J] [Nonempty (PaperStates r c)]
    (hsmall : ∀ i j,FirstPaperPhysicalMarginal.paperSmall r c i j=true)
    (fallback : (z : PaperStates r c) → PaperFibre r c z)
    (x : PaperStates r c) (n : ℕ) :
    (variation (mapLaw (uniformLaw (α := Fin (n*s) → Bool))
      (unitJointDraw r c fallback x n)) (uniformLaw (α := PaperStateJoint r c)):ℝ) ≤
      ((stateBound r c+1:ℕ):ℝ)^(2*dimensionAllowance (I := I) (J := J))*
        Real.exp (-(n:ℝ)/(dimensionAllowance (I := I) (J := J):ℝ)^160) := by
  rw [unitJointDraw_law]
  have hv := variation_map (walkLaw (unitSmallStep r c) x n)
    (uniformLaw (α := PaperStates r c)) (fun z => (⟨z,fallback z⟩ : PaperStateJoint r c))
  rw [uniform_singleton_joint r c hsmall fallback] at hv
  exact ((Rat.cast_le (K := ℝ)).mpr hv).trans (unitSmallWalk_variation r c hsmall x n)

end
end ContingencyTables.SmallGraphProfiles

end OAI
