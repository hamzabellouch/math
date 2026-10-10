import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperBooleanStep

namespace OAI

/-! # Fixed Boolean words for the entire small walk and outer sampler -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess CompletionTranslation CompletionCounts FairBits

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)
variable (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
variable (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
variable {q : ℕ}
variable (e : ({i : LargeRows r ((dimensionAllowance (I := I) (J := J))^20) // i≠i₀} ×
  {j : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20) // j≠j₀}) ≃ Fin q)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
variable (a : GridBoundary.Grid (I := Fin q) (4*(dimensionAllowance (I := I) (J := J))^8))
variable (fallback : (z : PaperStates r c) → PaperFibre r c z)

local notation "d" => dimensionAllowance (I := I) (J := J)
local notation "R" => referenceRows r c (d^20) (d^12) (stateCapacity r c) i₀
local notation "P" => referenceColumns r c (d^20) (d^12) (stateCapacity r c) j₀

local notation "s" => smallProposalBits (I := I) (J := J)
local notation "f" => 25*(d+b+h+1)^62

def flatSmallWalk (x : PaperStates r c) (n : ℕ)
    (bits : Fin (n*(s+f)) → Bool) : PaperStates r c :=
  wordWalk (smallBitStep r c i₀ j₀ e b h hb a fallback) x n
    (GridBoundary.gridWordEquiv n (s+f) bits)

theorem flatSmallWalk_law (x : PaperStates r c) (n : ℕ) :
    mapLaw (uniformLaw (α := Fin (n*(s+f)) → Bool))
      (flatSmallWalk r c i₀ j₀ e b h hb a fallback x n)=
      walkLaw (implementedSmallKernel r c i₀ j₀ e b h hb a fallback) x n := by
  unfold flatSmallWalk
  rw [←map_equiv (GridBoundary.gridWordEquiv n (s+f)),uniform_equiv]
  change wordWalkLaw _ _ _=_
  rw [wordWalkLaw_eq]
  exact congrArg (fun K => walkLaw K x n)
    (funext (smallBitStep_law r c i₀ j₀ e b h hb a fallback))

def smallJointDraw (x : PaperStates r c) (n : ℕ)
    (bits : Fin (n*(s+f)+f) → Bool) : PaperStateJoint r c :=
  let draws := splitWordEquiv (n*(s+f)) f bits
  let z := flatSmallWalk r c i₀ j₀ e b h hb a fallback x n draws.1
  ⟨z,completionPaddedDraw r c i₀ j₀ e b h hb a z (fallback z) draws.2⟩

/-- The terminal completion uses fresh bits at the adaptively obtained
state, with exactly the joint law used in the error proof. -/
theorem smallJointDraw_law (x : PaperStates r c) (n : ℕ) :
    mapLaw (uniformLaw (α := Fin (n*(s+f)+f) → Bool))
      (smallJointDraw r c i₀ j₀ e b h hb a fallback x n)=
      implementedJointLaw r c i₀ j₀ e b h hb a fallback x n := by
  let E := splitWordEquiv (n*(s+f)) f
  let F := fun ab : (Fin (n*(s+f)) → Bool) × (Fin f → Bool) =>
    let z := flatSmallWalk r c i₀ j₀ e b h hb a fallback x n ab.1
    (⟨z,completionPaddedDraw r c i₀ j₀ e b h hb a z (fallback z) ab.2⟩ : PaperStateJoint r c)
  have he := map_equiv E (uniformLaw (α := Fin (n*(s+f)+f) → Bool)) F
  rw [uniform_equiv,←uniform_product] at he
  calc
    _ = mapLaw (productLaw (uniformLaw (α := Fin (n*(s+f)) → Bool))
        (uniformLaw (α := Fin f → Bool))) F := he.symm
    _ = dependentJointLaw
        (mapLaw (uniformLaw (α := Fin (n*(s+f)) → Bool))
          (flatSmallWalk r c i₀ j₀ e b h hb a fallback x n))
        (fun z => mapLaw (uniformLaw (α := Fin f → Bool))
          (completionPaddedDraw r c i₀ j₀ e b h hb a z (fallback z))) :=
      mapLaw_dependent_product (A := Fin (n*(s+f)) → Bool) (B := Fin f → Bool)
        (X := PaperStates r c) (Y := PaperFibre r c)
        (uniformLaw (α := Fin (n*(s+f)) → Bool)) (uniformLaw (α := Fin f → Bool))
        (flatSmallWalk r c i₀ j₀ e b h hb a fallback x n)
        (fun z => completionPaddedDraw r c i₀ j₀ e b h hb a z (fallback z))
    _ = _ := by rw [flatSmallWalk_law]; rfl

def finiteOuterDraw (x : PaperStates r c) (n J₀ : ℕ) (z₀ : Table r c)
    (bits : Fin (J₀*(n*(s+f)+f)) → Bool) : Table r c :=
  wordRetry (fun bitword => stateTrial r c
    (smallJointDraw r c i₀ j₀ e b h hb a fallback x n bitword)) z₀ J₀
    (GridBoundary.gridWordEquiv J₀ (n*(s+f)+f) bits)

/-- All trial words are independent and failed trials return the fixed
feasible fallback. In particular, every bit word returns a feasible table. -/
theorem finiteOuterDraw_law (x : PaperStates r c) (n J₀ : ℕ) (z₀ : Table r c) :
    mapLaw (uniformLaw (α := Fin (J₀*(n*(s+f)+f)) → Bool))
      (finiteOuterDraw r c i₀ j₀ e b h hb a fallback x n J₀ z₀)=
      retryLaw (implementedJointLaw r c i₀ j₀ e b h hb a fallback x n)
        (stateTrial r c) z₀ J₀ := by
  unfold finiteOuterDraw
  rw [←map_equiv (GridBoundary.gridWordEquiv J₀ (n*(s+f)+f)),uniform_equiv]
  change wordRetryLaw _ _ _=_
  rw [wordRetryLaw_eq,←retryLaw_map,smallJointDraw_law]

end
end ContingencyTables.SmallGraphProfiles

end OAI
