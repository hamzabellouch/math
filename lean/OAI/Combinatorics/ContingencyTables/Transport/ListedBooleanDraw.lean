import OAI.Combinatorics.ContingencyTables.Transport.ListedBooleanStep

namespace OAI

/-! # Literal finite-word outer sampling with the computed dense draw -/

namespace ContingencyTables.SmallGraphProfiles
open ResidualMixture FirstSuccess CompletionTranslation CompletionCounts FairBits
open ProfilePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "f" => 25*(d+b+h+1)^62

def listedFlatWalk (x : PaperStates r c) (n : ℕ)
    (bits : Fin (n*(s+f)) → Bool) : PaperStates r c :=
  wordWalk (listedBitStep r c e hr hc b h hb) x n
    (GridBoundary.gridWordEquiv n (s+f) bits)

theorem listedFlatWalk_law (htotal : (∑ i,r i)=∑ j,c j) (x : PaperStates r c) (n : ℕ) :
    mapLaw (uniformLaw (α := Fin (n*(s+f)) → Bool))
      (listedFlatWalk r c e hr hc b h hb x n)=
      walkLaw (listedSmallKernel r c hr hc b h hb) x n := by
  unfold listedFlatWalk
  rw [←map_equiv (GridBoundary.gridWordEquiv n (s+f)),uniform_equiv]
  change wordWalkLaw _ _ _=_
  rw [wordWalkLaw_eq]
  exact congrArg (fun K => walkLaw K x n)
    (funext (listedBitStep_law r c e hr hc b h hb htotal))

def listedJointDraw (x : PaperStates r c) (n : ℕ)
    (bits : Fin (n*(s+f)+f) → Bool) : PaperStateJoint r c :=
  let draws := splitWordEquiv (n*(s+f)) f bits
  let z := listedFlatWalk r c e hr hc b h hb x n draws.1
  ⟨z,listedPaddedDraw r c hr hc b h hb z draws.2⟩

/-- The terminal completion uses fresh bits at the adaptively obtained
state, with exactly the joint law used in the error proof. -/
theorem listedJointDraw_law (htotal : (∑ i,r i)=∑ j,c j) (x : PaperStates r c) (n : ℕ) :
    mapLaw (uniformLaw (α := Fin (n*(s+f)+f) → Bool))
      (listedJointDraw r c e hr hc b h hb x n)=
      listedJointLaw r c hr hc b h hb x n := by
  let E := splitWordEquiv (n*(s+f)) f
  let F := fun ab : (Fin (n*(s+f)) → Bool) × (Fin f → Bool) =>
    let z := listedFlatWalk r c e hr hc b h hb x n ab.1
    (⟨z,listedPaddedDraw r c hr hc b h hb z ab.2⟩ : PaperStateJoint r c)
  have he := map_equiv E (uniformLaw (α := Fin (n*(s+f)+f) → Bool)) F
  rw [uniform_equiv,←uniform_product] at he
  calc
    _ = mapLaw (productLaw (uniformLaw (α := Fin (n*(s+f)) → Bool))
        (uniformLaw (α := Fin f → Bool))) F := he.symm
    _ = dependentJointLaw
        (mapLaw (uniformLaw (α := Fin (n*(s+f)) → Bool))
          (listedFlatWalk r c e hr hc b h hb x n))
        (fun z => mapLaw (uniformLaw (α := Fin f → Bool))
          (listedPaddedDraw r c hr hc b h hb z)) :=
      mapLaw_dependent_product (A := Fin (n*(s+f)) → Bool) (B := Fin f → Bool)
        (X := PaperStates r c) (Y := PaperFibre r c)
        (uniformLaw (α := Fin (n*(s+f)) → Bool)) (uniformLaw (α := Fin f → Bool))
        (listedFlatWalk r c e hr hc b h hb x n)
        (fun z => listedPaddedDraw r c hr hc b h hb z)
    _ = _ := by rw [listedFlatWalk_law r c e hr hc b h hb htotal]; rfl

def listedOuterDraw (x : PaperStates r c) (n J₀ : ℕ) (z₀ : Table r c)
    (bits : Fin (J₀*(n*(s+f)+f)) → Bool) : Table r c :=
  wordRetry (fun bitword => stateTrial r c
    (listedJointDraw r c e hr hc b h hb x n bitword)) z₀ J₀
    (GridBoundary.gridWordEquiv J₀ (n*(s+f)+f) bits)

/-- All trial words are independent and failed trials return the fixed
feasible fallback. In particular, every bit word returns a feasible table. -/
theorem listedOuterDraw_law (htotal : (∑ i,r i)=∑ j,c j) (x : PaperStates r c) (n J₀ : ℕ) (z₀ : Table r c) :
    mapLaw (uniformLaw (α := Fin (J₀*(n*(s+f)+f)) → Bool))
      (listedOuterDraw r c e hr hc b h hb x n J₀ z₀)=
      retryLaw (listedJointLaw r c hr hc b h hb x n)
        (stateTrial r c) z₀ J₀ := by
  unfold listedOuterDraw
  rw [←map_equiv (GridBoundary.gridWordEquiv J₀ (n*(s+f)+f)),uniform_equiv]
  change wordRetryLaw _ _ _=_
  rw [wordRetryLaw_eq,←retryLaw_map,listedJointDraw_law r c e hr hc b h hb htotal]


end
end ContingencyTables.SmallGraphProfiles

end OAI
