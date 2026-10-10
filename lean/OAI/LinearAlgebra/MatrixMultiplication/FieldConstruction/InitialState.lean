import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.InitialHistories
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Tensors
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.CanonicalInitial

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldInitialState

open MatrixMultiplication.Foundation AllFieldHistory AllFieldParameters AllFieldFiniteFamily
open scoped BigOperators Classical

variable {K : ℕ} (allocation : Allocation) (dilation : ℕ)

abbrev CanonicalKey := JointCanonicalization.ClassKey (H := Fin K)

abbrev PlacementPositions (p : InitialPlacement K) :=
  Fin (population allocation dilation (.initial p.1, p.2))

def classPosition (c : CanonicalKey (K := K))
    (i : Fin (initialJointCounts allocation dilation c.1 c.2)) :
    Σ p : InitialPlacement K, PlacementPositions allocation dilation p :=
  let q := initialClassPositionEquiv allocation dilation c.1 c.2 i
  ⟨((c.1, q.1.val.1), q.1.val.2), q.2⟩

theorem classPosition_shape (c : CanonicalKey (K := K))
    (i : Fin (initialJointCounts allocation dilation c.1 c.2)) :
    JointCanonicalCW.shapeNat c.2 =
      physicalShape (classPosition allocation dilation c i).1.2
        (initialShape (classPosition allocation dilation c i).1.1) := by
  have h := congrArg decodeShape (initialClassPosition_shape allocation dilation c.1 c.2 i)
  simp only [rootShape, decode_encodePhysicalShape] at h
  exact h.symm

theorem prod_classPosition {F : Type*} [CommMonoid F]
    (f : ∀ p : InitialPlacement K, PlacementPositions allocation dilation p → F) :
    (∏ c : CanonicalKey (K := K),
      ∏ i : Fin (initialJointCounts allocation dilation c.1 c.2),
        f (classPosition allocation dilation c i).1
          (classPosition allocation dilation c i).2) =
      ∏ p : InitialPlacement K, ∏ i : PlacementPositions allocation dilation p, f p i := by
  conv_lhs => rw [Fintype.prod_prod_type]
  conv_rhs =>
    rw [Fintype.prod_prod_type]
    rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro j _
  calc
    (∏ u : JointPopulation.Shape, ∏ i : Fin (initialJointCounts allocation dilation j u),
        f (classPosition allocation dilation (j, u) i).1
          (classPosition allocation dilation (j, u) i).2) =
        ∏ u : JointPopulation.Shape, ∏ p : InitialShapeFiber j u,
          ∏ i : Fin (population allocation dilation (.initial (j, p.val.1), p.val.2)),
            f ((j, p.val.1), p.val.2) i := by
      apply Finset.prod_congr rfl
      intro u _
      rw [← Fintype.prod_sigma']
      apply Fintype.prod_equiv (initialClassPositionEquiv allocation dilation j u)
      intro i
      rfl
    _ = ∏ p : Fin sortedInitial.length × Placement,
          ∏ i : Fin (population allocation dilation (.initial (j, p.1), p.2)),
            f ((j, p.1), p.2) i :=
      Fintype.prod_fiberwise (fun p : Fin sortedInitial.length × Placement =>
        rootShape (j, p.1) p.2)
        (fun p => ∏ i : Fin (population allocation dilation (.initial (j, p.1), p.2)),
          f ((j, p.1), p.2) i)
    _ = _ := by rw [Fintype.prod_prod_type]

abbrev StateWords := ∀ h : State K 0, HistoryWord allocation dilation h.val

def toCanonical (w : StateWords (K := K) allocation dilation) :
    JointCanonicalInitial.CanonicalWords (initialJointCounts (K := K) allocation dilation) :=
  fun c i =>
    let q := classPosition allocation dilation c i
    w ((initialStateEquiv K).symm q.1) q.2

theorem coefficient (F : Type*) [Field F] (ε : ℝ)
    (x y z : StateWords (K := K) allocation dilation) :
    JointCanonicalInitial.canonical (F := F) (initialJointCounts allocation dilation)
      (toCanonical allocation dilation x) (toCanonical allocation dilation y)
      (toCanonical allocation dilation z) =
      stateTensor F allocation dilation ε 0 x y z := by
  let f : ∀ p : InitialPlacement K, PlacementPositions allocation dilation p → F :=
    fun p i => CWStrands.shapeTensor (Fin 8) (physicalShape p.2 (initialShape p.1))
      (x ((initialStateEquiv K).symm p) i)
      (y ((initialStateEquiv K).symm p) i)
      (z ((initialStateEquiv K).symm p) i)
  have hcanonical :
      JointCanonicalInitial.canonical (F := F) (initialJointCounts allocation dilation)
        (toCanonical allocation dilation x) (toCanonical allocation dilation y)
        (toCanonical allocation dilation z) =
      ∏ p : InitialPlacement K, ∏ i : PlacementPositions allocation dilation p, f p i := by
    rw [← prod_classPosition allocation dilation f]
    unfold JointCanonicalInitial.canonical InheritedMasks.classProduct
    apply Finset.prod_congr rfl
    intro c _
    apply Finset.prod_congr rfl
    intro i _
    dsimp only [toCanonical, f]
    rw [classPosition_shape allocation dilation c i]
  have hstate : stateTensor F allocation dilation ε 0 x y z =
      ∏ p : InitialPlacement K, ∏ i : PlacementPositions allocation dilation p, f p i := by
    change (∏ h : State K 0, historyTensor F allocation dilation ε h.val (x h) (y h) (z h)) = _
    rw [← (initialStateEquiv K).symm.prod_comp
      (fun h : State K 0 => historyTensor F allocation dilation ε h.val (x h) (y h) (z h))]
    apply Finset.prod_congr rfl
    intro p _
    change historyTensor F allocation dilation ε (.initial p.1, p.2)
      (x ((initialStateEquiv K).symm p)) (y ((initialStateEquiv K).symm p))
      (z ((initialStateEquiv K).symm p)) = _
    rw [historyTensor_initial]
    rfl
  exact hcanonical.trans hstate.symm

def map (F : Type*) [Field F] (ε : ℝ) :
    LocalMap
      (JointCanonicalInitial.canonical (F := F) (initialJointCounts (K := K) allocation dilation))
      (stateTensor F (K := K) allocation dilation ε 0) where
  x := fun x s => if s = toCanonical allocation dilation x then 1 else 0
  y := fun y s => if s = toCanonical allocation dilation y then 1 else 0
  z := fun z s => if s = toCanonical allocation dilation z then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    exact coefficient allocation dilation F ε x y z

def execution (F : Type*) [Field F] (ε : ℝ) {I : Type} [Fintype I] {N : ℕ}
    (E : Execution (cwSource F K N)
      (Tensor.directSum (fun _ : I => JointCanonicalInitial.canonical
        (initialJointCounts (K := K) allocation dilation)))) :
    Execution (cwSource F K N)
      (Tensor.directSum (fun _ : I => stateTensor F (K := K) allocation dilation ε 0)) :=
  E.restrict _ ((map (K := K) allocation dilation F ε).parallelCopies I)

@[simp] theorem execution_copies (F : Type*) [Field F] (ε : ℝ)
    {I : Type} [Fintype I] {N : ℕ}
    (E : Execution (cwSource F K N)
      (Tensor.directSum (fun _ : I => JointCanonicalInitial.canonical
        (initialJointCounts (K := K) allocation dilation)))) :
    Fintype.card (execution allocation dilation F ε E).Copies = Fintype.card E.Copies := rfl

end MatrixMultiplication.AllFieldInitialState

end

end OAI
