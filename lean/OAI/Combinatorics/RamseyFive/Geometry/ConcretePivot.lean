import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.GuardedNodeEncoder
import OAI.Combinatorics.RamseyFive.Trees.PivotTree

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

abbrev PivotContext (K V : Type) [Field K] [AddCommGroup V] [Module K V] :=
  Finset (ℙ K V)×Finset (ℙ K (Dual K V))

abbrev PivotTape (pred : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (C : PivotContext K V) := FiniteNodeTape (pred C) (1000*(Nat.card K)^2) (Nat.card K)
abbrev PivotMessage (pred : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (C : PivotContext K V) (ω : PivotTape pred C) :=
  FiniteNodeMessage (pred C) C.2 (1000*(Nat.card K)^2) (Nat.card K) ω
noncomputable def pivotLeft (pred : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (C : PivotContext K V) (ω : PivotTape pred C) (m : PivotMessage pred C ω) : PivotContext K V :=
  (C.1∩(finiteNodeDecoded (pred C) C.2 (1000*(Nat.card K)^2) (Nat.card K) ω m).2,C.2)
noncomputable def pivotRight (pred : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (C : PivotContext K V) (ω : PivotTape pred C) (m : PivotMessage pred C ω) : PivotContext K V :=
  (C.1,C.2∩(finiteNodeDecoded (pred C) C.2 (1000*(Nat.card K)^2) (Nat.card K) ω m).1)

omit [Finite K] [FiniteDimensional K V] in
lemma pivot_inheritance (pred : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (C : PivotContext K V) (ω : PivotTape pred C) (m : PivotMessage pred C ω) :
    (pivotLeft pred C ω m).1⊆C.1 ∧ (pivotLeft pred C ω m).2=C.2 ∧
    (pivotRight pred C ω m).1=C.1 ∧ (pivotRight pred C ω m).2⊆C.2 :=
  ⟨Finset.inter_subset_left,rfl,rfl,Finset.inter_subset_left⟩

variable {ι : Type}

abbrev PivotTreeTape (pred : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (b : BinaryTree ι) := TreeCodec.Tape (fun _ : ι=>PivotTape pred) b
abbrev PivotTreeMessage (pred : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (b : BinaryTree ι) (ω : PivotTreeTape pred b) (C : PivotContext K V) :=
  TreeCodec.Message (fun _ : ι=>PivotTape pred) (fun _ : ι=>PivotMessage pred)
    (fun _ : ι=>pivotLeft pred) (fun _ : ι=>pivotRight pred) b ω C
noncomputable instance pivotTreeTapeFintype
    (pred : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (b : BinaryTree ι) : Fintype (PivotTreeTape pred b) := by
  letI : ∀(_ : ι) C,Fintype (PivotTape pred C) := fun _ _=>inferInstance
  exact @TreeCodec.tapeFintype ι (PivotContext K V) inferInstance (fun _ : ι=>PivotTape pred) (fun _ _=>inferInstance) b
noncomputable instance pivotTreeMessageFintype
    (pred : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (b : BinaryTree ι) (ω : PivotTreeTape pred b) (C : PivotContext K V) :
    Fintype (PivotTreeMessage pred b ω C) := by
  letI : ∀(_ : ι) C ω,Fintype (PivotMessage pred C ω) := fun _ _ _=>inferInstance
  exact TreeCodec.messageFintype (fun _ : ι=>PivotTape pred) (fun _ : ι=>PivotMessage pred)
    (fun _ : ι=>pivotLeft pred) (fun _ : ι=>pivotRight pred) b ω C
noncomputable def pivotTreeLaw (pred : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (b : BinaryTree ι) : Law (PivotTreeTape pred b) := by
  letI : ∀(_ : ι) C,Fintype (PivotTape pred C) := fun _ _=>inferInstance
  exact @TreeCodec.tapeLaw ι (PivotContext K V) inferInstance
    (fun _ : ι=>PivotTape pred) (fun _ _=>inferInstance)
    (fun _ C=>finiteNodeTapeLaw (pred C) (1000*(Nat.card K)^2) (Nat.card K)) b

noncomputable def pivotTreeEncoded
    (pred : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ : ι→Finset (ℙ K V)) (B₀ : ι→Finset (ℙ K (Dual K V)))
    (hA₀ : ∀i,(A₀ i).Nonempty) (hB₀ : ∀i,(B₀ i).Nonempty)
    (c δ τ P : ℝ) (hδ : 0<δ) (b : BinaryTree ι) (ω : PivotTreeTape pred b)
    (C : PivotContext K V) : PivotTreeMessage pred b ω C :=
  TreeCodec.encoded (fun _ : ι=>PivotTape pred) (fun _ : ι=>PivotMessage pred)
    (fun _ : ι=>pivotLeft pred) (fun _ : ι=>pivotRight pred)
    (fun i C ω=>guardedNodeEncoded (pred C) σ hσ hq hd (A₀ i) C.1 (B₀ i) C.2
      (hA₀ i) (hB₀ i) c δ τ (((A₀ i∩C.1).card:ℝ)*Real.exp (10*P)) hδ ω) b ω C
noncomputable def pivotTreeRetained
    (pred : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (b : BinaryTree ι) (ω : PivotTreeTape pred b) (C : PivotContext K V)
    (m : PivotTreeMessage pred b ω C) : BinaryTree ι :=
  TreeCodec.retained (fun _ : ι=>PivotTape pred) (fun _ : ι=>PivotMessage pred)
    (fun _ : ι=>pivotLeft pred) (fun _ : ι=>pivotRight pred) b ω C m

omit [Finite K] [FiniteDimensional K V] in
lemma pivotTree_retained_nodes
    (pred : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (b : BinaryTree ι) (ω : PivotTreeTape pred b) (C : PivotContext K V)
    (m : PivotTreeMessage pred b ω C) : (pivotTreeRetained pred b ω C m).numNodes≤b.numNodes :=
  TreeCodec.retained_nodes_le _ _ _ _ b ω C m
end SharpRamseyFive.ProjectiveIncidence

end OAI
