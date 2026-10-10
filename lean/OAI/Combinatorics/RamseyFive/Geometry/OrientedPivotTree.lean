import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.GuardedNodeSent
import OAI.Combinatorics.RamseyFive.Geometry.ConcretePivot

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))

abbrev OrientedPivotTape (C : PivotContext K V) :=
  OrientedNodeTape (f C) (r C) (1000*(Nat.card K)^2) (Nat.card K)
abbrev OrientedPivotMessage (C : PivotContext K V) (ω : OrientedPivotTape f r C) :=
  OrientedNodeMessage (f C) (r C) C.1 C.2 (1000*(Nat.card K)^2) (Nat.card K) ω
noncomputable instance orientedPivotMessageFintype (C : PivotContext K V) (ω : OrientedPivotTape f r C) :
    Fintype (OrientedPivotMessage f r C ω) := by
  exact @instFintypeSum
    (FiniteNodeMessage (f C) C.2 (1000*(Nat.card K)^2) (Nat.card K) ω.1)
    (FiniteNodeMessage (r C) (C.1.map bidualPoint.toEmbedding) (1000*(Nat.card K)^2) (Nat.card K) ω.2)
    inferInstance inferInstance
noncomputable def orientedPivotLeft (C : PivotContext K V)
    (ω : OrientedPivotTape f r C) (m : OrientedPivotMessage f r C ω) : PivotContext K V :=
  (C.1∩(orientedNodeDecoded (f C) (r C) C.1 C.2 (1000*(Nat.card K)^2) (Nat.card K) ω m).2,C.2)
noncomputable def orientedPivotRight (C : PivotContext K V)
    (ω : OrientedPivotTape f r C) (m : OrientedPivotMessage f r C ω) : PivotContext K V :=
  (C.1,C.2∩(orientedNodeDecoded (f C) (r C) C.1 C.2 (1000*(Nat.card K)^2) (Nat.card K) ω m).1)
omit [Finite K] in
lemma orientedPivot_inheritance (C : PivotContext K V)
    (ω : OrientedPivotTape f r C) (m : OrientedPivotMessage f r C ω) :
    (orientedPivotLeft f r C ω m).1⊆C.1 ∧ (orientedPivotLeft f r C ω m).2=C.2 ∧
    (orientedPivotRight f r C ω m).1=C.1 ∧ (orientedPivotRight f r C ω m).2⊆C.2 :=
  ⟨Finset.inter_subset_left,rfl,rfl,Finset.inter_subset_left⟩

variable {ι : Type}
abbrev OrientedPivotTreeTape (b : BinaryTree ι) := TreeCodec.Tape (fun _ : ι=>OrientedPivotTape f r) b
abbrev OrientedPivotTreeMessage (b : BinaryTree ι) (ω : OrientedPivotTreeTape f r b)
    (C : PivotContext K V) :=
  TreeCodec.Message (fun _ : ι=>OrientedPivotTape f r) (fun _ : ι=>OrientedPivotMessage f r)
    (fun _ : ι=>orientedPivotLeft f r) (fun _ : ι=>orientedPivotRight f r) b ω C
noncomputable instance orientedPivotTreeTapeFintype (b : BinaryTree ι) :
    Fintype (OrientedPivotTreeTape f r b) := by
  exact @TreeCodec.tapeFintype ι (PivotContext K V) inferInstance
    (fun _ : ι=>OrientedPivotTape f r) (fun _ _=>orientedNodeTapeFintype _ _ _ _) b
noncomputable instance orientedPivotTreeMessageFintype (b : BinaryTree ι)
    (ω : OrientedPivotTreeTape f r b) (C : PivotContext K V) :
    Fintype (OrientedPivotTreeMessage f r b ω C) := by
  letI : ∀(_ : ι) C ω,Fintype (OrientedPivotMessage f r C ω) := fun _ _ _=>inferInstance
  exact TreeCodec.messageFintype (fun _ : ι=>OrientedPivotTape f r) (fun _ : ι=>OrientedPivotMessage f r)
    (fun _ : ι=>orientedPivotLeft f r) (fun _ : ι=>orientedPivotRight f r) b ω C
noncomputable def orientedPivotTreeLaw (b : BinaryTree ι) : Law (OrientedPivotTreeTape f r b) := by
  exact @TreeCodec.tapeLaw ι (PivotContext K V) inferInstance
    (fun _ : ι=>OrientedPivotTape f r) (fun _ _=>orientedNodeTapeFintype _ _ _ _)
    (fun _ C=>orientedNodeTapeLaw (f C) (r C) (1000*(Nat.card K)^2) (Nat.card K)) b

noncomputable def orientedPivotTreeEncoded
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ : ι→Finset (ℙ K V)) (B₀ : ι→Finset (ℙ K (Dual K V)))
    (hA₀ : ∀i,(A₀ i).Nonempty) (hB₀ : ∀i,(B₀ i).Nonempty)
    (c δ τ P : ℝ) (hδ : 0<δ) (b : BinaryTree ι) (ω : OrientedPivotTreeTape f r b)
    (C : PivotContext K V) : OrientedPivotTreeMessage f r b ω C :=
  TreeCodec.encoded (fun _ : ι=>OrientedPivotTape f r) (fun _ : ι=>OrientedPivotMessage f r)
    (fun _ : ι=>orientedPivotLeft f r) (fun _ : ι=>orientedPivotRight f r)
    (fun i C ω=>orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd (A₀ i) C.1 (B₀ i) C.2
      (hA₀ i) (hB₀ i) c δ τ P hδ ω) b ω C
noncomputable def orientedPivotTreeRetained (b : BinaryTree ι)
    (ω : OrientedPivotTreeTape f r b) (C : PivotContext K V)
    (m : OrientedPivotTreeMessage f r b ω C) : BinaryTree ι :=
  TreeCodec.retained (fun _ : ι=>OrientedPivotTape f r) (fun _ : ι=>OrientedPivotMessage f r)
    (fun _ : ι=>orientedPivotLeft f r) (fun _ : ι=>orientedPivotRight f r) b ω C m
omit [Finite K] in
lemma orientedPivotTree_retained_nodes (b : BinaryTree ι)
    (ω : OrientedPivotTreeTape f r b) (C : PivotContext K V)
    (m : OrientedPivotTreeMessage f r b ω C) :
    (orientedPivotTreeRetained f r b ω C m).numNodes≤b.numNodes :=
  TreeCodec.retained_nodes_le _ _ _ _ b ω C m
end SharpRamseyFive.ProjectiveIncidence

end OAI
