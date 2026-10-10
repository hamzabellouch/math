import OAI.Probability.SwitchChain.AugmentedMatrixEquiv
import OAI.Probability.SwitchChain.ThreeVertexEncoding

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.TripleEncoding

variable {W : Type*} [Fintype W]

abbrev TripleBlock (s : Nat) (d : Fin 3 → Nat) (columns : W → Nat) :=
  {p : {G : SimpleGraph (Fin 3) // edgeCount G = s} × (Fin 3 → W → Fin 2) //
    AugmentedMatrix.BlockCompatible (fun G i => graphDegree G.val i) d columns p.1 p.2}

def oneEdgeBlockEquiv (d : Fin 3 → Nat) (columns : W → Nat) :
    TripleBlock 1 d columns ≃
      {M : Fin 3 → Option W → Fin 2 //
        AugmentedMatrix.Compatible (fun _ => 0) d columns 2 M} :=
  AugmentedMatrix.augmentedMatrixEquiv (fun G i => graphDegree G.val i)
    (fun _ => 0) d columns 2 oneEdgeColumnEquiv (by
      intro G i
      simpa only [zero_add] using (oneEdgeColumnEquiv_value G i).symm)

def twoEdgeBlockEquiv (d : Fin 3 → Nat) (columns : W → Nat) :
    TripleBlock 2 d columns ≃
      {M : Fin 3 → Option W → Fin 2 //
        AugmentedMatrix.Compatible (fun _ => 1) d columns 1 M} :=
  AugmentedMatrix.augmentedMatrixEquiv (fun G i => graphDegree G.val i)
    (fun _ => 1) d columns 1 twoEdgeColumnEquiv (by
      intro G i
      simpa only [Nat.add_comm] using twoEdgeColumnEquiv_degree G i)

theorem binaryColumn_zero_eq (c : BinaryColumn 0) : c.val = fun _ => 0 := by
  funext i
  apply Fin.ext
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp
    c.property i (Finset.mem_univ i)

def zeroEdgeColumnEquiv :
    {G : SimpleGraph (Fin 3) // edgeCount G = 0} ≃ BinaryColumn 0 where
  toFun _ := ⟨fun _ => 0, by simp⟩
  invFun _ := ⟨⊥, by simp [edgeCount]⟩
  left_inv G := Subtype.ext (eq_bot_of_edgeCount_zero G.val G.property).symm
  right_inv c := Subtype.ext (binaryColumn_zero_eq c).symm

def threeEdgeColumnEquiv :
    {G : SimpleGraph (Fin 3) // edgeCount G = 3} ≃ BinaryColumn 0 where
  toFun _ := ⟨fun _ => 0, by simp⟩
  invFun _ := ⟨⊤, by norm_num [edgeCount, SimpleGraph.top_adj, Fin.ext_iff]⟩
  left_inv G := Subtype.ext (eq_top_of_edgeCount_three G.val G.property).symm
  right_inv c := Subtype.ext (binaryColumn_zero_eq c).symm

def zeroEdgeBlockEquiv (d : Fin 3 → Nat) (columns : W → Nat) :
    TripleBlock 0 d columns ≃
      {M : Fin 3 → Option W → Fin 2 //
        AugmentedMatrix.Compatible (fun _ => 0) d columns 0 M} :=
  AugmentedMatrix.augmentedMatrixEquiv (fun G i => graphDegree G.val i)
    (fun _ => 0) d columns 0 zeroEdgeColumnEquiv (by
      intro G i
      change graphDegree G.val i = 0
      exact graphDegree_of_edgeCount_zero G.val G.property i)

def threeEdgeBlockEquiv (d : Fin 3 → Nat) (columns : W → Nat) :
    TripleBlock 3 d columns ≃
      {M : Fin 3 → Option W → Fin 2 //
        AugmentedMatrix.Compatible (fun _ => 2) d columns 0 M} :=
  AugmentedMatrix.augmentedMatrixEquiv (fun G i => graphDegree G.val i)
    (fun _ => 2) d columns 0 threeEdgeColumnEquiv (by
      intro G i
      change graphDegree G.val i = 2
      exact graphDegree_of_edgeCount_three G.val G.property i)

end Problem315.TripleEncoding

end

end OAI
