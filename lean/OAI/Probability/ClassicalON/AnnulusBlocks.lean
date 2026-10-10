import OAI.Probability.ClassicalON.BlockLocal

namespace OAI

universe uK

noncomputable section
open Set
open scoped Classical
namespace ClassicalON.LatticeGraph
variable {K : Type uK}

def annulusFreeEquiv (G : LatticeGraph) (N : ℤ) (hN : 0≤N) (z : K → Site)
    (hz : SeparatedCenters N z) (i : K) :
    BlockVertex (G.allAnnulusPins N z) (G.annulusVertexLabel N z) (some i) ≃
      ↥((G.annulusPins N (z i))ᶜ) where
  toFun v := ⟨⟨v.val.val.val,Finset.mem_filter.mpr ⟨v.val.val.property,
    (centerLabel_some_iff N z hz _ i).mp v.property⟩⟩,
    fun hp => v.val.property ⟨i,hp⟩⟩
  invFun v := ⟨⟨G.restrictVertex _ v.val,fun hp => v.property
    ((local_centerPins_iff N hN z hz _ i (Finset.mem_filter.mp v.val.property).2).mp hp)⟩,
    (centerLabel_some_iff N z hz _ i).mpr (Finset.mem_filter.mp v.val.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def annulusEdgesEquiv (G : LatticeGraph) (N : ℤ) (z : K → Site)
    (hz : SeparatedCenters N z) (i : K) :
    {e : G.edges // G.annulusEdgeLabel N z e=some i} ≃ (G.annulusGraph N (z i)).edges :=
  (Equiv.subtypeEquivRight (fun e => G.annulusEdgeLabel_some_iff N z hz e i)).trans
    (G.restrictEdgeEquiv (·∈annulusSites N (z i)))

@[simp] theorem annulusEdgesEquiv_restrictEdge (G : LatticeGraph) (N : ℤ) (z : K → Site)
    (hz : SeparatedCenters N z) (i : K) (e : {e : G.edges // G.annulusEdgeLabel N z e=some i}) :
    G.restrictEdge _ (G.annulusEdgesEquiv N z hz i e)=e.val := rfl

theorem annulus_blockSpin (G : LatticeGraph) (N : ℤ) (hN : 0≤N) (z : K → Site)
    (hz : SeparatedCenters N z) (i : K) (s : ↥((G.annulusPins N (z i))ᶜ) → Spin 3)
    (v : (G.annulusGraph N (z i)).vertices) :
    glueFamily (G.annulusPins N (z i)) (fun _ => poleSpin true) s v=
      blockSpin (G.allAnnulusPins N z) (G.annulusVertexLabel N z) (some i)
        (fun w => s (G.annulusFreeEquiv N hN z hz i w)) (G.restrictVertex _ v) := by
  by_cases hp : v∈G.annulusPins N (z i)
  · have hB : G.restrictVertex _ v∈G.allAnnulusPins N z := ⟨i,hp⟩
    rw [show glueFamily (G.annulusPins N (z i)) (fun _ => poleSpin true) s v=poleSpin true from
      glueFamily_in _ _ _ ⟨v,hp⟩]
    simp only [blockSpin,hB,↓reduceDIte]
  · have hB : G.restrictVertex _ v∉G.allAnnulusPins N z := by
      intro h
      exact hp ((local_centerPins_iff N hN z hz v.val i (Finset.mem_filter.mp v.property).2).mp h)
    have hl : G.annulusVertexLabel N z (G.restrictVertex _ v)=some i :=
      (centerLabel_some_iff N z hz v.val i).mpr (Finset.mem_filter.mp v.property).2
    rw [show glueFamily (G.annulusPins N (z i)) (fun _ => poleSpin true) s v=s ⟨v,hp⟩ from
      glueFamily_out _ _ _ ⟨v,hp⟩]
    simp only [blockSpin,hB,hl,↓reduceDIte]
    rfl

theorem annulus_blockMean (G : LatticeGraph) (b : G.edges → ℝ) (N : ℤ) (hN : 0≤N)
    (z : K → Site) (hz : SeparatedCenters N z) (i : K)
    (f : ((G.annulusGraph N (z i)).edges → Bool) → ℝ) :
    poleBondMean (fun e : (G.annulusGraph N (z i)).edges => e.val.1) (fun e => e.val.2)
      (G.annulusCoupling b N (z i)) (G.annulusPins N (z i)) (fun _ => true) f=
    blockBondMean (fun e : G.edges => e.val.1) (fun e => e.val.2) b
      (G.allAnnulusPins N z) (G.annulusVertexLabel N z) (G.annulusEdgeLabel N z) (some i)
      (fun η => f (arrowEquiv (G.annulusEdgesEquiv N z hz i) η)) := by
  apply blockBondMean_local (fun e : G.edges => e.val.1) (fun e => e.val.2) b
    (G.allAnnulusPins N z) (G.annulusVertexLabel N z) (G.annulusEdgeLabel N z) (some i)
    (fun e : (G.annulusGraph N (z i)).edges => e.val.1) (fun e => e.val.2)
    (G.annulusCoupling b N (z i)) (G.annulusPins N (z i)) (G.annulusFreeEquiv N hN z hz i)
    (G.annulusEdgesEquiv N z hz i)
  · intro e; rfl
  · intro s e
    exact G.annulus_blockSpin N hN z hz i s (G.annulusEdgesEquiv N z hz i e).val.1
  · intro s e
    exact G.annulus_blockSpin N hN z hz i s (G.annulusEdgesEquiv N z hz i e).val.2

end ClassicalON.LatticeGraph

end

end OAI
