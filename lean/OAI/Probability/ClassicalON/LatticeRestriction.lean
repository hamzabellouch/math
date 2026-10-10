import OAI.Probability.ClassicalON.LatticeGeometry

namespace OAI

noncomputable section
open Set
open scoped Classical
namespace ClassicalON.LatticeGraph

def restrictVertices (G : LatticeGraph) (P : Site → Prop) : Finset Site := G.vertices.filter P

def restrictVertex (G : LatticeGraph) (P : Site → Prop) (v : G.restrictVertices P) : G.vertices :=
  ⟨v.val,(Finset.mem_filter.mp v.property).1⟩

def restrict (G : LatticeGraph) (P : Site → Prop) : LatticeGraph where
  vertices := G.restrictVertices P
  edges := Finset.univ.filter (fun e : G.restrictVertices P × G.restrictVertices P =>
    (G.restrictVertex P e.1,G.restrictVertex P e.2)∈G.edges)
  nearest _e he := G.nearest _ (Finset.mem_filter.mp he).2

def restrictEdge (G : LatticeGraph) (P : Site → Prop) (e : (G.restrict P).edges) : G.edges :=
  ⟨(G.restrictVertex P e.val.1,G.restrictVertex P e.val.2),(Finset.mem_filter.mp e.property).2⟩

def restrictVertexEquiv (G : LatticeGraph) (P : Site → Prop) :
    {v : G.vertices // P v.val} ≃ (G.restrict P).vertices where
  toFun v := ⟨v.val.val,Finset.mem_filter.mpr ⟨v.val.property,v.property⟩⟩
  invFun v := ⟨G.restrictVertex P v,(Finset.mem_filter.mp v.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def restrictEdgeEquiv (G : LatticeGraph) (P : Site → Prop) :
    {e : G.edges // P e.val.1.val ∧ P e.val.2.val} ≃ (G.restrict P).edges where
  toFun e := ⟨(⟨e.val.val.1.val,Finset.mem_filter.mpr ⟨e.val.val.1.property,e.property.1⟩⟩,
    ⟨e.val.val.2.val,Finset.mem_filter.mpr ⟨e.val.val.2.property,e.property.2⟩⟩),
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.val.property⟩⟩
  invFun e := ⟨G.restrictEdge P e,(Finset.mem_filter.mp e.val.1.property).2,
    (Finset.mem_filter.mp e.val.2.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem restrictVertexEquiv_val (G : LatticeGraph) (P : Site → Prop)
    (v : {v : G.vertices // P v.val}) : (G.restrictVertexEquiv P v).val=v.val.val := rfl

@[simp] theorem restrictEdgeEquiv_left (G : LatticeGraph) (P : Site → Prop)
    (e : {e : G.edges // P e.val.1.val ∧ P e.val.2.val}) :
    (G.restrictEdgeEquiv P e).val.1=G.restrictVertexEquiv P ⟨e.val.val.1,e.property.1⟩ := rfl

@[simp] theorem restrictEdgeEquiv_right (G : LatticeGraph) (P : Site → Prop)
    (e : {e : G.edges // P e.val.1.val ∧ P e.val.2.val}) :
    (G.restrictEdgeEquiv P e).val.2=G.restrictVertexEquiv P ⟨e.val.val.2,e.property.2⟩ := rfl

def translateVertexEquiv (G : LatticeGraph) (z : Site) :
    G.vertices ≃ G.vertices.map (Equiv.addRight (-z)).toEmbedding :=
  Finset.equivMap (Equiv.addRight (-z)).toEmbedding G.vertices

def translate (G : LatticeGraph) (z : Site) : LatticeGraph where
  vertices := G.vertices.map (Equiv.addRight (-z)).toEmbedding
  edges := G.edges.map ((Equiv.prodCongr (G.translateVertexEquiv z) (G.translateVertexEquiv z)).toEmbedding)
  nearest e he := by
    obtain ⟨e',he',rfl⟩ := Finset.mem_map.mp he
    have h := G.nearest e' he'
    change PositiveNeighbor (e'.1.val+-z) (e'.2.val+-z)
    rcases h with h | h
    · left
      constructor <;> simp only [Prod.fst_add,Prod.snd_add,Prod.fst_neg,Prod.snd_neg]
      · omega
      · omega
    · right
      constructor <;> simp only [Prod.fst_add,Prod.snd_add,Prod.fst_neg,Prod.snd_neg]
      · omega
      · omega

def translateEdgeEquiv (G : LatticeGraph) (z : Site) : G.edges ≃ (G.translate z).edges :=
  Finset.equivMap ((Equiv.prodCongr (G.translateVertexEquiv z) (G.translateVertexEquiv z)).toEmbedding) G.edges

@[simp] theorem translateVertexEquiv_val (G : LatticeGraph) (z : Site) (v : G.vertices) :
    (G.translateVertexEquiv z v).val=v.val-z := rfl

@[simp] theorem translateEdgeEquiv_left (G : LatticeGraph) (z : Site) (e : G.edges) :
    (G.translateEdgeEquiv z e).val.1=G.translateVertexEquiv z e.val.1 := rfl

@[simp] theorem translateEdgeEquiv_right (G : LatticeGraph) (z : Site) (e : G.edges) :
    (G.translateEdgeEquiv z e).val.2=G.translateVertexEquiv z e.val.2 := rfl

end ClassicalON.LatticeGraph

end

end OAI
