import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.ProjectionComponent

namespace OAI

namespace ProjectionComparison

open Set Filter ClusterDisplacement

attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [Fintype E]

def transmissionGraph (S : System V E) (u₀ u₁ : ℝ → V → ℝ) (δ : ℝ) : SimpleGraph {x // x∉S.pins} where
  Adj x y := x≠y ∧ ∃e,∃t∈Icc (0:ℝ) 1,
    (S.cost e-(u₀ t (S.left e)-u₀ t (S.right e))≤δ ∨
     S.cost e-(u₁ t (S.left e)-u₁ t (S.right e))≤δ) ∧
    ((S.left e=x.val ∧ S.right e=y.val) ∨ (S.left e=y.val ∧ S.right e=x.val))
  symm := ⟨by rintro x y ⟨hne,e,t,ht,hsl,hor⟩;exact ⟨hne.symm,e,t,ht,hsl,hor.symm⟩⟩
  loopless := ⟨by intro x hx;exact hx.1 rfl⟩

def transmissionSet (S : System V E) (u₀ u₁ : ℝ → V → ℝ) (δ : ℝ) (root : {x // x∉S.pins}) : Set V :=
  {x | x∈S.pins ∨ ∃hx : x∉S.pins,(transmissionGraph S u₀ u₁ δ).Reachable root ⟨x,hx⟩}

end ProjectionComparison

namespace ProjectionComparison

open Set Filter ClusterDisplacement

attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
lemma transmission_edge_reachable (S : System V E) (u₀ u₁ : ℝ → V → ℝ) (δ t : ℝ)
    (ht : t∈Icc (0:ℝ) 1) (e : E)
    (hsl : S.cost e-(u₀ t (S.left e)-u₀ t (S.right e))≤δ ∨
      S.cost e-(u₁ t (S.left e)-u₁ t (S.right e))≤δ)
    (hl : S.left e∉S.pins) (hr : S.right e∉S.pins) :
    (transmissionGraph S u₀ u₁ δ).Reachable ⟨S.left e,hl⟩ ⟨S.right e,hr⟩ := by
  by_cases he : S.left e=S.right e
  · have he' : (⟨S.left e,hl⟩ : {x // x∉S.pins})=⟨S.right e,hr⟩ := Subtype.ext he
    rw [he']
  · apply SimpleGraph.Adj.reachable
    refine ⟨?_,e,t,ht,hsl,Or.inl ⟨rfl,rfl⟩⟩
    intro he'
    exact he (congrArg Subtype.val he')

omit [Fintype V] [Fintype E] in
lemma transmissionSet_free (S : System V E) (u₀ u₁ : ℝ → V → ℝ) (δ : ℝ)
    (root : {x // x∉S.pins}) (x : V) (hx : x∉S.pins) :
    x∈transmissionSet S u₀ u₁ δ root ↔ (transmissionGraph S u₀ u₁ δ).Reachable root ⟨x,hx⟩ := by
  constructor
  · rintro (hp | ⟨hx',hr⟩)
    · exact (hx hp).elim
    · exact hr
  · intro hr;exact Or.inr ⟨hx,hr⟩

omit [Fintype V] [Fintype E] in
lemma transmissionSet_closed (S : System V E) (u₀ u₁ : ℝ → V → ℝ) (δ t : ℝ)
    (root : {x // x∉S.pins}) (ht : t∈Icc (0:ℝ) 1) (e : E)
    (hsl : S.cost e-(u₀ t (S.left e)-u₀ t (S.right e))≤δ ∨
      S.cost e-(u₁ t (S.left e)-u₁ t (S.right e))≤δ)
    (hl : S.left e∉S.pins) (hr : S.right e∉S.pins) :
    S.left e∈transmissionSet S u₀ u₁ δ root ↔ S.right e∈transmissionSet S u₀ u₁ δ root := by
  rw [transmissionSet_free S u₀ u₁ δ root _ hl,transmissionSet_free S u₀ u₁ δ root _ hr]
  have he := transmission_edge_reachable S u₀ u₁ δ t ht e hsl hl hr
  exact ⟨fun h => h.trans he,fun h => h.trans he.symm⟩

omit [Fintype E] in
lemma transmission_free_card (S : System V E) (u₀ u₁ : ℝ → V → ℝ) (δ : ℝ)
    (root : {x // x∉S.pins}) :
    Fintype.card {x : transmissionSet S u₀ u₁ δ root // x.val∉S.pins}=
      Fintype.card {x : {x // x∉S.pins} // (transmissionGraph S u₀ u₁ δ).Reachable root x} := by
  apply Fintype.card_congr
  exact {
    toFun := fun x => ⟨⟨x.val.val,x.property⟩,(transmissionSet_free S u₀ u₁ δ root _ x.property).mp x.val.property⟩
    invFun := fun x => ⟨⟨x.val.val,Or.inr ⟨x.val.property,x.property⟩⟩,x.val.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

end ProjectionComparison

namespace ProjectionComparison

open Set Filter ClusterDisplacement

attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [Fintype E]

theorem transmission_cluster_tail (S : System V E)
    (b₀ b₁ h₀ h₁ : V → ℝ) (hh₀ : h₀∈feasible S b₀) (hh₁ : h₁∈feasible S b₁)
    (w : ℝ → FreeSpace S) (u₀ u₁ : ℝ → V → ℝ)
    (hlim₀ : TendstoUniformlyOn (fun n => pathMesh S b₀ h₀ hh₀ w (n+1)) u₀ atTop (Icc 0 1))
    (hlim₁ : TendstoUniformlyOn (fun n => pathMesh S b₁ h₁ hh₁ w (n+1)) u₁ atTop (Icc 0 1))
    (δ : ℝ) (hδ : 0<δ) (root : {x // x∉S.pins})
    (a : ℝ) (hb : ∀x∈S.pins,b₁ x-b₀ x≤a) :
    let W := transmissionSet S u₀ u₁ δ root
    0≤energy (componentPathTail S W u₀ u₁ a 0)-energy (componentPathTail S W u₀ u₁ a 1) ∧
    ∀t∈Icc (0:ℝ) 1,∀x : {x : W // x.val∉S.pins},
      |componentPathTail S W u₀ u₁ a t x-componentPathTail S W u₀ u₁ a 0 x|≤
        5*(Fintype.card {x : W // x.val∉S.pins}+1:ℝ)*
          Real.sqrt (energy (componentPathTail S W u₀ u₁ a 0)-energy (componentPathTail S W u₀ u₁ a 1)) := by
  exact transmission_component_tail S _ (fun x hx => Or.inl hx) b₀ b₁ h₀ h₁ hh₀ hh₁ w u₀ u₁
    hlim₀ hlim₁ δ hδ
    (fun t ht e he hl hr => transmissionSet_closed S u₀ u₁ δ t root ht e (Or.inl he) hl hr)
    (fun t ht e he hl hr => transmissionSet_closed S u₀ u₁ δ t root ht e (Or.inr he) hl hr) a hb

end ProjectionComparison

end OAI
