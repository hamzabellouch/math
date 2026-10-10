import OAI.Combinatorics.Crossing.PolygonalArcInjective
import OAI.Combinatorics.Crossing.FiniteAffineCover
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace OAI

noncomputable section
namespace Zarankiewicz

def StraightEdgeEmbedding {V : Type*} (G : SimpleGraph V) (pos : V → Plane) : Prop :=
  Function.Injective pos ∧
    ∀ a b c d, G.Adj a b → G.Adj c d → ∀ x,
      x ∈ segment ℝ (pos a) (pos b) → x ∈ segment ℝ (pos c) (pos d) →
      (a=c ∧ b=d) ∨ (a=d ∧ b=c) ∨
      (a=c ∧ x=pos a) ∨ (a=d ∧ x=pos a) ∨
      (b=c ∧ x=pos b) ∨ (b=d ∧ x=pos b)

def graphWalkPath {V : Type*} {G : SimpleGraph V} (pos : V → Plane) {a b : V} (p : G.Walk a b) :
    Path (pos a) (pos b) :=
  (polygonalArcPath (fun i => pos (p.getVert i)) p.length).cast
    (congrArg pos p.getVert_zero).symm (congrArg pos p.getVert_length).symm

theorem graphWalkPath_hasFiniteAffineCover {V : Type*} {G : SimpleGraph V} (pos : V → Plane)
    {a b : V} (p : G.Walk a b) : HasFiniteAffineCover (graphWalkPath pos p) :=
  polygonalArcPath_hasFiniteAffineCover _ _

theorem graphWalkPath_injective {V : Type*} {G : SimpleGraph V} (pos : V → Plane)
    (hemb : StraightEdgeEmbedding G pos) {a b : V} (hab : a ≠ b)
    (p : G.Walk a b) (hp : p.IsPath) : Function.Injective (graphWalkPath pos p) := by
  have hn : 0 < p.length := by
    by_contra h
    have hz : p.length=0 := by omega
    have he := p.getVert_zero.symm.trans (hz ▸ p.getVert_length)
    exact hab he
  change Function.Injective (polygonalArcPath (fun i => pos (p.getVert i)) p.length)
  apply polygonalArcPath_injective _ _ hn
  · intro i hi he
    have hij := hp.getVert_injOn (show i ≤ p.length by omega) (show i+1 ≤ p.length by omega) (hemb.1 he)
    omega
  · intro i j hij hj x hx hy
    have hmeet := hemb.2 _ _ _ _ (p.adj_getVert_succ (show i < p.length by omega))
      (p.adj_getVert_succ hj) x hx hy
    have hindex (r s : ℕ) (hr : r ≤ p.length) (hs : s ≤ p.length)
        (he : p.getVert r=p.getVert s) : r=s := hp.getVert_injOn hr hs he
    rcases hmeet with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ | ⟨h₁,hx⟩ | ⟨h₁,hx⟩ | ⟨h₁,hx⟩ | ⟨h₁,hx⟩
    · have hh := hindex i j (by omega) (by omega) h₁
      omega
    · have hh := hindex i (j+1) (by omega) (by omega) h₁
      omega
    · have hh := hindex i j (by omega) (by omega) h₁
      omega
    · have hh := hindex i (j+1) (by omega) (by omega) h₁
      omega
    · have hh := hindex (i+1) j (by omega) (by omega) h₁
      exact ⟨hh.symm,hx.trans (congrArg pos h₁)⟩
    · have hh := hindex (i+1) (j+1) (by omega) (by omega) h₁
      omega

theorem exists_simple_graphWalkPath {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (pos : V → Plane) (hemb : StraightEdgeEmbedding G pos) {a b : V} (hab : a ≠ b)
    (p : G.Walk a b) :
    ∃ q : G.Walk a b, q.IsPath ∧ List.Sublist q.darts p.darts ∧
      Function.Injective (graphWalkPath pos q) ∧ HasFiniteAffineCover (graphWalkPath pos q) :=
  ⟨p.bypass,p.bypass_isPath,p.darts_bypass_sublist_darts,
    graphWalkPath_injective pos hemb hab p.bypass p.bypass_isPath,
    graphWalkPath_hasFiniteAffineCover pos p.bypass⟩

end Zarankiewicz

end

end OAI
