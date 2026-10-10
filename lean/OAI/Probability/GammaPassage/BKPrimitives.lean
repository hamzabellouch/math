import OAI.Probability.GammaPassage.CrossingLocalized
import OAI.Probability.GammaPassage.BKForcing
import OAI.Probability.GammaPassage.DyadicRanks

namespace OAI

namespace GammaFPP.BK
open PlanarFPP Finset

/-- The same physical support used by the crossing and spatial events. -/
abbrev pathEdges := GammaFPP.CrossingBridge.pathEdges

@[simp] theorem pathEdges_eq_crossing (p : Vertex) (ds : List Step) :
    pathEdges p ds = GammaFPP.CrossingBridge.pathEdges p ds := rfl

theorem pathCost_eq_of_agree (w w' : Edge → ℝ) (p : Vertex) (ds : List Step)
    (h : ∀ e ∈ pathEdges p ds, w e=w' e) : pathCost w p ds=pathCost w' p ds := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih =>
    simp only [pathCost]
    rw [h (d.edge p) (by simp [pathEdges, GammaFPP.CrossingBridge.pathEdges])]
    rw [ih (p+d.delta) (fun e he => h e (by simp [pathEdges, GammaFPP.CrossingBridge.pathEdges,he]))]

/-- A labelled strict finite path. Different bounds on the same path are
retained as different witnesses. -/
structure StrictPathWitness where
  start : Vertex
  steps : List Step
  bound : ℝ

namespace StrictPathWitness

def edges (p : StrictPathWitness) : Finset Edge := pathEdges p.start p.steps

def bits (p : StrictPathWitness) (t : ℕ) : Finset (Edge × Fin t) := p.edges ×ˢ univ

end StrictPathWitness

/-- The bits in `x` are the zero bits of the manuscript's uniform expansion.
This is exactly 1-U^(t); zero is the cell whose rounded cost is infinity. -/
noncomputable def dyadicSurvival (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) : ℝ :=
  ∑ h : Fin t, if (e,h) ∈ x then 1/(2:ℝ)^(h.val+1) else 0

lemma dyadicSurvival_nonneg (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) :
    0 ≤ dyadicSurvival t x e := by
  apply Finset.sum_nonneg
  intro h _
  split_ifs <;> positivity

lemma dyadicSurvival_mono (t : ℕ) {x y : Finset (Edge × Fin t)} (hxy : x ⊆ y) (e : Edge) :
    dyadicSurvival t x e ≤ dyadicSurvival t y e := by
  apply Finset.sum_le_sum
  intro h _
  by_cases hx : (e,h) ∈ x
  · simp [hx,hxy hx]
  · simp only [hx,↓reduceIte]
    split_ifs <;> positivity

lemma dyadicSurvival_eq (t : ℕ) (x y : Finset (Edge × Fin t)) (e : Edge)
    (h : ∀ a : Fin t, (e,a) ∈ x ↔ (e,a) ∈ y) :
    dyadicSurvival t x e = dyadicSurvival t y e := by
  apply Finset.sum_congr rfl
  intro a _
  simp only [h a]

lemma pathCost_le_of_edges {w v : Edge → ℝ} (p : Vertex) (ds : List Step)
    (h : ∀ e ∈ pathEdges p ds, w e ≤ v e) : pathCost w p ds ≤ pathCost v p ds := by
  induction ds generalizing p with
  | nil => exact le_rfl
  | cons d ds ih =>
    exact add_le_add (h _ (by simp [pathEdges, GammaFPP.CrossingBridge.pathEdges]))
      (ih _ (fun e he => h e (by simp [pathEdges, GammaFPP.CrossingBridge.pathEdges,he])))

lemma StrictPathWitness.disjoint_bits {p q : StrictPathWitness} (t : ℕ)
    (h : Disjoint p.edges q.edges) : Disjoint (p.bits t) (q.bits t) := by
  apply Finset.disjoint_left.mpr
  intro a hp hq
  exact Finset.disjoint_left.mp h (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hq).1

def StrictPathWitness.Good (w : Edge → ℝ) (p : StrictPathWitness) : Prop :=
  pathCost w p.start p.steps < p.bound

/-- Original strict witnesses with pairwise disjoint physical edge supports. -/
def StrictDisjointPaths (S : Finset Edge) (Fs : List (Set StrictPathWitness)) (w : Edge → ℝ) : Prop :=
  ∃ ps : List StrictPathWitness,
    List.Forall₂ (fun p F => p ∈ F ∧ p.edges ⊆ S ∧ p.Good w) ps Fs ∧
    ps.Pairwise (fun p q => Disjoint p.edges q.edges)

lemma dyadicRank_sum (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) :
    dyadicRank t x e = ∑ h : Fin t, if (e,h) ∈ x then 2^(t-(h.val+1)) else 0 := by
  unfold dyadicRank dyadicPositions
  rw [sum_image]
  · simp only [sum_filter]
  · intro a _ b _ hab
    change t-(a.val+1)=t-(b.val+1) at hab
    apply Fin.ext
    have := a.isLt
    have := b.isLt
    omega

/-- Exact binary representation of the source rounded survival probability. -/
lemma dyadicSurvival_eq_rank (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) :
    dyadicSurvival t x e = (dyadicRank t x e : ℝ)/(2:ℝ)^t := by
  rw [dyadicRank_sum]
  simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_zero]
  rw [Finset.sum_div]
  unfold dyadicSurvival
  apply sum_congr rfl
  intro h _
  by_cases hm : (e,h) ∈ x
  · simp only [hm,↓reduceIte]
    have hh : t=(t-(h.val+1))+(h.val+1) := by omega
    have hp : (2:ℝ)^t = 2^(t-(h.val+1))*2^(h.val+1) := by rw [← pow_add,← hh]
    rw [hp]
    field_simp
  · simp [hm]

/-- Existence of a strict path witness with support in a prescribed finite edge set. -/
def StrictPathEvent (S : Finset Edge) (F : Set StrictPathWitness) (w : Edge → ℝ) : Prop :=
  ∃ p ∈ F, p.edges ⊆ S ∧ p.Good w

@[simp] theorem StrictPathWitness.edges_eq_crossing (p : StrictPathWitness) :
    p.edges = GammaFPP.CrossingBridge.pathEdges p.start p.steps := rfl

end GammaFPP.BK

end OAI
