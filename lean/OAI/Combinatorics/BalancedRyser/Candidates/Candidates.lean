import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Topology.Instances.ENNReal.Lemmas
import OAI.Combinatorics.BalancedRyser.Construction.Construction

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
open scoped Classical
open Filter Topology

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def SupportsValidTuple (M : MergedPairs F) (l : Line F) : Prop :=
  ∃ T : FourTuple F, ValidChoice M l.1 ⟨l, T⟩

def retainedChoice (M : MergedPairs F) (l : Line F) : SplitChoice F :=
  ⟨l, if h : SupportsValidTuple M l then Classical.choose h
    else ⟨fun _ => none, fun _ => false⟩⟩

abbrev CandidateVertex (F : Type*) := Slot F × F

def candidateLine (v : CandidateVertex F) : Line F := (v.1.1, v.2)

def candidateChoice (M : MergedPairs F) (v : CandidateVertex F) : SplitChoice F :=
  retainedChoice M (candidateLine v)

def candidateVertices (M : MergedPairs F) : Finset (CandidateVertex F) :=
  Finset.univ.filter (fun v => SupportsValidTuple M (candidateLine v))

def candidateSlot (M : MergedPairs F) (s : Slot F) : Finset (CandidateVertex F) :=
  (candidateVertices M).filter (fun v => v.1 = s)

def ChoicesCompatible (M : MergedPairs F) (g h : Direction F)
    (A B : SplitChoice F) : Prop :=
  (∀ p ∈ designated M A, ¬ OnLine p B.line) ∧
  (∀ p ∈ designated M B, ¬ OnLine p A.line) ∧
  ((generatorSet A.tuple) ∩ (generatorSet B.tuple)).card ≤ 1 ∧
  (g = h → ∀ d,
    ¬ (2 ≤ ((designated M A) ∩ mergedPoints M d).card ∧
       1 ≤ ((designated M B) ∩ mergedPoints M d).card) ∧
    ¬ (2 ≤ ((designated M B) ∩ mergedPoints M d).card ∧
       1 ≤ ((designated M A) ∩ mergedPoints M d).card))

def CandidateAdjacent (M : MergedPairs F) (v w : CandidateVertex F) : Prop :=
  v ∈ candidateVertices M ∧ w ∈ candidateVertices M ∧ v.1 ≠ w.1 ∧
  ¬ ChoicesCompatible M v.1.1 w.1.1 (candidateChoice M v) (candidateChoice M w)

def candidateNeighbors (M : MergedPairs F) (v : CandidateVertex F) : Finset (CandidateVertex F) :=
  (candidateVertices M).filter (CandidateAdjacent M v)

def sampledMultiplicity (M : MergedPairs F) (p : Point F) : ℕ :=
  (Finset.univ.filter (fun ds : Direction F × Bool => OnLine p (constituent M ds.1 ds.2))).card

def initialDeletedLines (M : MergedPairs F) : Finset (Line F) :=
  Finset.univ.image (fun d => constituent M d true)

def initiallyRetained (M : MergedPairs F) : Finset (Point F) :=
  Finset.univ.filter (fun p => ∀ l ∈ initialDeletedLines M, ¬ OnLine p l)

def CandidateGraphGood (M : MergedPairs F) (c C : ℝ) : Prop :=
  let q : ℝ := Fintype.card F
  (∀ s, c * q ≤ ((candidateSlot M s).card : ℝ) ∧
    (candidateSlot M s).card ≤ Fintype.card F) ∧
  (∀ v ∈ candidateVertices M,
    ((candidateNeighbors M v).card : ℝ) ≤ C * q ∧
    ∀ s, (((candidateNeighbors M v) ∩ candidateSlot M s).card : ℝ) ≤ q ^ (1 / 8 : ℝ)) ∧
  (∀ v ∈ candidateVertices M, ∃ J : Finset (CandidateVertex F),
    J ⊆ candidateVertices M ∧ (J.card : ℝ) ≤ q ^ (1 / 8 : ℝ) ∧
    (∀ w ∈ J, CandidateAdjacent M v w ∨ w.1 = v.1) ∧
    ∀ w ∈ candidateVertices M, w ∉ J →
      (((candidateNeighbors M v) ∩ candidateNeighbors M w).card : ℝ) ≤ q ^ (1 / 8 : ℝ)) ∧
  (∀ p, sampledMultiplicity M p ≤ ⌈Real.log q⌉₊) ∧
  (∀ l, l ∉ initialDeletedLines M →
    (1 / 5 : ℝ) * q ≤ ((linePoints l ∩ initiallyRetained M).card : ℝ))

def offsetLaw (F : Type*) [Field F] [Fintype F] : PMF (MergedPairs F) :=
  PMF.uniformOfFintype (MergedPairs F)

def offsetEventProbability (E : Set (MergedPairs F)) : ℝ :=
  ((offsetLaw F).toOuterMeasure E).toReal

def CandidateSelector (M : MergedPairs F) (f : Slot F → F) : Prop :=
  ∀ s, SupportsValidTuple M (s.1, f s)

def IndependentSelector (M : MergedPairs F) (f : Slot F → F) : Prop :=
  ∀ s t, s ≠ t → ¬ CandidateAdjacent M (s, f s) (t, f t)

def selectedConfiguration (M : MergedPairs F) (f : Slot F → F) : Configuration F :=
  ⟨M, fun s => retainedChoice M (s.1, f s)⟩

universe u

def CandidateGraphResult : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
  ∀ (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)] [∀ n, DecidableEq (F n)],
    Tendsto (fun n => Fintype.card (F n)) atTop atTop →
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | CandidateGraphGood M c C}) atTop (𝓝 1) ∧
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | CandidateGraphGood M c C ∧ DistinctConstituents M}) atTop (𝓝 (Real.exp (-1)))

end
end Balanced

end OAI
