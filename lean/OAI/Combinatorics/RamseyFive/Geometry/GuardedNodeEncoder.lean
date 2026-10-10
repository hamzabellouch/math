import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.FiniteNode

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def guardedNodeEncoded (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ M : ℝ) (hδ : 0<δ)
    (t : FiniteNodeTape pred (1000*(Nat.card K)^2) (Nat.card K)) :
    Option (FiniteNodeMessage pred UB (1000*(Nat.card K)^2) (Nat.card K) t) := by
  letI : Finite V := Module.finite_of_finite K
  letI : Fintype V := Fintype.ofFinite _
  letI : Finite (Dual K V) := Module.finite_of_finite K
  letI : Fintype (Dual K V) := Fintype.ofFinite _
  letI : Finite (Dual K (Dual K V)) := Module.finite_of_finite K
  letI : Fintype (ℙ K (Dual K (Dual K V))) := Fintype.ofFinite _
  exact if hr : OriginalNodeReady A₀ UA B₀ UB δ τ then
    let hA := nonempty_of_positive_trim (A₀∩UA) A₀ hA₀ δ hδ hr.1
    let hB := nonempty_of_positive_trim (B₀∩UB) B₀ hB₀ δ hδ hr.2.1
    let hnA := reverseLength_universal_bound σ hσ hq hd (A₀∩UA) UA hA Finset.inter_subset_right
    let hnB := reverseLength_universal_bound σ hσ hq (show finrank K (Dual K V)≤5 by simpa using hd)
      (B₀∩UB) UB hB Finset.inter_subset_right
    finiteNodeEncoded pred (A₀∩UA) UA (B₀∩UB) UB (1000*(Nat.card K)^2)
      ⟨_,Nat.lt_succ_of_le hnA⟩ ⟨_,Nat.lt_succ_of_le hnB⟩ (Nat.card K)
      ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/(B₀∩UB).card)
      ((320/c+320)*(Nat.card K:ℝ)^5/(A₀∩UA).card) c M t
  else none

lemma guardedNode_encoder_law (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ M : ℝ) (hδ : 0<δ) :
    map (finiteNodeTapeLaw pred (1000*(Nat.card K)^2) (Nat.card K)) (fun t=>
      (guardedNodeEncoded pred σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ M hδ t).map
        (finiteNodeDecoded pred UB (1000*(Nat.card K)^2) (Nat.card K) t))=
      guardedNodeLaw pred σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ M hδ := by
  unfold guardedNodeEncoded guardedNodeLaw
  split_ifs
  · rfl
  · simp only [Option.map_none]
    exact map_const _ none

lemma guardedNode_encode_none (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ M : ℝ) (hδ : 0<δ)
    (hr : ¬OriginalNodeReady A₀ UA B₀ UB δ τ)
    (t : FiniteNodeTape pred (1000*(Nat.card K)^2) (Nat.card K)) :
    guardedNodeEncoded pred σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ M hδ t=none := by
  simp only [guardedNodeEncoded,hr,↓reduceDIte]
end SharpRamseyFive.ProjectiveIncidence

end OAI
