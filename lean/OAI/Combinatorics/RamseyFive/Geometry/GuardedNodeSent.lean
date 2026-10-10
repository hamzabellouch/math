import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.GuardedNodeEncoder
import OAI.Combinatorics.RamseyFive.Trees.FiniteNodeSent

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

lemma guardedNode_sent_valid (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ M : ℝ) (hδ : 0<δ)
    (t : FiniteNodeTape pred (1000*(Nat.card K)^2) (Nat.card K))
    (m : FiniteNodeMessage pred UB (1000*(Nat.card K)^2) (Nat.card K) t)
    (hm : guardedNodeEncoded pred σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ M hδ t=some m) :
    OriginalNodeReady A₀ UA B₀ UB δ τ ∧
    ValidCap (B₀∩UB) UB ((320/c+320)*(Nat.card K:ℝ)^5/(A₀∩UA).card)
      (UB∩(finiteNodeDecoded pred UB (1000*(Nat.card K)^2) (Nat.card K) t m).1) ∧
    ValidCap (A₀∩UA) UA ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/(B₀∩UB).card)
      (UA∩(finiteNodeDecoded pred UB (1000*(Nat.card K)^2) (Nat.card K) t m).2) := by
  unfold guardedNodeEncoded at hm
  split_ifs at hm with hr
  exact ⟨hr,finiteNode_sent_valid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm⟩

lemma guardedNode_original_capture (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ M : ℝ) (hδ : 0<δ)
    (t : FiniteNodeTape pred (1000*(Nat.card K)^2) (Nat.card K))
    (m : FiniteNodeMessage pred UB (1000*(Nat.card K)^2) (Nat.card K) t)
    (hm : guardedNodeEncoded pred σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ M hδ t=some m) :
    (9/10:ℝ)*δ*A₀.card≤(A₀∩(UA∩(finiteNodeDecoded pred UB (1000*(Nat.card K)^2) (Nat.card K) t m).2)).card ∧
    (9/10:ℝ)*δ*B₀.card≤(B₀∩(UB∩(finiteNodeDecoded pred UB (1000*(Nat.card K)^2) (Nat.card K) t m).1)).card := by
  obtain ⟨hr,hB,hA⟩ := guardedNode_sent_valid pred σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ M hδ t m hm
  have ha := hA.2.2
  have hb := hB.2.2
  simp only [Finset.inter_assoc,Finset.inter_left_idem] at ha hb
  constructor
  · nlinarith [hr.1]
  · nlinarith [hr.2.1]
end

open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

abbrev OrientedNodeTape
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V)))) (H : ℕ) (q : ℝ) :=
  FiniteNodeTape f H q × FiniteNodeTape r H q
noncomputable instance orientedNodeTapeFintype
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V)))) (H : ℕ) (q : ℝ) :
    Fintype (OrientedNodeTape f r H q) := by
  exact @instFintypeProd (FiniteNodeTape f H q) (FiniteNodeTape r H q) inferInstance inferInstance
abbrev OrientedNodeMessage
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (UA : Finset (ℙ K V)) (UB : Finset (ℙ K (Dual K V))) (H : ℕ) (q : ℝ)
    (t : OrientedNodeTape f r H q) :=
  FiniteNodeMessage f UB H q t.1 ⊕ FiniteNodeMessage r (UA.map bidualPoint.toEmbedding) H q t.2
noncomputable def orientedNodeTapeLaw
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V)))) (H : ℕ) (q : ℝ) :
    Law (OrientedNodeTape f r H q) :=
  adaptiveLaw (finiteNodeTapeLaw f H q) (fun _=>finiteNodeTapeLaw r H q)
noncomputable def reverseNodePair
    (out : Finset (ℙ K (Dual K (Dual K V)))×Finset (ℙ K (Dual K V))) :
    Finset (ℙ K (Dual K V))×Finset (ℙ K V) :=
  (out.2,out.1.map bidualPoint.symm.toEmbedding)
noncomputable def orientedNodeDecoded
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (UA : Finset (ℙ K V)) (UB : Finset (ℙ K (Dual K V))) (H : ℕ) (q : ℝ)
    (t : OrientedNodeTape f r H q) (m : OrientedNodeMessage f r UA UB H q t) :
    Finset (ℙ K (Dual K V))×Finset (ℙ K V) := match m with
  | .inl m=>finiteNodeDecoded f UB H q t.1 m
  | .inr m=>reverseNodePair (finiteNodeDecoded r (UA.map bidualPoint.toEmbedding) H q t.2 m)
noncomputable def orientedNodeCost
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (UA : Finset (ℙ K V)) (UB : Finset (ℙ K (Dual K V))) (H : ℕ) (q : ℝ)
    (t : OrientedNodeTape f r H q) (m : OrientedNodeMessage f r UA UB H q t) : ℝ :=
  Real.log 2 + match m with
    | .inl m=>finiteNodeCost f UB H q t.1 m
    | .inr m=>finiteNodeCost r (UA.map bidualPoint.toEmbedding) H q t.2 m

noncomputable def orientedGuardedNodeEncoded
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ P : ℝ) (hδ : 0<δ)
    (t : OrientedNodeTape f r (1000*(Nat.card K)^2) (Nat.card K)) :
    Option (OrientedNodeMessage f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t) :=
  if (A₀∩UA).card≤(B₀∩UB).card then
    (guardedNodeEncoded f σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ
      (((A₀∩UA).card:ℝ)*Real.exp (10*P)) hδ t.1).map Sum.inl
  else
    (guardedNodeEncoded r σ hσ hq (by simpa using hd) B₀ UB
      (A₀.map bidualPoint.toEmbedding) (UA.map bidualPoint.toEmbedding) hB₀
      hA₀.map c δ τ (((B₀∩UB).card:ℝ)*Real.exp (10*P)) hδ t.2).map Sum.inr

lemma orientedGuardedNode_law
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ P : ℝ) (hδ : 0<δ) :
    map (orientedNodeTapeLaw f r (1000*(Nat.card K)^2) (Nat.card K)) (fun t=>
      (orientedGuardedNodeEncoded f r σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ P hδ t).map
        (orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t))=
    if (A₀∩UA).card≤(B₀∩UB).card then
      guardedNodeLaw f σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ (((A₀∩UA).card:ℝ)*Real.exp (10*P)) hδ
    else map
      (guardedNodeLaw r σ hσ hq (by simpa using hd) B₀ UB
        (A₀.map bidualPoint.toEmbedding) (UA.map bidualPoint.toEmbedding) hB₀
        hA₀.map c δ τ (((B₀∩UB).card:ℝ)*Real.exp (10*P)) hδ)
      (Option.map reverseNodePair) := by
  unfold orientedGuardedNodeEncoded
  split_ifs with h
  · simp only [Option.map_map,Function.comp_def,orientedNodeDecoded]
    exact (map_independent_left
      (finiteNodeTapeLaw f (1000*(Nat.card K)^2) (Nat.card K))
      (finiteNodeTapeLaw r (1000*(Nat.card K)^2) (Nat.card K)) _).trans
      (guardedNode_encoder_law f σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ
        (((A₀∩UA).card:ℝ)*Real.exp (10*P)) hδ)
  · simp only [Option.map_map,Function.comp_def,orientedNodeDecoded]
    have hh := congrArg (fun p=>map p (Option.map reverseNodePair))
      (guardedNode_encoder_law r σ hσ hq (by simpa using hd) B₀ UB
        (A₀.map bidualPoint.toEmbedding) (UA.map bidualPoint.toEmbedding) hB₀
        hA₀.map c δ τ (((B₀∩UB).card:ℝ)*Real.exp (10*P)) hδ)
    rw [map_comp] at hh
    simp only [Option.map_map,Function.comp_def] at hh
    exact (map_independent_right
      (finiteNodeTapeLaw f (1000*(Nat.card K)^2) (Nat.card K))
      (finiteNodeTapeLaw r (1000*(Nat.card K)^2) (Nat.card K)) _).trans hh

end SharpRamseyFive.ProjectiveIncidence

end OAI
