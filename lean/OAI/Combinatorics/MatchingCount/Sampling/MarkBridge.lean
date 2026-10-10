import Mathlib
import OAI.Combinatorics.MatchingCount.Probability.Marking
import OAI.Combinatorics.MatchingCount.Algorithm.RelabelWeights
import OAI.Combinatorics.MatchingCount.Sampling.RelabelMarking

namespace OAI

namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (BagPM (bags w K)) := Classical.decEq _
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    Fintype (BagPM (bags w K)) := Fintype.ofFinite _
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    Fintype (Marked w K) := Fintype.ofFinite _
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    Fintype (SourceMarked (fun x y=>(w x y:ℝ)) K) := Fintype.ofFinite _
lemma sourceEdgeEquiv_central (w : V → V → ℚ) (K : ℕ) (q : LogicalEdge V) :
    sourceEdgeEquiv w K (Enlargement.centralEdge (fun x y=>(w x y:ℝ)) K q)=centralEdge w K q :=
  sourceEdgeEquiv_real w K _
lemma probePortion_cast (w : V → V → ℚ) (K D : ℕ)
    (e : BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) :
    (probePortion w K D (sourceEdgeEquiv w K e):ℝ)=Enlargement.probePortion (fun x y=>(w x y:ℝ)) K D e := by
  classical
  have he : (∃ q,centralEdge w K q=sourceEdgeEquiv w K e) ↔
      ∃ q,Enlargement.centralEdge (fun x y=>(w x y:ℝ)) K q=e := by
    constructor
    · rintro ⟨q,hq⟩
      exact ⟨q,(sourceEdgeEquiv w K).injective ((sourceEdgeEquiv_central w K q).trans hq)⟩
    · rintro ⟨q,rfl⟩
      exact ⟨q,(sourceEdgeEquiv_central w K q).symm⟩
  simp only [probePortion,Enlargement.probePortion,he]
  split_ifs <;> push_cast <;> rfl
lemma portions_cast (w : V → V → ℚ) (K D : ℕ)
    (e : BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) (i : Fin 3) :
    (portions w K D (sourceEdgeEquiv w K e) i:ℝ)=sourcePortions (fun x y=>(w x y:ℝ)) K D e i := by
  fin_cases i
  · exact realPortion_cast w K e
  · change ((bagHeight w K (sourceEdgeEquiv w K e).color/D-probePortion w K D (sourceEdgeEquiv w K e):ℚ):ℝ)=_
    rw [Rat.cast_sub,Rat.cast_div,Rat.cast_natCast,probePortion_cast,sourceEdgeEquiv_color,bagHeight_cast]
    rfl
  · exact probePortion_cast w K D e
noncomputable def sourceMarkedEquiv (w : V → V → ℚ) (K : ℕ) :
    SourceMarked (fun x y=>(w x y:ℝ)) K ≃ Marked w K :=
  markedEquiv (inc:=BagEdge.Incident (bags:=sourceBags (fun x y=>(w x y:ℝ)) K))
    (j:=BagEdge.Incident (bags:=bags w K)) (sourceEdgeEquiv w K) (fun _ _=>Iff.rfl)
lemma portions_collapse (w : V → V → ℚ) (K D : ℕ) :
    Marking.collapse (fun e i=>(portions w K D e i:ℝ))=fun e=>(bagWeight w K D e:ℝ) := by
  funext e
  change (∑ i : Fin 3,(portions w K D e i:ℝ))=(bagWeight w K D e:ℝ)
  exact_mod_cast portions_sum w K D e
lemma markedLaw_eq (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 0<D)
    (a : Marked w K) :
    markedLaw w K D a=Marking.law BagEdge.Incident (fun e i=>(portions w K D e i:ℝ)) a := by
  have hc : ∀ e,Marking.collapse (fun e i=>(portions w K D e i:ℝ)) e≠0 := by
    intro e
    rw [portions_collapse]
    dsimp only
    exact_mod_cast (bagWeight_pos w hw K D hD e).ne'
  have h:=Marking.law_from_reveal BagEdge.Incident (fun e i=>(portions w K D e i:ℝ)) hc a
  rw [portions_collapse] at h
  convert h using 1
  simp only [markedLaw,Variation.sigmaLift,product,gibbs,matchingWeight,partition,Marking.conditional,
    portions_collapse,Rat.cast_div,partitionWeight]
  congr 3
  ext
  simp
lemma markedLaw_equiv (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 0<D)
    (a : SourceMarked (fun x y=>(w x y:ℝ)) K) :
    markedLaw w K D (sourceMarkedEquiv w K a)=sourceLaw (fun x y=>(w x y:ℝ)) K D a := by
  rw [markedLaw_eq w hw K D hD]
  change Marking.law BagEdge.Incident (fun e i=>(portions w K D e i:ℝ))
    (markedEquiv (inc:=BagEdge.Incident (bags:=sourceBags (fun x y=>(w x y:ℝ)) K))
    (j:=BagEdge.Incident (bags:=bags w K)) (sourceEdgeEquiv w K) (fun _ _=>Iff.rfl) a)=_
  rw [law_markedEquiv (inc:=BagEdge.Incident (bags:=sourceBags (fun x y=>(w x y:ℝ)) K))
    (j:=BagEdge.Incident (bags:=bags w K)) (sourceEdgeEquiv w K) (fun _ _=>Iff.rfl)]
  have hp : ((fun e i=>(portions w K D e i:ℝ)) ∘ sourceEdgeEquiv w K)=
        sourcePortions (fun x y=>(w x y:ℝ)) K D := by
    funext e i
    exact portions_cast w K D e i
  rw [hp]
  rfl
end MatchingFPRAS.RationalSource

end OAI
