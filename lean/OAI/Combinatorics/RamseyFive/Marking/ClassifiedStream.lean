import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.MarkedStreamExtraction
import OAI.Combinatorics.RamseyFive.Geometry.RectangleTransport
import OAI.Combinatorics.RamseyFive.Marking.DomainTransport

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy SelectedTuple CoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n l : ℕ} {admissible : (Fin N→α)→Prop}
local instance csFinDE (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance csPDE : DecidableEq (ℙ K V) := Classical.decEq _
local instance csDDE : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _

def DomainClass (width : ℝ) (D : Finset (FlagPair K V)) : SlotClass→Prop
  | .inl b=>∃u,Real.log (Nat.card K)≤u ∧ u≤4*Real.log (Nat.card K) ∧
      ForwardCaps D u ∧ BandCondition (Real.log (Nat.card K)) width u b
  | .inr (.inl b)=>∃u,Real.log (Nat.card K)≤u ∧ u≤4*Real.log (Nat.card K) ∧
      ReverseCaps D u ∧ BandCondition (Real.log (Nat.card K)) width u b
  | .inr (.inr (r,s))=>5<r.val+s.val ∧ HighCaps D r.val s.val

omit [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] in
lemma classValid_domainClass (hd : finrank K V=5) (width : ℝ)
    (m : UnionTranscript (Fin n) (FlagPair K V)) (i : Fin n) (a : SlotClass)
    (hne : (markingDomain m i).Nonempty) (hc : classValid width m i a) :
    DomainClass width (markingDomain m i) a := by
  rcases a with b|b|⟨r,s⟩
  · exact hc
  · exact hc
  · obtain ⟨hr,hs,hp,hp',hgt⟩:=hc
    refine ⟨hgt,?_⟩
    have hh:=marking_highCaps hd m i hne hp hp'
    simpa only [hr,hs] using hh

lemma classStream_domainClass (hd : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (hl : l≤n) (a : SlotClass)
    (hE : 0<eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hd width hw l a)))
    (hinc : ∀z,0<S.law z→TupleIncident (S.tuple z))
    (hcons : ∀z,0<S.law z→TupleConsistent (S.tuple z)) :
    let T:=classStream hd width hw S ctx hl a hE
    ∀c,0 < map T.law (markedContext ctx S.tuple) c→∀i,
      DomainClass width (classDomain hd width hw hl a c i) a := by
  intro T c hc i
  obtain ⟨z,hz,rfl⟩:=map_positive T.law (markedContext ctx S.tuple) c hc
  have hmem:=classStream_contains hd width hw S ctx hl a hE hinc hcons z hz i
  exact classValid_domainClass hd width _ _ a ⟨T.tuple z i,hmem⟩
    (classStream_valid hd width hw S ctx hl a hE hinc hcons z hz i)

omit [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype κ] in
lemma classDomain_cap (hd : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (hl : l≤n) (a : SlotClass) (c : κ×UnionTranscript (Fin n) (FlagPair K V)) (i : Fin l) :
    ((classDomain hd width hw hl a c i).card:ℝ)≤153*(Nat.card K:ℝ)^4 :=
  markingDomain_card hd _ _
omit [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype κ] in
lemma classDomain_log_cap (hd : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (hl : l≤n) (a : SlotClass) (c : κ×UnionTranscript (Fin n) (FlagPair K V)) (i : Fin l) :
    Real.log (classDomain hd width hw hl a c i).card≤Real.log (153*(Nat.card K:ℝ)^4) := by
  by_cases hz : (classDomain hd width hw hl a c i).card=0
  · rw [hz,Nat.cast_zero,Real.log_zero]
    apply Real.log_nonneg
    have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α:=K)).le
    nlinarith [sq_nonneg ((Nat.card K:ℝ)^2-1),sq_nonneg ((Nat.card K:ℝ)-1)]
  · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz)
      (classDomain_cap hd width hw hl a c i)

lemma classStream_occupancy (hd : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (hl : l≤n) (a : SlotClass)
    (hE : 0<eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hd width hw l a))) (M : ℝ)
    (hocc : ∀z,0<S.law z→∀W : Submodule K (Dual K V),
      (∑i,if InRectangle W (S.tuple z i).1.rep (S.tuple z i).2.rep then (1:ℝ) else 0)≤M) :
    let T:=classStream hd width hw S ctx hl a hE
    ∀z,0<T.law z→∀W : Submodule K (Dual K V),
      (∑i,if InRectangle W (T.tuple z i).1.rep (T.tuple z i).2.rep then (1:ℝ) else 0)≤M := by
  intro T z hz W
  have hp:=conditionOn_positive S.law
    (eventPreimage (markedContext ctx S.tuple) (markedEvent hd width hw l a)) hE z hz
  exact occupancy_reindex (S.tuple z)
    (retainedIndices hl (markedPositions hd width hw ctx S.tuple a z))
    (retainedIndices hl (markedPositions hd width hw ctx S.tuple a z)).injective
    M (hocc z hp.2) W

end
end SharpRamseyFive.Marking

end OAI
