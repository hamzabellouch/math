import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.ClassifiedStream
import OAI.Combinatorics.RamseyFive.Entropy.DescriptionClean

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
local instance cpFinDE (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def classPrepared (hd : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (hl : l≤n) (a : SlotClass)
    (hE : 0<eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hd width hw l a)))
    (hm : (1:ℝ)/39≤eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hd width hw l a)))
    (hinc : ∀z,0<S.law z→TupleIncident (S.tuple z))
    (hcons : ∀z,0<S.law z→TupleConsistent (S.tuple z))
    (D : κ→Fin n→Finset (FlagPair K V)) (cap B L M : ℝ) (hcap : 1≤cap)
    (hD : ∀c i,((D c i).card:ℝ)≤cap)
    (hsupp : ∀z,0<S.law z→∀i,S.tuple z i∈D (ctx z) i)
    (hΔ : 0≤Real.log cap-Real.log (153*(Nat.card K:ℝ)^4))
    (hent : (n:ℝ)*Real.log (153*(Nat.card K:ℝ)^4)-entropy (map S.law S.tuple)≤B)
    (hctx : entropy (map S.law ctx)≤L)
    (hocc : ∀z,0<S.law z→∀W : Submodule K (Dual K V),
      (∑i,if InRectangle W (S.tuple z i).1.rep (S.tuple z i).2.rep then (1:ℝ) else 0)≤M) :
    Prepared (classStream hd width hw S ctx hl a hE) (markedContext ctx S.tuple)
      (Real.log (153*(Nat.card K:ℝ)^4))
      (39*(B+L+(n:ℝ)*Real.log 800+
        expensiveBound K V*(Real.log cap-Real.log (153*(Nat.card K:ℝ)^4)))) M where
  domain:=classDomain hd width hw hl a
  contains:=classStream_contains hd width hw S ctx hl a hE hinc hcons
  cap:=classDomain_log_cap hd width hw hl a
  deficit:=actual_marked_deficit hd width hw S ctx hl a hE hm hinc hcons D cap B L
    hcap hD hsupp hΔ hent hctx
  incident z hz:=(classStream_consistent hd width hw S ctx hl a hE hinc hcons z hz).1
  consistent z hz:=(classStream_consistent hd width hw S ctx hl a hE hinc hcons z hz).2
  occupancy:=classStream_occupancy hd width hw S ctx hl a hE M hocc
end
end SharpRamseyFive.Marking

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking CoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
local instance cmFinDE (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {K V α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype α]

structure ClassifiedPrepared (N n : ℕ) (admissible : (Fin N→α)→Prop)
    (d J B M width : ℝ) where
  sample : Type
  [finiteSample : Fintype sample]
  context : Type
  [finiteContext : Fintype context]
  stream : SelectedStream (Ω:=sample) (β:=FlagPair K V) N n admissible
  ctx : sample→context
  prepared : Prepared stream ctx J B M
  slotClass : SlotClass
  classified : ∀c,0 < map stream.law ctx c→∀i,DomainClass width (prepared.domain c i) slotClass
  density_bound : stream.density≤d
attribute [instance] ClassifiedPrepared.finiteSample ClassifiedPrepared.finiteContext

theorem classify_coded [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
    [Nonempty (ℙ K (Dual K (Dual K V)))]
    {N n m : ℕ} {adm : (Fin N→α)→Prop} {d Λ Δ M B width : ℝ}
    (hd : finrank K V=5) (hw : 0≤width) (hΔ : 0≤Δ)
    (S : CodedStream (K:=K) (V:=V) N n adm d Λ (Real.log (153*(Nat.card K:ℝ)^4)+Δ) M)
    (hm : m≤n) (hsize : 39*(m:ℝ)+expensiveBound K V≤n)
    (hent : n*Real.log (153*(Nat.card K:ℝ)^4)≤entropy (map S.stream.law S.stream.tuple))
    (hB : 39*(Λ+n*Real.log 800+expensiveBound K V*Δ)≤B) :
    Nonempty (ClassifiedPrepared (K:=K) (V:=V) N m adm (39*d)
      (Real.log (153*(Nat.card K:ℝ)^4)) B M width) := by
  let ctx:=S.description.context
  obtain ⟨a,ha⟩:=actual_marked_class hd S.stream ctx S.geometric.consistent width hw m hsize
  have hE : 0<eventMass S.stream.law (eventPreimage (markedContext ctx S.stream.tuple)
      (markedEvent hd width hw m a)) := lt_of_lt_of_le (by norm_num) ha
  have hcheap : 0≤Real.log (153*(Nat.card K:ℝ)^4) := by
    apply Real.log_nonneg
    have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α:=K)).le
    have hh:=one_le_pow₀ (n:=4) hq
    linarith
  let P:=classPrepared hd width hw S.stream ctx hm a hE ha
    S.geometric.incident S.geometric.consistent S.description.cleanDomain
    (Real.exp (Real.log (153*(Nat.card K:ℝ)^4)+Δ)) 0 Λ M
    (Real.one_le_exp_iff.mpr (add_nonneg hcheap hΔ)) S.description.clean_cap
    S.description.clean_contains (by simpa only [Real.log_exp,add_sub_cancel_left] using hΔ)
    (sub_nonpos.mpr hent) S.description.entropy_bound S.geometric.occupancy
  have hBP : 39*(0+Λ+n*Real.log 800+expensiveBound K V*
      (Real.log (Real.exp (Real.log (153*(Nat.card K:ℝ)^4)+Δ))-Real.log (153*(Nat.card K:ℝ)^4)))≤B := by
    simpa only [zero_add,Real.log_exp,add_sub_cancel_left] using hB
  refine ⟨{
    sample := S.sample
    context := (S.code × UnionTranscript (Fin n) (FlagPair K V))
    stream := classStream hd width hw S.stream ctx hm a hE
    ctx := markedContext ctx S.stream.tuple
    prepared := P.mono hBP
    slotClass := a
    classified := ?_
    density_bound := ?_ }⟩
  · exact classStream_domainClass hd width hw S.stream ctx hm a hE
      S.geometric.incident S.geometric.consistent
  · exact (classStream_density hd width hw S.stream ctx hm a hE ha).trans
      (mul_le_mul_of_nonneg_left S.density_bound (by norm_num))
end
end SharpRamseyFive.SelectedTuple

end OAI
