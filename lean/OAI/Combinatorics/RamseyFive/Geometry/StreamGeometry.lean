import Mathlib
import OAI.Combinatorics.RamseyFive.Streams.DependentPrivateStream
import OAI.Combinatorics.RamseyFive.Streams.PreparedStream

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking CoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype Ω] [Fintype κ] [Fintype α]
  {N n l : ℕ} {admissible : (Fin N→α)→Prop}
structure Geometric (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible) (M : ℝ) : Prop where
  incident : ∀z,0<S.law z→TupleIncident (S.tuple z)
  consistent : ∀z,0<S.law z→TupleConsistent (S.tuple z)
  occupancy : ∀z,0<S.law z→∀W : Submodule K (Dual K V),
    (∑i,if InRectangle W (S.tuple z i).1.rep (S.tuple z i).2.rep then (1:ℝ) else 0)≤M
omit [FiniteDimensional K V] in
lemma Prepared.geometric {S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible}
    {ctx : Ω→κ} {J B M : ℝ} (P : Prepared S ctx J B M) : Geometric S M :=
  ⟨P.incident,P.consistent,P.occupancy⟩
namespace Geometric
variable {S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible} {M : ℝ}
omit [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma restrict (P : Geometric S M) (E : Finset Ω) (hE : 0<eventMass S.law E) :
    Geometric (S.restrict E hE) M := by
  have hp : ∀z,0<(S.restrict E hE).law z→0<S.law z :=
    fun z hz=>(conditionOn_positive S.law E hE z hz).2
  exact ⟨fun z hz=>P.incident z (hp z hz),fun z hz=>P.consistent z (hp z hz),
    fun z hz=>P.occupancy z (hp z hz)⟩
omit [FiniteDimensional K V] in
lemma reindex (P : Geometric S M) (e : Fin l↪o Fin n) : Geometric (S.reindex e) M :=
  ⟨fun z hz i=>P.incident z hz (e i),
    fun z hz i j hij=>P.consistent z hz (e i) (e j) (e.strictMono hij),
    fun z hz=>occupancy_reindex _ e e.injective M (P.occupancy z hz)⟩
omit [FiniteDimensional K V] in
lemma extract (P : Geometric S M) (hl : l≤n) (pos : Ω→Finset (Fin n)) :
    Geometric (S.extract hl pos) M := by
  have hsub (z : Ω) : ∃e : Fin l↪o Fin n,∀i,S.tuple z (e i)=(S.extract hl pos).tuple z i :=
    (mem_occurrences_iff _ _).mp (retainedTuple_occurs hl (S.tuple z) (pos z))
  constructor
  · intro z hz
    obtain ⟨e,he⟩:=hsub z
    intro i
    rw [←he i]
    exact P.incident z hz (e i)
  · intro z hz
    obtain ⟨e,he⟩:=hsub z
    intro i j hij
    rw [←he i,←he j]
    exact P.consistent z hz (e i) (e j) (e.strictMono hij)
  · intro z hz
    obtain ⟨e,he⟩:=hsub z
    have hh:=occupancy_reindex (S.tuple z) e e.injective M (P.occupancy z hz)
    simpa only [he] using hh
omit [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma augment (P : Geometric S M) (q : Ω→Law κ) : Geometric (S.augment q) M := by
  have hp : ∀z,0<(S.augment q).law z→0<S.law z.1 := by
    intro z hz
    change 0<S.law z.1*q z.1 z.2 at hz
    exact ((mul_pos_iff.mp hz).resolve_right (fun h=>(S.law.nonneg _).not_gt h.1)).1
  exact ⟨fun z hz=>P.incident z.1 (hp z hz),fun z hz=>P.consistent z.1 (hp z hz),
    fun z hz=>P.occupancy z.1 (hp z hz)⟩
omit [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma augmentSigma {Γ : Ω→Type} [∀z,Fintype (Γ z)] (P : Geometric S M) (q : ∀z,Law (Γ z)) :
    Geometric (S.augmentSigma q) M := by
  have hp : ∀z,0<(S.augmentSigma q).law z→0<S.law z.1 :=
    fun z hz=>(sigmaLaw_positive S.law q z hz).1
  exact ⟨fun z hz=>P.incident z.1 (hp z hz),fun z hz=>P.consistent z.1 (hp z hz),
    fun z hz=>P.occupancy z.1 (hp z hz)⟩
omit [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma swap (P : Geometric S M) :
    Geometric (S.changeOrientation swapFlag swapFlag.symm swapFlag.symm_apply_apply) M :=
  ⟨fun z hz=>reverseTuple_incident (P.incident z hz),
    fun z hz=>reverseTuple_consistent (P.consistent z hz),
    fun z hz=>occupancy_reverse _ M (P.occupancy z hz)⟩
end Geometric

structure CodedStream (N n : ℕ) (admissible : (Fin N→α)→Prop) (density Λ J M : ℝ) where
  sample : Type
  [finiteSample : Fintype sample]
  stream : SelectedStream (Ω:=sample) (β:=FlagPair K V) N n admissible
  code : Type
  [finiteCode : Fintype code]
  description : ContextDescription (κ:=code) stream.law stream.tuple Λ J
  density_bound : stream.density≤density
  geometric : Geometric stream M
attribute [instance] CodedStream.finiteSample CodedStream.finiteCode
end
end SharpRamseyFive.SelectedTuple

end OAI
