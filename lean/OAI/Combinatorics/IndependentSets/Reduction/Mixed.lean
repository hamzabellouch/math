import Mathlib
import OAI.Combinatorics.IndependentSets.Geometry.Witness
import OAI.Combinatorics.IndependentSets.Reduction.ThresholdDecidable

namespace OAI

namespace LargeIndependentSets.ExplicitEnum

def mixed {A B : Type*} [DecidableEq A] [DecidableEq B]
    (ea : ExplicitEnum A) (eb : ExplicitEnum B) (n i : ℕ) : ExplicitEnum (MixedTuple A B n i) :=
  subtype (pi (fin n) (fun _ => sum eb ea)) (fun x => ∀ h, (x h).isLeft = decide (h.val < i))

def question {U V : Type*} [DecidableEq U] [DecidableEq V]
    (eu : ExplicitEnum U) (ev : ExplicitEnum V) (n : ℕ) : ExplicitEnum (LayerQuestion U V n) :=
  sigma (fin (n+1)) (fun i => mixed eu ev n i.val)

def grid {U V L R : Type} [Fintype L] [Fintype R]
    [DecidableEq U] [DecidableEq V] [DecidableEq L] [DecidableEq R]
    (eu : ExplicitEnum U) (ev : ExplicitEnum V) (el : ExplicitEnum L) (er : ExplicitEnum R)
    (n D : ℕ) [NeZero D] :
    ExplicitEnum (GridLocation (LayerAnswer L R (U:=U) (V:=V) (n:=n)) D) :=
  sigma (question eu ev n) (fun q => pi (mixed el er n q.1.val) (fun _ => zmod D))

def equiv {α : Type*} [DecidableEq α] (e : ExplicitEnum α) : Fin e.values.length ≃ α :=
  enumerationEquiv e.values e.nodup e.covers

lemma length_eq_card {α : Type*} [DecidableEq α] [Fintype α] (e : ExplicitEnum α) :
    e.values.length = Fintype.card α := by
  simpa using Fintype.card_congr e.equiv

end LargeIndependentSets.ExplicitEnum

namespace LargeIndependentSets
open BooleanJunta PhaseTest
open scoped BigOperators ENNReal

def rotationCode {k : ℕ} (x : Cube k) : Fin (2^k) := ⟨gridIndex x,gridIndex_lt x⟩

def sampleLocationCode {U V L R C : Type} [Fintype L] [Fintype R]
    {n s m k : ℕ} (lc : LabelCoverData U V L R C) (chain : Fin n → C) (hs : 0<s)
    (o : SamplerOutcome L R n s m k) :
    GridLocation (LayerAnswer L R (U:=U) (V:=V) (n:=n)) (m*2^k) :=
  let b : o.1.val := ⟨o.1.val.min' (supported_nonempty hs o.1),
    o.1.val.min'_mem (supported_nonempty hs o.1)⟩
  ⟨occurrenceQuestion lc chain b.val,
    fun a => ∑ j : o.1.val, ((o.2.1 j).val *
      (rotationCode (o.2.2 ⟨j,chainComposite lc chain b.val.val j.val.val
        (Finset.min'_le _ _ j.property) a⟩)).val : ℕ)⟩

lemma sampleLocationCode_eq {U V L R C : Type} [Fintype L] [Fintype R]
    {n s m k : ℕ} (lc : LabelCoverData U V L R C) (chain : Fin n → C) (hs : 0<s)
    (o : SamplerOutcome L R n s m k) :
    sampleLocationCode lc chain hs o = sampleLocation lc chain hs o := rfl

instance layeredImposedDecidable {U V L R C : Type}
    [Fintype U] [Fintype V] [Fintype L] [Fintype R] [Fintype C]
    [DecidableEq U] [DecidableEq V] [DecidableEq L] [DecidableEq R]
    (lc : LabelCoverData U V L R C) (n : ℕ) (q q' : LayerQuestion U V n)
    (π : LayerAnswer L R q → LayerAnswer L R q') :
    Decidable ((layeredSystem lc n).imposed q q' π) :=
  LayerImposed.imposed_decidable lc n q q' π

namespace SamplerParameters

def locationCode (p : SamplerParameters) {U V L R C : Type} [Fintype L] [Fintype R]
    (lc : LabelCoverData U V L R C) (v : p.Vertices L R C) :=
  sampleLocationCode lc v.1 p.hs v.2.1

lemma locationCode_eq (p : SamplerParameters) {U V L R C : Type} [Fintype L] [Fintype R]
    (lc : LabelCoverData U V L R C) (v : p.Vertices L R C) :
    p.locationCode lc v = p.location lc v := rfl

def chainEnumeration (n : ℕ) {C O : Type} [DecidableEq C] [DecidableEq O]
    (ec : ExplicitEnum C) (eo : ExplicitEnum O) :
    ExplicitEnum ((Fin n → C) × O) :=
  ExplicitEnum.prod (ExplicitEnum.pi (ExplicitEnum.fin n) (fun _ => ec)) eo

def graphAdjDecidable (p : SamplerParameters) {U V L R C : Type}
    [Fintype U] [Fintype V] [Fintype L] [Fintype R] [Fintype C]
    [DecidableEq U] [DecidableEq V] [DecidableEq L] [DecidableEq R]
    [DecidableEq (p.Vertices L R C)]
    (lc : LabelCoverData U V L R C) {N : ℕ}
    (eg : Fin N ≃ GridLocation (LayerAnswer L R (U:=U) (V:=V) (n:=p.n)) (p.m*2^p.k))
    (u v : p.Vertices L R C) : Decidable ((p.graph lc).Adj u v) := by
  letI := ShortestPaths.thresholdDecidable (layeredSystem lc p.n) eg
    (p.locationCode lc u) (gridAntipode (p.locationCode lc v))
  exact inferInstanceAs (Decidable (u ≠ v ∧
    pathDistance (layeredSystem lc p.n).linkLength (p.locationCode lc u)
      (gridAntipode (p.locationCode lc v)) ≤ ENNReal.ofReal (1/8)))

def cliqueDecidable (p : SamplerParameters) {U V L R C : Type}
    [Fintype U] [Fintype V] [Fintype L] [Fintype R] [Fintype C]
    [DecidableEq U] [DecidableEq V] [DecidableEq L] [DecidableEq R]
    (lc : LabelCoverData U V L R C) {N : ℕ}
    (eg : Fin N ≃ GridLocation (LayerAnswer L R (U:=U) (V:=V) (n:=p.n)) (p.m*2^p.k)) :
    Decidable (p.CliqueTest lc) := by
  letI (i : Fin N) := ShortestPaths.thresholdDecidable (layeredSystem lc p.n) eg
    (eg i) (gridAntipode (eg i))
  have he : p.CliqueTest lc ↔ ∃ i : Fin N,
      pathDistance (layeredSystem lc p.n).linkLength (eg i) (gridAntipode (eg i)) ≤
        ENNReal.ofReal (1/8) := by
    constructor
    · rintro ⟨x,hx⟩; exact ⟨eg.symm x,by simpa using hx⟩
    · rintro ⟨i,hi⟩; exact ⟨eg i,hi⟩
  exact decidable_of_iff _ he.symm

def enumeratedGraph (p : SamplerParameters) {U V L R C : Type}
    [Fintype U] [Fintype V] [Fintype L] [Fintype R] [Fintype C]
    [DecidableEq U] [DecidableEq V] [DecidableEq L] [DecidableEq R]
    [DecidableEq (p.Vertices L R C)]
    (lc : LabelCoverData U V L R C) {N t : ℕ} (ht : 0<t)
    (eg : Fin N ≃ GridLocation (LayerAnswer L R (U:=U) (V:=V) (n:=p.n)) (p.m*2^p.k))
    (ev : Fin t ≃ p.Vertices L R C) : Graph where
  vertices := t
  nonempty := ht
  adj i j := @decide _ (p.graphAdjDecidable lc eg (ev i) (ev j))
  symm i j := by
    simp only [decide_eq_decide]
    exact (p.graph lc).adj_comm _ _
  loopless i := by simp

def enumeratedOutput (p : SamplerParameters) (q : ℕ) (hq : 0<q)
    {U V L R C : Type}
    [Fintype U] [Fintype V] [Fintype L] [Fintype R] [Fintype C]
    [DecidableEq U] [DecidableEq V] [DecidableEq L] [DecidableEq R]
    [DecidableEq (p.Vertices L R C)]
    (lc : LabelCoverData U V L R C) {N t : ℕ} (ht : 0<t)
    (eg : Fin N ≃ GridLocation (LayerAnswer L R (U:=U) (V:=V) (n:=p.n)) (p.m*2^p.k))
    (ev : Fin t ≃ p.Vertices L R C) : Graph := by
  letI := p.cliqueDecidable lc eg
  exact if p.CliqueTest lc then Graph.clique q hq else p.enumeratedGraph lc ht eg ev

end SamplerParameters
end LargeIndependentSets

namespace LargeIndependentSets.Graph

structure Renaming (G H : Graph) where
  equiv : Fin G.vertices ≃ Fin H.vertices
  adj_eq : ∀ i j, G.adj i j = H.adj (equiv i) (equiv j)

namespace Renaming
variable {G H : Graph}

def symm (e : Renaming G H) : Renaming H G where
  equiv := e.equiv.symm
  adj_eq i j := by simpa using (e.adj_eq (e.equiv.symm i) (e.equiv.symm j)).symm

lemma vertices_eq (e : Renaming G H) : G.vertices = H.vertices := by
  simpa using Fintype.card_congr e.equiv

lemma independent (e : Renaming G H) (A : Finset (Fin G.vertices)) (hA : G.Independent A) :
    H.Independent (A.image e.equiv) := by
  intro u hu v hv huv
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
  rw [← e.adj_eq]
  exact hA i hi j hj (fun h => huv (congrArg e.equiv h))

lemma independent_card_le (G : Graph) (A : Finset (Fin G.vertices)) (hA : G.Independent A) :
    A.card ≤ G.independenceNumber := by
  unfold Graph.independenceNumber
  exact Finset.le_sup (f:=Finset.card) (Finset.mem_filter.mpr ⟨by simp,hA⟩)

lemma alpha_le (e : Renaming G H) : G.independenceNumber ≤ H.independenceNumber := by
  obtain ⟨A,hA,he⟩ := G.exists_max_independent
  rw [he,← Finset.card_image_of_injective A e.equiv.injective]
  exact independent_card_le H _ (e.independent A hA)

lemma alpha_eq (e : Renaming G H) : G.independenceNumber = H.independenceNumber :=
  le_antisymm e.alpha_le e.symm.alpha_le

lemma colorable (e : Renaming G H) (h : G.ThreeColorable) : H.ThreeColorable := by
  obtain ⟨c,hc⟩ := h
  refine ⟨fun v => c (e.equiv.symm v),?_⟩
  intro i j hij
  apply hc
  simpa only [e.adj_eq,Equiv.apply_symm_apply] using hij

lemma strict_density {δ : ℝ} (e : Renaming G H)
    (h : (G.independenceNumber:ℝ) < δ*G.vertices) :
    (H.independenceNumber:ℝ) < δ*H.vertices := by
  simpa only [e.alpha_eq,e.vertices_eq] using h

end Renaming
end LargeIndependentSets.Graph

end OAI
