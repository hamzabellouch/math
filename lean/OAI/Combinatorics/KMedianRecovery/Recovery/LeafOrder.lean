import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Coupled
import OAI.Combinatorics.KMedianRecovery.Recovery.LengthSearch

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
instance labelLinearOrder {V : Type*} [LinearOrder V] : LinearOrder (Label V) :=
  inferInstanceAs (LinearOrder (V ⊕ₗ (ℕ ×ₗ (V ×ₗ ℚ))))
end MetricKMedianRecovery.RationalLeaves

namespace MetricKMedianRecovery.CanonicalSensitiveEndpoint
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing CanonicalLengthView RationalLeaves
variable {V : Type*} [LinearOrder V] {d : ℕ}

def run (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (Q : Finset (Label V)) (v lam b : ℚ) (q n k key precision : ℕ)
    (H : List (Label V)) (T U : List (List (Label V))) (J : Plan (Label V)) :
    CanonicalLengthSearch.Result (Label V) :=
  let C := J.common H
  let i := parent J.root
  let A := J.small T U
  let Z := J.large T U
  let R := Q∪C.toFinset
  if ((after (insert (leaf key i 0) R) A)∩F.image original).card=k then
    .success 0 A
  else
    CanonicalLengthSearch.run (F.image original) R (leaf key i)
      (fun s=>FiniteLabelContinuation.continuation (fun j=>original (loc j)) (rows distance)
        (F.image original) v lam (q+1) n (insert (leaf key i s) R)) A Z b k precision

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

lemma run_spec (loc : Fin d → V) (distance : V → Fin d → ℚ)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j))
    (F : Finset V) (B Q : Finset (Label V)) (v lam b : ℚ) (eta : ℝ)
    (q n k key precision : ℕ) (H : List (Label V)) (T U : List (List (Label V))) (J : Plan (Label V))
    (hQ : Q⊆F.image original∪B) (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hb : 0<b)
    (h : EndpointSpec loc F B Q v lam eta q n k key b H T U J) :
    (run loc distance F Q v lam b q n k key precision H T U J).Spec
      (F.image original) (Q∪(J.common H).toFinset) (leaf key (parent J.root))
      (fun s W=>Runs (fun j=>original (loc j)) (F.image original) (insert (leaf key (parent J.root) s) B)
        (insert (leaf key (parent J.root) s) (Q∪(J.common H).toFinset)) v lam (q+1) n W)
      b k precision := by
  obtain ⟨hC,hA,hZ,hs⟩ := h
  dsimp only [run]
  split
  · rename_i hk
    exact ⟨le_rfl,hb.le,hA,hk⟩
  · rename_i hk
    apply CanonicalLengthSearch.run_spec _ _ _ _ _ _ _ _ _ _ hb hA hZ _ (hs.resolve_left hk)
    intro s _ _
    apply FiniteLabelContinuation.continuation_spec _ _ (rows_spec loc distance hmetric) _ _ _
      v lam hv hv1 (q+1) n
    exact Finset.insert_subset (Finset.mem_union_right _ (Finset.mem_insert_self _ _))
      ((Finset.union_subset hQ hC.1.1.opened_subset).trans
        (Finset.union_subset_union_right (Finset.subset_insert _ _)))

end MetricKMedianRecovery.CanonicalSensitiveEndpoint

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [DecidableEq V] {d : ℕ}

inductive Correction (V : Type*) where
  | identity
  | shorten (key : ℕ) (i : V) (l u : ℚ)

def Correction.apply : Correction V → Label V → Label V
  | .identity => id
  | .shorten key i l u => RationalLeaves.shorten key i l u

def Correction.error : Correction V → ℚ
  | .identity => 0
  | .shorten _ _ l u => u-l

structure State (V : Type*) where
  B : Finset (Label V)
  P : List (List (Label V))
  correction : Correction V
  lam : ℚ
  lam' : ℚ
  T : List (List (Label V))
  U : List (List (Label V))

def State.mapPrefix (s : State V) := s.P.map (List.map s.correction.apply)
def State.mapFree (s : State V) := s.B.image s.correction.apply

def State.a (F : Finset V) (s : State V) :=
  ((after (after ∅ s.mapPrefix) s.T)∩F.image original).card

def State.b (F : Finset V) (s : State V) :=
  ((after (after ∅ s.P) s.U)∩F.image original).card

structure Output (V : Type*) where
  B : Finset (Label V)
  lam : ℚ
  P : List (List (Label V))

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

structure Certified (loc : Fin d → V) (F : Finset V) (v eta lo hi : ℝ)
    (q n k : ℕ) (s : State V) : Prop where
  before : Before (3*q) s.B
  before_map : Before (3*q) s.mapFree
  disjoint : Disjoint (F.image original) s.B
  low : lo≤(s.lam:ℝ)
  high : (s.lam':ℝ)≤hi
  price : (s.lam:ℝ)≤(s.lam':ℝ)
  eps_nonneg : (0:ℝ)≤ s.correction.error
  error : (s.lam':ℝ)-s.lam+(d:ℝ)*((1-3*v)*(s.correction.error:ℝ))≤(d:ℝ)*eta
  inj : Function.Injective s.correction.apply
  fixed : ∀ i∈F.image original,s.correction.apply i=i
  shrink : ∀ j,∀ x∈F.image original∪s.B,
    dist (original (loc j)) (s.correction.apply x)≤dist (original (loc j)) x
  loss : ∀ j,∀ x∈F.image original∪s.B,
    dist (original (loc j)) x≤dist (original (loc j)) (s.correction.apply x)+s.correction.error
  old_prefix : PrefixData (fun j=>original (loc j)) (F.image original) s.B v s.lam eta q s.P
  new_prefix : PrefixData (fun j=>original (loc j)) (F.image original) s.mapFree v s.lam' eta q s.mapPrefix
  sandwich : Sandwich k (s.a F) (s.b F)
  new_tail : Runs (fun j=>original (loc j)) (F.image original) s.mapFree (after ∅ s.mapPrefix) v s.lam' q n s.T
  old_tail : Runs (fun j=>original (loc j)) (F.image original) s.B (after ∅ s.P) v s.lam q n s.U

noncomputable def Certified.coupled {loc : Fin d → V} {F : Finset V} {v eta lo hi : ℝ}
    {q n k : ℕ} {s : State V} (h : Certified loc F v eta lo hi q n k s) :
    Coupled (fun j=>original (loc j)) (F.image original) v eta lo hi q n k where
  B := s.B
  P := s.P
  r := s.correction.apply
  lam := s.lam
  lam' := s.lam'
  eps := s.correction.error
  a := s.a F
  b := s.b F
  disjoint := h.disjoint
  low := h.low
  high := h.high
  price := h.price
  eps_nonneg := h.eps_nonneg
  error := by simpa only [Fintype.card_fin] using h.error
  inj := h.inj
  fixed := h.fixed
  shrink := h.shrink
  loss := h.loss
  old_prefix := h.old_prefix
  new_prefix := h.new_prefix
  sandwich := h.sandwich
  new_tail := h.new_tail.attains
  old_tail := h.old_tail.attains

lemma Certified.zero_false {loc : Fin d → V} {F : Finset V} {v eta lo hi : ℝ}
    {q k : ℕ} {s : State V} (h : Certified loc F v eta lo hi q 0 k s) : False :=
  h.coupled.zero_false

def Output.Correct (loc : Fin d → V) (F : Finset V) (v eta lo hi : ℝ)
    (total k : ℕ) (o : Output V) : Prop :=
  Disjoint (F.image original) o.B ∧ lo≤(o.lam:ℝ) ∧ (o.lam:ℝ)≤hi ∧
  PrefixData (fun j=>original (loc j)) (F.image original) o.B v o.lam eta total o.P ∧
    ((after ∅ o.P)∩F.image original).card=k

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
