import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.CoupledLoop
import OAI.Combinatorics.KMedianRecovery.Recovery.InitialRows

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [LinearOrder V] {d : ℕ}

def initial (l u : ℚ) (T U : List (List (Label V))) : State V :=
  ⟨∅,[],.identity,l,u,T,U⟩

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

lemma initial_certified {loc : Fin d → V} {F : Finset V} {v eta lo hi : ℝ}
    {l u : ℚ} {n k : ℕ} {T U : List (List (Label V))}
    (hl : lo≤(l:ℝ)) (hu : (u:ℝ)≤hi) (hlu : l≤u) (hl0 : (0:ℝ)≤l)
    (hwidth : (u:ℝ)-l≤(d:ℝ)*eta)
    (hfar : ∀ i∈F,∀ j,1≤dist i (loc j))
    (hT : Runs (fun j=>original (loc j)) (F.image original) ∅ ∅ v u 0 n T)
    (hU : Runs (fun j=>original (loc j)) (F.image original) ∅ ∅ v l 0 n U)
    (hs : Sandwich k ((after ∅ T)∩F.image original).card ((after ∅ U)∩F.image original).card) :
    Certified loc F v eta lo hi 0 n k (initial l u T U) := by
  have hf : ∀ x∈F.image original,∀ j,1≤dist x (original (loc j)) := by
    intro x hx j
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
    rw [original_dist]
    exact hfar i hi j
  have hp := PhaseInitialBracket.empty_prefix (fun j=>original (loc j)) (F.image original) ∅
    v (l:ℝ) eta hl0 hf
  have hp' := PhaseInitialBracket.empty_prefix (fun j=>original (loc j)) (F.image original) ∅
    v (u:ℝ) eta (hl0.trans (by exact_mod_cast hlu)) hf
  refine {
    before := by simp [initial,Before]
    before_map := by simp [initial,State.mapFree,Before]
    disjoint := Finset.disjoint_empty_right _
    low := hl
    high := hu
    price := by exact_mod_cast hlu
    eps_nonneg := by norm_num [initial,Correction.error]
    error := ?_
    inj := Function.injective_id
    fixed := fun _ _=>rfl
    shrink := fun _ _ _=>le_rfl
    loss := fun _ _ _=>by simp only [initial,Correction.apply,Correction.error,id_eq,Rat.cast_zero,add_zero,le_refl]
    old_prefix := hp
    new_prefix := ?_
    sandwich := hs
    new_tail := ?_
    old_tail := hU }
  · simpa only [initial,Correction.error,Rat.cast_zero,mul_zero,add_zero] using hwidth
  · simpa only [initial,State.mapFree,State.mapPrefix,Finset.image_empty,List.map_nil] using hp'
  · simpa only [initial,State.mapFree,State.mapPrefix,Finset.image_empty,List.map_nil,after] using hT

end MetricKMedianRecovery.CanonicalCoupledMerge

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [LinearOrder V] {d : ℕ}

inductive StartOutput (V : Type*) where
  | small (o : Output V)
  | normal (o : Output V)

def initialHistory (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (v lam : ℚ) (total : ℕ) : List (List (Label V)) :=
  FiniteLabelContinuation.continuation (fun j=>original (loc j)) (rows distance)
    (F.image original) v lam 0 total ∅

def initialCount (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (v lam : ℚ) (total : ℕ) : ℕ :=
  ((after ∅ (initialHistory loc distance F v lam total))∩F.image original).card

def start (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (v lo M : ℚ) (N precision total k : ℕ) : StartOutput V :=
  let count := fun lam => initialCount loc distance F v lam total
  if count lo≤k then .small (finish ∅ lo [] (initialHistory loc distance F v lo total))
  else
    let high := 8*(d:ℚ)*M
    let I := PriceBisection.search count k (PriceBisection.iterations lo high precision) (lo,high)
    let U := initialHistory loc distance F v I.1 total
    let T := initialHistory loc distance F v I.2 total
    if count I.1=k then .normal (finish ∅ I.1 [] U)
    else if count I.2=k then .normal (finish ∅ I.2 [] T)
    else .normal (run loc distance F v M N precision k 0 total (initial I.1 I.2 T U))

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

def StartOutput.Correct (loc : Fin d → V) (F : Finset V) (v eta : ℝ) (lo M : ℚ)
    (total k : ℕ) : StartOutput V → Prop
  | .small o => o.B=∅ ∧ o.lam=lo ∧
      PrefixData (fun j=>original (loc j)) (F.image original) ∅ v lo eta total o.P ∧
      ((after ∅ o.P)∩F.image original).card≤k
  | .normal o => o.Correct loc F v eta lo (8*(d:ℝ)*(M:ℝ)) total k

lemma initialHistory_spec (loc : Fin d → V) (distance : V → Fin d → ℚ)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset V)
    (v lam : ℚ) (total : ℕ) (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) :
    Runs (fun j=>original (loc j)) (F.image original) ∅ ∅ v lam 0 total
      (initialHistory loc distance F v lam total) :=
  FiniteLabelContinuation.continuation_spec _ _ (rows_spec loc distance hmetric) _ _ _ _ _ hv hv1 _ _
    (Finset.empty_subset _)

lemma start_correct (loc : Fin d → V) (distance : V → Fin d → ℚ)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset V)
    (v lo M : ℚ) (eta : ℝ) (N precision total k : ℕ)
    (hd : 0<d) (hdN : d≤N) (hk : 2≤k) (hF : F.Nonempty) (hM : 0<M) (hN : 3≤N)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0≤eta)
    (hlohi : lo≤8*(d:ℚ)*M) (hprecision : (1/(2:ℚ)^precision:ℚ)≤eta)
    (hfar : ∀ i∈F,∀ j,1≤dist i (loc j)) (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ)) :
    (start loc distance F v lo M N precision total k).Correct loc F v eta lo M total k := by
  let count := fun lam=>initialCount loc distance F v lam total
  let high : ℚ := 8*(d:ℚ)*M
  have hloR : (0:ℝ)<lo := by exact_mod_cast hlo
  have hhighR : (high:ℝ)=8*(d:ℝ)*(M:ℝ) := by simp only [high,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat]
  have hhN : 8*(d:ℝ)*(M:ℝ)≤8*N*(M:ℝ) := by
    gcongr
  have hfar' : ∀ x∈F.image original,∀ j,1≤dist x (original (loc j)) := by
    intro x hx j
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
    rw [original_dist]
    exact hfar i hi j
  have hs (lam : ℚ) := initialHistory_spec loc distance hmetric F v lam total hv hv1
  have hp (lam : ℚ) (hlam : (0:ℝ)≤lam) :=
    PhaseInitialBracket.empty_prefix (fun j=>original (loc j)) (F.image original) ∅ v lam eta hlam hfar'
  dsimp only [start]
  change StartOutput.Correct loc F v eta lo M total k (if count lo≤k then _ else _)
  split
  next hc =>
    refine ⟨rfl,rfl,?_,hc⟩
    have ht := hs lo
    have hh := (hp lo hloR.le).append_exact hv hv1 hloR heta _ ht.2.1 ht.2.2
    simpa only [ht.1,Nat.zero_add,finish,List.nil_append] using hh
  next hc =>
    have hhigh : count high≤k := by
      let : NeZero d := ⟨by omega⟩
      apply (PhaseUpperBracket.attains_high (fun j=>original (loc j)) (F.image original)
        (v:ℝ) (M:ℝ) hv hv1 (by exact_mod_cast hM) (fun x hx j=>by
          obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
          rw [original_dist]
          exact hdiam i hi j) (n:=total) (c:=count high) ?_).trans (by omega : 1≤k)
      have hh := (hs high).attains
      simpa only [Fintype.card_fin,hhighR,count,initialCount] using hh
    let I := PriceBisection.search count k (PriceBisection.iterations lo high precision) (lo,high)
    obtain ⟨hl,hlu,hu,hcl,hcu,hw⟩:=PriceBisection.search_spec count k
      (PriceBisection.iterations lo high precision) lo high hlohi (by omega) hhigh
    change k≤count I.1 at hcl
    change count I.2≤k at hcu
    have hlR : (lo:ℝ)≤(I.1:ℝ) := by exact_mod_cast hl
    have hluR : (I.1:ℝ)≤(I.2:ℝ) := by exact_mod_cast hlu
    have huR : (I.2:ℝ)≤8*(d:ℝ)*(M:ℝ) := by rw [←hhighR]; exact_mod_cast hu
    have hlp : (0:ℝ)<(I.1:ℝ) := hloR.trans_le hlR
    have hup : (0:ℝ)<(I.2:ℝ) := hlp.trans_le hluR
    have hw' : I.2-I.1 ≤1/(2:ℚ)^precision := hw ▸ PriceBisection.iterations_precision lo high precision
    change StartOutput.Correct loc F v eta lo M total k (if count I.1=k then _ else if count I.2=k then _ else _)
    split
    next he =>
      have hh := finish_correct (hp I.1 hlp.le) hv hv1 hlp heta (Finset.disjoint_empty_right _)
        hlR (hluR.trans huR) (hs I.1) he
      simpa only [StartOutput.Correct,Nat.zero_add] using hh
    next he =>
      split
      next he' =>
        have hh := finish_correct (hp I.2 hup.le) hv hv1 hup heta (Finset.disjoint_empty_right _)
          (hlR.trans hluR) huR (hs I.2) he'
        simpa only [StartOutput.Correct,Nat.zero_add] using hh
      next he' =>
        have hwR : (I.2:ℝ)-I.1≤(d:ℝ)*eta := by
          have hh : (I.2:ℝ)-I.1≤eta := by
            have hwr : ((I.2-I.1:ℚ):ℝ)≤((1/(2:ℚ)^precision:ℚ):ℝ) := by exact_mod_cast hw'
            simpa only [Rat.cast_sub] using hwr.trans hprecision
          have hdR : (1:ℝ)≤d := by exact_mod_cast hd
          exact hh.trans (by nlinarith)
        have hsand : Sandwich k (count I.2) (count I.1) := Or.inl ⟨by omega,by omega⟩
        have hi := initial_certified hlR huR hlu hlp.le hwR hfar (hs I.2) (hs I.1) hsand
        have hh := run_correct loc distance hmetric F v M eta lo (8*(d:ℝ)*(M:ℝ)) N precision k
          hF hM hN hv hv1 hloR heta hhN hprecision hdiam 0 total _ hi
        simpa only [StartOutput.Correct,Nat.zero_add] using hh

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
