import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.ProjectionMachine
import OAI.Combinatorics.KMedianRecovery.Recovery.InitialCorrect

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitialAuto
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
variable {m d : ℕ}
def pack (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m) (F : Finset (Fin m)) (M : ℚ) (k : ℕ) : List Bool :=
  encode [Rectangular.encode distance,List.replicate d true,BinaryFinSet.encode F,
    encode (List.ofFn (fun j=>(loc j).val.bits)),BinaryRational.encode M,k.bits]
noncomputable def size (x : List Bool) : List Bool := field 1 x++Count.run (field 2 x)
noncomputable def size_computes : PolyComputes size := (field_computes 1).append ((field_computes 2).comp Count.run_computes)
noncomputable def sizeRat : PolyComputes (fun x=>BinaryRational.encode ((size x).length:ℚ)) := BinaryInitial.unaryRat size_computes
noncomputable def low (x : List Bool) : List Bool := BinaryRational.encode (2/((size x).length:ℚ)^2)
noncomputable def low_computes : PolyComputes low := by
  change PolyComputes (fun x=>BinaryRational.encode (2/((size x).length:ℚ)^2))
  have hh := RatOps.div (RatOps.const 2) (RatOps.mul sizeRat sizeRat)
  simpa only [pow_two] using hh
noncomputable def threshold (x : List Bool) : List Bool := BinaryRational.encode
  (BinaryRational.decode (field 4 x)+8*((field 1 x).length:ℚ)*BinaryRational.decode (field 4 x))
noncomputable def threshold_computes : PolyComputes threshold := RatOps.add (RatOps.ofWords (field_computes 4))
  (RatOps.mul (RatOps.mul (RatOps.const 8) (BinaryInitial.unaryRat (field_computes 1))) (RatOps.ofWords (field_computes 4)))
noncomputable def total (v : ℚ) (C : ℕ) (x : List Bool) : List Bool := true::BinaryPhaseFuel.run (1+v^2) C (threshold x)
noncomputable def total_computes (v : ℚ) (C : ℕ) : PolyComputes (total v C) := by
  change PolyComputes (fun x=>true::BinaryPhaseFuel.run (1+v^2) C (threshold x))
  simpa only [Function.comp_def,List.singleton_append] using
    (const_computes [true]).append (threshold_computes.comp (BinaryPhaseFuel.run_computes (1+v^2) C))
noncomputable def context (v : ℚ) (x : List Bool) : List Bool :=
  encode [field 0 x,field 1 x,BinaryProjection.lift (field 2 x),[],
    map BinaryProjection.originalWord (field 3 x),BinaryRational.encode v,BinaryRational.encode 0,BinaryRational.encode 0]
noncomputable def context_computes (v : ℚ) : PolyComputes (context v) := by
  unfold context
  simpa only [Function.comp_def,encode] using
    cons_computes (field_computes 0) (cons_computes (field_computes 1)
      (cons_computes ((field_computes 2).comp BinaryProjection.lift_computes) (cons_computes (const_computes [])
        (cons_computes ((field_computes 3).comp (map_computes BinaryProjection.originalWord_computes))
          (cons_computes (const_computes (BinaryRational.encode v)) (cons_computes (const_computes (BinaryRational.encode 0))
            (cons_computes (const_computes (BinaryRational.encode 0)) (const_computes []))))))))
noncomputable def initialInput (v : ℚ) (C : ℕ) (x : List Bool) : List Bool :=
  encode [context v x,size x,size x,total v C x,field 5 x,low x,field 4 x]
noncomputable def initialInput_computes (v : ℚ) (C : ℕ) : PolyComputes (initialInput v C) :=
  cons_computes (context_computes v) (cons_computes size_computes (cons_computes size_computes
    (cons_computes (total_computes v C) (cons_computes (field_computes 5)
      (cons_computes low_computes (cons_computes (field_computes 4) (const_computes [])))))))
noncomputable def run (v : ℚ) (C : ℕ) : List Bool→List Bool := BinaryInitial.run ∘ initialInput v C
noncomputable def run_computes (v : ℚ) (C : ℕ) : PolyComputes (run v C) :=
  (initialInput_computes v C).comp BinaryInitial.run_computes
lemma size_pack (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m) (F : Finset (Fin m)) (M : ℚ) (k : ℕ) :
    size (pack distance loc F M k)=List.replicate (d+F.card) true := by
  simp only [size,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryFinSet.encode_eq,
    Count.run_encode,List.length_map,Finset.length_sort,←List.replicate_add]
lemma threshold_pack (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m) (F : Finset (Fin m)) (M : ℚ) (k : ℕ) :
    threshold (pack distance loc F M k)=BinaryRational.encode (M+8*(d:ℚ)*M) := by
  simp only [threshold,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryRational.decode_encode,List.length_replicate]
lemma low_pack (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m) (F : Finset (Fin m)) (M : ℚ) (k : ℕ) :
    low (pack distance loc F M k)=BinaryRational.encode (2/((d+F.card:ℕ):ℚ)^2) := by
  rw [low,size_pack,List.length_replicate]
lemma total_pack (v M : ℚ) (hv : 0<v) (hM : 0<M) (C : ℕ) (hC : 2≤(1+v^2)^C)
    (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m) (F : Finset (Fin m)) (k : ℕ) :
    total v C (pack distance loc F M k)=List.replicate (HistoryPhaseBound.limit v ((M:ℝ)+8*(d:ℝ)*M)+1) true := by
  rw [total,threshold_pack,BinaryPhaseFuel.run_encode v _ hv (by positivity) C hC]
  simp only [Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,List.replicate_succ]
lemma context_pack (v M : ℚ) (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m) (F : Finset (Fin m)) (k : ℕ) :
    context v (pack distance loc F M k)=BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) ∅ v 0 0 := by
  simp only [context,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryProjection.lift_encode,map_encode,List.map_ofFn]
  simp only [BinaryFiniteContext.pack,setBits,labels,BinaryLabel.orderedSort,Finset.sort_empty,List.map_nil,List.map_ofFn,encode]
  rfl
lemma initialInput_pack (v M : ℚ) (hv : 0<v) (hM : 0<M) (C : ℕ) (hC : 2≤(1+v^2)^C)
    (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m) (F : Finset (Fin m)) (k : ℕ) :
    initialInput v C (pack distance loc F M k)=BinaryInitial.pack distance loc F v
      (2/((d+F.card:ℕ):ℚ)^2) M (d+F.card) (d+F.card)
      (HistoryPhaseBound.limit v ((M:ℝ)+8*(d:ℝ)*M)+1) k := by
  rw [initialInput,context_pack,size_pack,total_pack v M hv hM C hC,low_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryInitial.pack]
end MetricKMedianRecovery.BitMachine.BinaryInitialAuto

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeInvariant PhaseMergeCertificate HistoryPhaseBound
variable {V : Type*} [LinearOrder V] {d : ℕ}
lemma start_small_eq (loc : Fin d→V) (distance : V→Fin d→ℚ) (F : Finset V)
    (v lo M : ℚ) (N precision total k : ℕ) (o : Output V)
    (he : start loc distance F v lo M N precision total k=.small o) :
    o=finish ∅ lo [] (initialHistory loc distance F v lo total) ∧
      initialCount loc distance F v lo total≤k := by
  simp only [start] at he
  split at he
  next hc => exact ⟨(StartOutput.small.inj he).symm,hc⟩
  next => split at he <;> first | contradiction | (split at he <;> contradiction)
variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric
lemma start_small_certificate (loc : Fin d→V) (distance : V→Fin d→ℚ)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset V)
    (v lo M : ℚ) (N precision k : ℕ) (o : Output V)
    (he : start loc distance F v lo M N precision
      (limit v ((M:ℝ)+8*(d:ℝ)*(M:ℝ))+1) k=.small o)
    (hd : 0<d) (hF : F.Nonempty) (hv : (0:ℝ)<v) (hv1 : (v:ℝ)<1/6)
    (hlo : 0<lo) (hM : 0<M) (hlohi : lo≤8*(d:ℚ)*M)
    (hfar : ∀ i∈F,∀ j,1≤dist i (loc j)) (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ)) :
    o.project⊆F ∧ o.project.Nonempty ∧ o.project.card≤k ∧
    ∃ (Q : ℝ) (alpha : Fin d→ℝ), 0≤Q ∧ (∑ j,nearestDistance (loc j) o.project)≤Q ∧
      PhaseOriginalLedger.Dual loc F v lo alpha ∧ (1-3*(v:ℝ))*Q≤∑ j,alpha j := by
  let total := limit v ((M:ℝ)+8*(d:ℝ)*(M:ℝ))+1
  obtain ⟨rfl,hcount⟩:=start_small_eq loc distance F v lo M N precision total k o he
  have hfar' : ∀ x∈F.image original,∀ j,1≤dist x (original (loc j)) := by
    intro x hx j
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
    rw [original_dist]
    exact hfar i hi j
  have hdiam' : ∀ x∈F.image original,∀ j,dist x (original (loc j))≤(M:ℝ) := by
    intro x hx j
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
    rw [original_dist]
    exact hdiam i hi j
  have hloR : (0:ℝ)<lo := by exact_mod_cast hlo
  have hhi : (lo:ℝ)≤8*(d:ℝ)*(M:ℝ) := by exact_mod_cast hlohi
  have hZ : 0<(M:ℝ)+8*(d:ℝ)*(M:ℝ) := by exact_mod_cast (show 0<M+8*(d:ℚ)*M by positivity)
  have ht:=initialHistory_spec loc distance hmetric F v lo total hv hv1
  have hp0:=PhaseInitialBracket.empty_prefix (fun j=>original (loc j)) (F.image original) ∅
    (v:ℝ) (lo:ℝ) 0 hloR.le hfar'
  have hp : PrefixData (fun j=>original (loc j)) (F.image original) ∅ v lo 0 total
      (initialHistory loc distance F v lo total) := by
    have hh:=hp0.append_exact hv hv1 hloR le_rfl _ ht.2.1 ht.2.2
    simpa only [ht.1,Nat.zero_add,List.nil_append] using hh
  have hterm:=PhaseTerminalProducer.terminal_prefix (hF.image original) hv hv1 hdiam' hZ (by linarith only [hhi]) hp
  have hQF : after ∅ (initialHistory loc distance F v lo total)⊆F.image original := by
    simpa only [Finset.union_empty] using hp.after_subset
  have hne : (after ∅ (initialHistory loc distance F v lo total)).Nonempty := by
    by_contra hn
    have hh:=hterm ⟨0,hd⟩
    apply hh
    intro f hf
    rw [Finset.not_nonempty_iff_eq_empty.mp hn] at hf
    exact False.elim (Finset.notMem_empty f hf)
  obtain ⟨alpha,hpos,hdual,hpay,hstrict⟩:=certify (hF.image original) (Finset.disjoint_empty_right _) hv hv1 hloR
    hfar' hdiam' hZ hhi hp
  refine ⟨project_subset F ∅ _ (rooted_empty F) hp.after_subset,project_nonempty hne,?_,
    ∑ j,nearestDistance (original (loc j)) (after ∅ (initialHistory loc distance F v lo total)),alpha,
    Finset.sum_nonneg (fun j _=>nearestDistance_nonneg _ _),?_,?_,?_⟩
  · change (RationalLeaves.project (after ∅ ([]++initialHistory loc distance F v lo total))).card≤k
    rw [List.nil_append]
    exact (project_card _).trans (by simpa only [initialCount,Finset.inter_eq_left.mpr hQF] using hcount)
  · exact Finset.sum_le_sum (fun j _=>project_distance (loc j) _)
  · refine ⟨hpos,?_,?_⟩
    · intro i hi
      simpa only [original_dist] using hdual (original i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
    · intro C hC i hi b hb hP hlp hsmall
      have hP' : 0<∑ j∈C,dist (original i) (original (loc j)) := by simpa only [original_dist] using hP
      have hlp' : (lo:ℝ)≤b*(∑ j∈C,dist (original i) (original (loc j))) := by
        simpa only [original_dist] using hlp
      simpa only [original_dist] using hstrict C hC (original i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩) b hb hP' hlp' hsmall
  · simp only [mul_zero,sub_zero] at hpay
    have hh : (0:ℝ)≤(((after ∅ (initialHistory loc distance F v lo total)∩F.image original).card):ℝ)*(lo:ℝ) :=
      mul_nonneg (Nat.cast_nonneg _) hloR.le
    linarith only [hpay,hh]
end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
