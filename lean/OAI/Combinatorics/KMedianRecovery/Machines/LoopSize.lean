import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.LoopMachine

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledLoop
open WordOperations WordList BinaryArithmetic RationalLeaves RationalHeight CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryCoupled (stateBits outcomeBits outputBits)
lemma components (base : List Bool) (b : ℚ) (precision k : ℕ) {m : ℕ} (f : Frame (Fin m)) :
    base.length ≤ (pack base b precision k f).length ∧
    f.q+f.n ≤ (pack base b precision k f).length ∧
    (BinaryRational.encode b).length ≤ (pack base b precision k f).length ∧
    precision ≤ (pack base b precision k f).length ∧
    k.bits.length ≤ (pack base b precision k f).length := by
  simp only [pack,length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    List.length_cons,List.length_nil,List.length_replicate]
  omega
lemma base_dimension {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) :
    m ≤ (BinaryFiniteContext.pack distance loc F Q v z lam).length := by
  have h:=length_le_encode (List.ofFn (fun i : Fin m=>RationalMatrix.rowEncode (distance i)))
  simp only [List.length_ofFn] at h
  change m ≤ (Rectangular.encode distance).length at h
  simp only [BinaryFiniteContext.pack,length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    List.length_cons,List.length_nil]
  omega

noncomputable def capPoly : Polynomial ℕ := 20*Polynomial.X+4*BinaryCoupled.boundPoly+100
lemma capPoly_eval (L : ℕ) : capPoly.eval L=20*L+4*BinaryCoupled.bound L L (8*L+3) L+100 := by
  simp only [capPoly,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
    BinaryCoupled.boundPoly_eval]
variable {m d : ℕ} [PseudoMetricSpace (Fin m)]
attribute [local instance] RationalLeaves.metric
lemma outcome_length_bound {loc : Fin d→Fin m} {F : Finset (Fin m)} {v eta lo hi : ℝ}
    {total k h L : ℕ} {f : Frame (Fin m)}
    (hf : f.Valid loc F v eta lo hi total k h L) (ht : total ≤ L) (hm : m ≤ L) (hh : h ≤ 8*L+3) :
    (outcomeBits f.out).length ≤ BinaryCoupled.bound L L (8*L+3) L+3 := by
  obtain ⟨he,hf⟩:=hf
  have hq : f.q ≤ L := by omega
  cases ho : f.out with
  | inl o=>
    rw [ho] at hf
    have hl:=BinaryCoupled.output_length_bound hf.1 hf.2 hq ht
    have hb:=BinaryCoupled.bound_mono hm (le_refl L) hh (le_refl L)
    simp only [outcomeBits,pairBits_length,List.length_nil]
    omega
  | inr s=>
    rw [ho] at hf
    have hl:=BinaryCoupled.length_bound hf.1 hf.2.1 hf.2.2 (show f.q+f.n ≤ L by omega)
    have hb:=BinaryCoupled.bound_mono hm (le_refl L) hh (le_refl L)
    simp only [outcomeBits,pairBits_length,List.length_cons,List.length_nil]
    omega
lemma pack_length_bound {loc : Fin d→Fin m} {F : Finset (Fin m)} {v eta lo hi : ℝ}
    {total k h L precision : ℕ} {f : Frame (Fin m)} {base : List Bool} {b : ℚ}
    (hf : f.Valid loc F v eta lo hi total k h L) (ht : total ≤ L) (hm : m ≤ L) (hh : h ≤ 8*L+3)
    (hbase : base.length ≤ L) (hb : (BinaryRational.encode b).length ≤ L)
    (hp : precision ≤ L) (hk : k.bits.length ≤ L) :
    (pack base b precision k f).length ≤ capPoly.eval L := by
  have ho:=outcome_length_bound hf ht hm hh
  have hn : f.q+f.n ≤ L := hf.1.trans_le ht
  simp only [pack,length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    List.length_cons,List.length_nil,List.length_replicate,capPoly_eval]
  omega
end MetricKMedianRecovery.BitMachine.BinaryCoupledLoop

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledLoop
open WordOperations WordList BinaryArithmetic RationalLeaves RationalHeight CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryCoupled (stateBits outcomeBits outputBits)
noncomputable def capacity : PolynomialCounter capPoly := PolynomialCounter.choose capPoly
noncomputable def iterationInput (x : List Bool) : List Bool := pairBits (field 1 x,pairBits (capacity.word x,x))
noncomputable def iterationInput_computes : PolyComputes iterationInput :=
  (field_computes 1).pair (capacity.computes.pair id_computes)
noncomputable def stateRun : List Bool→List Bool := BoundedIteration.run step ∘ iterationInput
noncomputable def stateRun_computes : PolyComputes stateRun :=
  iterationInput_computes.comp (BoundedIteration.run_computes step_computes)
noncomputable def run : List Bool→List Bool := discardPrefix ∘ field 6 ∘ stateRun
noncomputable def run_computes : PolyComputes run := by
  unfold run
  simpa only [Function.comp_def] using
    stateRun_computes.comp ((field_computes 6).comp discardPrefix_computes)
variable {m d : ℕ} [PseudoMetricSpace (Fin m)]
attribute [local instance] RationalLeaves.metric
attribute [local irreducible] BinaryCoupledStep.run
lemma run_pack (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset (Fin m))
    (Q₀ : Finset (Label (Fin m))) (v z M : ℚ) (eta lo hi : ℝ) (N precision q n k : ℕ)
    (hF : F.Nonempty) (hM : 0<M) (hN : 3 ≤ N)
    (hv : (0:ℝ)<v) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0 ≤ eta)
    (hhi : hi ≤ 8*N*(M:ℝ)) (hprecision : (1/(2:ℚ)^precision:ℚ) ≤ eta)
    (hdiam : ∀ i∈F,∀ j,dist i (loc j) ≤ (M:ℝ))
    (s : State (Fin m)) (hc : Certified loc F v eta lo hi q n k s)
    (hkey : s.correction.Keys q)
    (hr : let x := pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0) (20*N*M) precision k ⟨q,n,.inr s⟩;
      s.Resources F q (CanonicalLengthSearch.heightBudget (20*N*M) precision x.length) x.length) :
    run (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0)
      (20*N*M) precision k ⟨q,n,.inr s⟩)=
      outputBits (CanonicalCoupledMerge.run loc distance F v M N precision k q n s) := by
  let base:=BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0
  let f : Frame (Fin m):=⟨q,n,.inr s⟩
  let x:=pack base (20*N*M) precision k f
  let L:=x.length
  let H:=CanonicalLengthSearch.heightBudget (20*N*M) precision L
  let tr:=transition loc distance F v M N precision k
  have hcomponents:=components base (20*N*M) precision k f
  change base.length ≤ L ∧ q+n ≤ L ∧ (BinaryRational.encode (20*N*M)).length ≤ L ∧ precision ≤ L ∧ k.bits.length ≤ L at hcomponents
  have hfar : Height (20*N*M) L := (BinaryRational.input_height _).mono hcomponents.2.2.1
  have hh : H ≤ 8*L+3:=CanonicalLengthSearch.heightBudget_le hfar le_rfl hcomponents.2.2.2.1
  have hm : m ≤ L:=(base_dimension distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0).trans hcomponents.1
  have hgood : ∀ j,(tr^[j] f).Valid loc F v eta lo hi (q+n) k H L := by
    intro j
    induction j with
    | zero=>exact ⟨rfl,hc,hr,hkey⟩
    | succ j ih=>
      rw [Function.iterate_succ_apply']
      exact transition_valid loc distance hmetric F v M eta lo hi N precision (q+n) k L L
        hF hM hN hv hv1 hlo heta hhi hprecision hdiam hfar _ ih
  have he : ∀ j,step^[j] x=pack base (20*N*M) precision k (tr^[j] f) := by
    intro j
    induction j with
    | zero=>rfl
    | succ j ih=>
      rw [Function.iterate_succ_apply',ih,Function.iterate_succ_apply']
      exact step_pack distance loc hmetric F Q₀ v z M N precision (q+n) k H L eta lo hi _ (hgood j) hv hv1 hlo heta
  have hbound : ∀ j,(step^[j] x).length ≤ capPoly.eval L := by
    intro j
    rw [he]
    exact pack_length_bound (hgood j) hcomponents.2.1 hm hh hcomponents.1 hcomponents.2.2.1
      hcomponents.2.2.2.1 hcomponents.2.2.2.2
  have hstate : stateRun x=pack base (20*N*M) precision k (tr^[n] f) := by
    simp only [stateRun,Function.comp_apply,iterationInput]
    rw [BoundedIteration.run_eq]
    · have hfield : field 1 x=List.replicate n true := by
        simp only [x,pack,f,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
      rw [hfield,List.length_replicate,he]
    · intro j _
      rw [capacity.word_length]
      exact hbound j
  obtain ⟨o,ho⟩:=valid_stopped_output (hgood n) (iterate_stopped loc distance F v M N precision k n f (le_refl n))
  have hval : o=CanonicalCoupledMerge.run loc distance F v M N precision k q n s := by
    have hh:=iterate_value loc distance F v M N precision k n f
    change (tr^[n] f).value loc distance F v M N precision k=f.value loc distance F v M N precision k at hh
    simpa only [Frame.value,ho,f] using hh
  change run x=_
  simp only [run,Function.comp_apply,hstate,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    ho,outcomeBits,discardPrefix_pairBits,hval]
end MetricKMedianRecovery.BitMachine.BinaryCoupledLoop

end OAI
