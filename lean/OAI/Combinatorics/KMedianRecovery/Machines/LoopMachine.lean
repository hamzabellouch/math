import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.StepPack
import OAI.Combinatorics.KMedianRecovery.Machines.LoopInvariant

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledLoop
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryCoupled (stateBits outcomeBits outputBits)
def pack (base : List Bool) (b : ℚ) (precision k : ℕ) {m : ℕ} (f : Frame (Fin m)) : List Bool :=
  encode [base,List.replicate f.n true,List.replicate f.q true,BinaryRational.encode b,
    List.replicate precision true,k.bits,outcomeBits f.out]
noncomputable def input (x : List Bool) : List Bool := encode [field 0 x,(field 1 x).tail,field 2 x,
  field 3 x,field 4 x,field 5 x,discardPrefix (field 6 x)]
noncomputable def input_computes : PolyComputes input := list_computes
  [field 0,List.tail ∘ field 1,field 2,field 3,field 4,field 5,discardPrefix ∘ field 6] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨field_computes _⟩ | exact ⟨(field_computes _).comp WordOperations.tail_computes⟩ |
      exact ⟨(field_computes _).comp discardPrefix_computes⟩)
noncomputable def next (x : List Bool) : List Bool := encode [field 0 x,(field 1 x).tail,true::field 2 x,
  field 3 x,field 4 x,field 5 x,BinaryCoupledStep.run (input x)]
noncomputable def next_computes : PolyComputes next := by
  unfold next
  simpa only [List.map_cons,List.map_nil,Function.comp_def] using list_computes
    [field 0,List.tail ∘ field 1,List.cons true ∘ field 2,field 3,field 4,field 5,BinaryCoupledStep.run ∘ input] (by
      intro component membership; refine Classical.choice ?_
      simp only [List.mem_cons,List.not_mem_nil,or_false] at membership
      rcases membership with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact ⟨field_computes 0⟩
      · exact ⟨(field_computes 1).comp WordOperations.tail_computes⟩
      · exact ⟨(const_computes [true]).append (field_computes 2)⟩
      · exact ⟨field_computes 3⟩
      · exact ⟨field_computes 4⟩
      · exact ⟨field_computes 5⟩
      · exact ⟨input_computes.comp BinaryCoupledStep.run_computes⟩)
noncomputable def step (x : List Bool) : List Bool :=
  if extractPrefix (field 6 x)=[] then x else if field 1 x=[] then x else next x
noncomputable def step_computes : PolyComputes step := by
  change PolyComputes (fun x=>if extractPrefix (field 6 x)=[] then x else if field 1 x=[] then x else next x)
  simpa only [Function.comp_def,decide_eq_true_eq,id_eq] using
    ((field_computes 6).comp extractPrefix_computes |>.comp isEmpty_computes).cond id_computes
      (((field_computes 1).comp isEmpty_computes).cond id_computes next_computes)
variable {m d : ℕ} [PseudoMetricSpace (Fin m)]
attribute [local instance] RationalLeaves.metric
lemma step_pack (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset (Fin m))
    (Q₀ : Finset (Label (Fin m))) (v z M : ℚ) (N precision total k h p : ℕ)
    (eta lo hi : ℝ) (f : Frame (Fin m)) (hf : f.Valid loc F v eta lo hi total k h p)
    (hv : (0:ℝ)<v) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0≤eta) :
    step (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0)
      (20*N*M) precision k f)=
      pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0)
        (20*N*M) precision k (transition loc distance F v M N precision k f) := by
  rcases f with ⟨q,n,o⟩
  cases o with
  | inl o=>
    simp only [step,pack,outcomeBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
      extractPrefix_pairBits,ite_true,transition]
  | inr s=>
    cases n with
    | zero=>
      simp only [step,pack,outcomeBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
        extractPrefix_pairBits,List.cons_ne_self,ite_false,List.replicate_zero,ite_true,transition]
    | succ n=>
      have hh:=BinaryCoupledStep.run_pack distance loc hmetric F Q₀ v z M N n q precision k s eta lo hi hf.2.1 hv hv1 hlo heta
      have hin : input (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0)
          (20*N*M) precision k ⟨q,n+1,.inr s⟩)=
          BinaryCoupledStep.pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0)
            n q (20*N*M) precision k s := by
        simp only [input,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
          List.tail_replicate,outcomeBits,discardPrefix_pairBits,BinaryCoupledStep.pack,Nat.add_sub_cancel]
      have hactive : step (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0)
          (20*N*M) precision k ⟨q,n+1,.inr s⟩)=
          next (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0)
            (20*N*M) precision k ⟨q,n+1,.inr s⟩) := by
        simp only [step,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
          outcomeBits,extractPrefix_pairBits,List.cons_ne_self,ite_false,List.replicate_succ,List.cons_ne_nil]
      rw [hactive]
      simp only [next,hin,hh]
      simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
        transition,List.replicate_succ,List.tail_cons]
end MetricKMedianRecovery.BitMachine.BinaryCoupledLoop

namespace MetricKMedianRecovery.RationalHeight
lemma Height.le_pow {b : ℚ} {H : ℕ} (hb : Height b H) : b ≤ (2^H:ℕ) := by
  have hnum : (b.num:ℚ) ≤ (b.num.natAbs:ℚ) := by simpa only [Nat.cast_natAbs,Int.cast_abs] using le_abs_self (b.num:ℚ)
  have hN : (b.num.natAbs:ℚ) ≤ (2^H:ℕ) := by exact_mod_cast hb.1
  have hden : (1:ℚ) ≤ b.den := by exact_mod_cast b.den_pos
  have hnonneg : (0:ℚ) ≤ (2^H:ℕ) := by positivity
  rw [←Rat.num_div_den b]
  apply (div_le_iff₀ (by exact_mod_cast b.den_pos : (0:ℚ)<b.den)).mpr
  nlinarith
lemma Height.ceil_le_pow {b : ℚ} {H : ℕ} (hb : Height b H) : Nat.ceil b ≤ 2^H := by
  exact Nat.ceil_le.mpr hb.le_pow
lemma Height.clog_ceil {b : ℚ} {H : ℕ} (hb : Height b H) : Nat.clog 2 (Nat.ceil b) ≤ H :=
  (Nat.clog_le_iff_le_pow (by decide)).mpr hb.ceil_le_pow
end MetricKMedianRecovery.RationalHeight
namespace MetricKMedianRecovery.CanonicalLengthSearch
open RationalHeight
lemma heightBudget_le {b : ℚ} {precision H L : ℕ} (hb : Height b H) (hH : H ≤ L) (hp : precision ≤ L) :
    heightBudget b precision H ≤ 8*L+3 := by
  have hh:=hb.clog_ceil
  simp only [heightBudget,PriceBisection.iterations,sub_zero]
  omega
end MetricKMedianRecovery.CanonicalLengthSearch
namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open BinaryCoupledState
lemma bound_mono {m t h p m' t' h' p' : ℕ} (hm : m ≤ m') (ht : t ≤ t') (hh : h ≤ h') (hp : p ≤ p') :
    bound m t h p ≤ bound m' t' h' p' := by
  unfold bound BinaryCoupledState.bound historyBound bankBound labelBound
  gcongr
noncomputable def boundPoly : Polynomial ℕ :=
  let X:=Polynomial.X
  let label:=6*X+2*X+3*(8*X+3)+8
  let bank:=X*(2*X+1)
  let history:=X*(2*(X+bank)*(2*label+2)+2)
  4*bank*(2*label+2)+8*history+12*X+40+6*label+2
lemma boundPoly_eval (L : ℕ) : boundPoly.eval L=bound L L (8*L+3) L := by
  simp only [boundPoly,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
    Polynomial.eval_one,bound,BinaryCoupledState.bound,historyBound,bankBound,labelBound]
end MetricKMedianRecovery.BitMachine.BinaryCoupled

end OAI
