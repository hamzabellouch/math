import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.LabelSize
import OAI.Combinatorics.KMedianRecovery.Branching.CategoricalChoice

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {q a T L : ℕ}
lemma optionBits_length (o : Option (Fin q)) : (optionBits elemBits o).length≤2*q+2 := by
  cases o with
  | none=>simp [optionBits,encode]
  | some e=>
    have he := (Indices.bits_length_le e.val).trans (Nat.le_of_lt e.isLt)
    simpa only [optionBits,Option.toList_some,List.map_cons,List.map_nil,encode,length_cons,List.length_nil,elemBits,Nat.add_zero] using
      Nat.add_le_add_right (Nat.mul_le_mul_left 2 he) 2
lemma tableBits_length (r : Fin a→Fin T→Option (Fin q)) :
    (tableBits elemBits r).length≤a*(2*(T*(4*q+6))+2) := by
  unfold tableBits
  apply (encode_le_bound _ (T*(4*q+6)) ?_).trans
  · simp only [List.length_ofFn,Nat.le_refl]
  · intro w hw
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hw
    have h:=encode_le_bound (List.ofFn (fun t=>optionBits elemBits (r j t))) (2*q+2) (by
      intro w hw
      obtain ⟨t,rfl⟩:=List.mem_ofFn.mp hw
      exact optionBits_length (r j t))
    simp only [List.length_ofFn] at h
    convert h using 1
    ring
lemma stateBits_length (s : Categorical.GreedyState (Fin q) a T) (ht : s.1≤T) :
    (stateBits s).length≤2*T+4+2*(a*(2*(T*(4*q+6))+2)) := by
  have hc := (Indices.bits_length_le s.1).trans ht
  have hb := tableBits_length s.2
  simp only [stateBits,encode,length_cons,List.length_nil]
  omega
noncomputable def runCapPoly : Polynomial ℕ := 100*(Polynomial.X+1)^4
noncomputable def runCap : PolynomialCounter runCapPoly := PolynomialCounter.choose _
lemma stateBits_length_bound (s : Categorical.GreedyState (Fin q) a T) (ht : s.1≤T)
    (N : ℕ) (hq : q≤N) (ha : a≤N) (hT : T≤N) : (stateBits s).length≤runCapPoly.eval N := by
  have hs := stateBits_length s ht
  have hb := Nat.mul_le_mul ha (Nat.add_le_add_right (Nat.mul_le_mul_left 2
    (Nat.mul_le_mul hT (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hq) 6))) 2)
  simp only [runCapPoly,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  nlinarith [sq_nonneg (N:ℤ)]
lemma step_clock_le (part : Fin q→Fin a) (hp : Function.Surjective part) (G : Finset (Fin q)→ℚ)
    (s : Categorical.GreedyState (Fin q) a T) (ht : s.1≤T) (seed : Categorical.OracleSeed (Fin q) a T L) :
    (Categorical.Selected.greedyStep part (rule part hp) (fun S=>(G S:ℝ)) s seed).1≤T := by
  unfold Categorical.Selected.greedyStep
  split_ifs with h
  · exact Nat.succ_le_of_lt h
  · exact ht
lemma fold_clock_le (part : Fin q→Fin a) (hp : Function.Surjective part) (G : Finset (Fin q)→ℚ)
    (s : Categorical.GreedyState (Fin q) a T) (ht : s.1≤T) (seeds : List (Categorical.OracleSeed (Fin q) a T L)) :
    (seeds.foldl (Categorical.Selected.greedyStep part (rule part hp) (fun S=>(G S:ℝ))) s).1≤T := by
  induction seeds generalizing s with
  | nil=>exact ht
  | cons b bs ih=>exact ih _ (step_clock_le part hp G s ht b)
end MetricKMedianRecovery.BitMachine.BinaryCategorical

namespace MetricKMedianRecovery.FiniteSampling
lemma adaptiveRun_list {S Ω : Type*} (f : S→Ω→S) (n : ℕ) (s : S) (seed : Fin n→Ω) :
    adaptiveRun f n s seed=(List.ofFn seed).foldl f s := by
  induction n generalizing s with
  | zero=>rfl
  | succ n ih=>simpa only [adaptiveRun,List.ofFn_succ,List.foldl_cons,Fin.tail_def] using ih (f s (seed 0)) (Fin.tail seed)
end MetricKMedianRecovery.FiniteSampling
namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {q a T L : ℕ}
def runPack (ctx : List Bool) (part : Fin q→Fin a) (T : ℕ)
    (seeds : List (Categorical.OracleSeed (Fin q) a T L)) : List Bool :=
  encode [ctx,partBits part,List.replicate a true,List.replicate T true,encode (seeds.map oracleBits)]
noncomputable def initial (x : List Bool) : List Bool :=
  encode [[],repeatWords (pairBits (field 2 x,repeatWords (pairBits (field 3 x,[]))))]
noncomputable def initial_computes : PolyComputes initial := by
  have computation := cons_computes (const_computes []) (cons_computes
    (((field_computes 2).pair (((field_computes 3).pair (const_computes [])).comp repeatWords_computes)).comp repeatWords_computes)
    (const_computes []))
  unfold initial
  simpa only [Function.comp_def, encode] using computation
noncomputable def context (x : List Bool) : List Bool := encode [field 0 x,field 1 x,field 3 x]
noncomputable def context_computes : PolyComputes context :=
  cons_computes (field_computes 0) (cons_computes (field_computes 1) (cons_computes (field_computes 3) (const_computes [])))
noncomputable def run (g : List Bool→List Bool) (x : List Bool) : List Bool :=
  CappedFold.run (step g) (pairBits (runCap.word x,Fold.pack (field 4 x) (context x) (initial x)))
noncomputable def run_computes {g : List Bool→List Bool} (hg : PolyComputes g) : PolyComputes (run g) :=
  (runCap.computes.pair (Fold.pack_computes (field_computes 4) context_computes initial_computes)).comp
    (CappedFold.run_computes (step_computes hg))
lemma initial_pack (ctx : List Bool) (part : Fin q→Fin a) (seeds : List (Categorical.OracleSeed (Fin q) a T L)) :
    initial (runPack ctx part T seeds)=stateBits (Categorical.initialState (Fin q) a T) := by
  simp only [initial,runPack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,repeatWords_ofFn]
  rfl
lemma context_pack (ctx : List Bool) (part : Fin q→Fin a) (seeds : List (Categorical.OracleSeed (Fin q) a T L)) :
    context (runPack ctx part T seeds)=stepContext ctx part T := by
  simp only [context,runPack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,stepContext]
lemma runPack_dimensions (ctx : List Bool) (part : Fin q→Fin a) (seeds : List (Categorical.OracleSeed (Fin q) a T L)) :
    q≤(runPack ctx part T seeds).length ∧ a≤(runPack ctx part T seeds).length ∧ T≤(runPack ctx part T seeds).length := by
  have hq : q≤(partBits part).length := by
    simpa only [partBits,List.length_ofFn] using length_le_encode (List.ofFn (fun e=>(part e).val.bits))
  have hp : (partBits part).length≤(runPack ctx part T seeds).length := member_length (by simp)
  have ha : (List.replicate a true).length≤(runPack ctx part T seeds).length := member_length (by simp)
  have hT : (List.replicate T true).length≤(runPack ctx part T seeds).length := member_length (by simp)
  exact ⟨hq.trans hp,by simpa only [List.length_replicate] using ha,by simpa only [List.length_replicate] using hT⟩
lemma run_pack (g : List Bool→List Bool) (ctx : List Bool) (G : Finset (Fin q)→ℚ)
    (hg : ∀ xs : List (Fin q),g (pairBits (ctx,encode (xs.map elemBits)))=BinaryRational.encode (G xs.toFinset))
    (part : Fin q→Fin a) (hp : Function.Surjective part) (seeds : List (Categorical.OracleSeed (Fin q) a T L)) :
    run g (runPack ctx part T seeds)=stateBits (seeds.foldl
      (Categorical.Selected.greedyStep part (rule part hp) (fun S=>(G S:ℝ))) (Categorical.initialState (Fin q) a T)) := by
  unfold run
  rw [initial_pack,context_pack]
  have hf : field 4 (runPack ctx part T seeds)=encode (seeds.map oracleBits) := by
    simp only [runPack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [hf]
  apply CappedFold.run_typed stateBits oracleBits _ _ _ _ (step_pack g ctx G hg part hp)
  intro n
  rw [runCap.word_length]
  obtain ⟨hq,ha,hT⟩:=runPack_dimensions ctx part seeds
  exact stateBits_length_bound _ (fold_clock_le part hp G _ (Nat.zero_le _) _) _ hq ha hT
lemma run_ofFn (g : List Bool→List Bool) (ctx : List Bool) (G : Finset (Fin q)→ℚ)
    (hg : ∀ xs : List (Fin q),g (pairBits (ctx,encode (xs.map elemBits)))=BinaryRational.encode (G xs.toFinset))
    (part : Fin q→Fin a) (hp : Function.Surjective part) (seed : Fin T→Categorical.OracleSeed (Fin q) a T L) :
    run g (runPack ctx part T (List.ofFn seed))=stateBits
      (Categorical.Selected.greedyRun part (rule part hp) (fun S=>(G S:ℝ)) seed) := by
  rw [run_pack g ctx G hg part hp,Categorical.Selected.greedyRun,FiniteSampling.adaptiveRun_list]
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
