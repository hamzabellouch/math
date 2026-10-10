import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.InitialPack

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitial
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing PhaseMergeInvariant PhaseCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryCoupled (outputBits)
variable {m d : ℕ} [PseudoMetricSpace (Fin m)]
attribute [local instance] RationalLeaves.metric
lemma run_pack (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset (Fin m))
    (v lo M : ℚ) (eta : ℝ) (N precision total k : ℕ)
    (hd : 0<d) (hdN : d≤N) (hk : 2≤k) (hF : F.Nonempty) (hM : 0<M) (hN : 3≤N)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0≤eta)
    (hlohi : lo≤8*(d:ℚ)*M) (hprecision : (1/(2:ℚ)^precision:ℚ)≤eta)
    (hfar : ∀ i∈F,∀ j,1≤dist i (loc j)) (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ)) :
    run (pack distance loc F v lo M N precision total k)=
      output (start loc distance F v lo M N precision total k) := by
  let xx := pack distance loc F v lo M N precision total k
  let count := fun lam=>initialCount loc distance F v lam total
  let high : ℚ := 8*(d:ℚ)*M
  let I := PriceBisection.search count k (PriceBisection.iterations lo high precision) (lo,high)
  have hkbits : field 4 xx=k.bits := by
    simp only [xx,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  have hloC : loCount xx=(count lo).bits := loCount_pack distance loc F v lo M N precision total k
  have hloF : loFinish xx=outputBits (finish ∅ lo [] (initialHistory loc distance F v lo total)) :=
    loFinish_pack distance loc F v lo M N precision total k
  change run xx=output (start loc distance F v lo M N precision total k)
  unfold run start
  rw [hkbits,hloC,value_bits,value_bits]
  change (if count lo≤k then _ else _)=output (if count lo≤k then _ else _)
  by_cases hc : count lo≤k
  · simp only [hc,ite_eq_left,output,hloF]
  · rw [ite_eq_right hc,ite_eq_right hc]
    have hloR : (0:ℝ)<lo := by exact_mod_cast hlo
    have hhighR : (high:ℝ)=8*(d:ℝ)*(M:ℝ) := by simp only [high,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat]
    have hhN : 8*(d:ℝ)*(M:ℝ)≤8*N*(M:ℝ) := by gcongr
    have hs (lam : ℚ) := initialHistory_spec loc distance hmetric F v lam total hv hv1
    have hhigh : count high≤k := by
      let : NeZero d := ⟨by omega⟩
      apply (PhaseUpperBracket.attains_high (fun j=>original (loc j)) (F.image original)
        (v:ℝ) (M:ℝ) hv hv1 (by exact_mod_cast hM) (fun x hx j=>by
          obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
          rw [original_dist]
          exact hdiam i hi j) (n:=total) (c:=count high) ?_).trans (by omega : 1≤k)
      have hh := (hs high).attains
      simpa only [Fintype.card_fin,hhighR,count,initialCount] using hh
    obtain ⟨hl,hlu,hu,hcl,hcu,hw⟩:=PriceBisection.search_spec count k
      (PriceBisection.iterations lo high precision) lo high hlohi (by omega) hhigh
    change k≤count I.1 at hcl
    change count I.2≤k at hcu
    obtain ⟨hlC,huC⟩:=counts_pack distance loc F v lo M N precision total k
    obtain ⟨hlF,huF⟩:=finishes_pack distance loc F v lo M N precision total k
    change lowerCount xx=(count I.1).bits at hlC
    change upperCount xx=(count I.2).bits at huC
    change lowerFinish xx=outputBits (finish ∅ I.1 [] (initialHistory loc distance F v I.1 total)) at hlF
    change upperFinish xx=outputBits (finish ∅ I.2 [] (initialHistory loc distance F v I.2 total)) at huF
    unfold normal
    rw [hlC,huC,hkbits,value_bits,value_bits,value_bits]
    change pairBits ([true], if count I.1=k then _ else if count I.2=k then _ else _)=
      output (if count I.1=k then _ else if count I.2=k then _ else _)
    by_cases he : count I.1=k
    · rw [ite_eq_left he,ite_eq_left he]
      simp only [output,hlF]
      rfl
    · rw [ite_eq_right he,ite_eq_right he]
      by_cases he' : count I.2=k
      · rw [ite_eq_left he',ite_eq_left he']
        simp only [output,huF]
        rfl
      · rw [ite_eq_right he',ite_eq_right he']
        simp only [output]
        have hlR : (lo:ℝ)≤(I.1:ℝ) := by exact_mod_cast hl
        have hluR : (I.1:ℝ)≤(I.2:ℝ) := by exact_mod_cast hlu
        have huR : (I.2:ℝ)≤8*(d:ℝ)*(M:ℝ) := by rw [←hhighR]; exact_mod_cast hu
        have hlp : (0:ℝ)<(I.1:ℝ) := hloR.trans_le hlR
        have hw' : I.2-I.1 ≤1/(2:ℚ)^precision := hw ▸ PriceBisection.iterations_precision lo high precision
        have hwR : (I.2:ℝ)-I.1≤(d:ℝ)*eta := by
          have hh : (I.2:ℝ)-I.1≤eta := by
            have hwr : ((I.2-I.1:ℚ):ℝ)≤((1/(2:ℚ)^precision:ℚ):ℝ) := by exact_mod_cast hw'
            simpa only [Rat.cast_sub] using hwr.trans hprecision
          have hdR : (1:ℝ)≤d := by exact_mod_cast hd
          exact hh.trans (by nlinarith)
        have hsand : Sandwich k (count I.2) (count I.1) := Or.inl ⟨by omega,by omega⟩
        have hi := initial_certified hlR huR hlu hlp.le hwR hfar (hs I.2) (hs I.1) hsand
        rw [loopInput_pack]
        rw [BinaryCoupledLoop.run_initial distance loc hmetric F v M I.1 I.2 eta lo (8*(d:ℝ)*(M:ℝ)) N precision total k
          hF hM hN hv hv1 hloR heta hhN hprecision hdiam _ _ hi]
end MetricKMedianRecovery.BitMachine.BinaryInitial

namespace MetricKMedianRecovery.RationalPhaseFuel

noncomputable def exponent (K Z : ℚ) : ℕ := ⌈Real.log (Z:ℝ) / Real.log (K:ℝ)⌉₊

lemma exponent_le_iff (K Z : ℚ) (hK : 1 < K) (hZ : 0 < Z) (n : ℕ) :
    exponent K Z ≤ n ↔ Z ≤ K^n := by
  have hk : (1:ℝ) < (K:ℝ) := by exact_mod_cast hK
  have hz : (0:ℝ) < (Z:ℝ) := by exact_mod_cast hZ
  rw [exponent,Nat.ceil_le,div_le_iff₀ (Real.log_pos hk)]
  rw [←Real.log_pow,Real.log_le_log_iff hz (pow_pos (lt_trans (by norm_num) hk) _)]
  exact_mod_cast Iff.rfl (a := Z ≤ K^n)

lemma to_limit (v Z : ℚ) : exponent (1+v^2) Z + 1 = HistoryPhaseBound.limit v Z := by
  simp only [exponent,HistoryPhaseBound.limit,Rat.cast_add,Rat.cast_one,Rat.cast_pow]

lemma exponent_bound (K Z : ℚ) (hK : 1 < K) (hZ : 0 < Z) (C N : ℕ)
    (hC : 2 ≤ K^C) (hN : Z ≤ 2^N) : exponent K Z ≤ C*N := by
  apply (exponent_le_iff K Z hK hZ _).mpr
  calc
    Z ≤ 2^N := hN
    _ ≤ (K^C)^N := pow_le_pow_left₀ (by norm_num) hC N
    _ = K^(C*N) := (pow_mul K C N).symm

lemma exists_multiplier (K : ℚ) (hK : 1 < K) : ∃ C : ℕ, 2 ≤ K^C := by
  obtain ⟨C,hC⟩ := pow_unbounded_of_one_lt (2:ℚ) hK
  exact ⟨C,hC.le⟩

def next (K Z : ℚ) (q : ℕ) : ℕ := if Z ≤ K^q then q else q+1

lemma next_min (K Z : ℚ) (hK : 1 < K) (hZ : 0 < Z) (j : ℕ) :
    next K Z (min j (exponent K Z)) = min (j+1) (exponent K Z) := by
  unfold next
  simp only [←exponent_le_iff K Z hK hZ]
  split_ifs <;> omega

lemma iterate_next (K Z : ℚ) (hK : 1 < K) (hZ : 0 < Z) (j : ℕ) :
    (next K Z)^[j] 0 = min j (exponent K Z) := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply',ih,next_min K Z hK hZ]

end MetricKMedianRecovery.RationalPhaseFuel

namespace MetricKMedianRecovery.RationalHeight
lemma Height.le_bound {q : ℚ} {b : ℕ} (h : Height q b) : q ≤ (2:ℚ)^b := by
  have hd : (1:ℚ) ≤ (q.den:ℚ) := by exact_mod_cast q.den_pos
  have hn : (q.num:ℚ) ≤ (2:ℚ)^b := by
    calc
      (q.num:ℚ) ≤ (q.num.natAbs:ℚ) := by
        calc
          (q.num:ℚ) ≤ |(q.num:ℚ)| := le_abs_self _
          _ = (q.num.natAbs:ℚ) := by simp
      _ ≤ (2:ℚ)^b := by exact_mod_cast h.1
  rw [←Rat.num_div_den q]
  exact (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0:ℚ)<1) hd)).mpr
    (hn.trans (le_mul_of_one_le_right (by positivity) hd))
end MetricKMedianRecovery.RationalHeight

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFuel
open WordOperations BinaryArithmetic RationalPhaseFuel RationalHeight

def pack (Z w : ℚ) (q : ℕ) : List Bool :=
  pairBits (BinaryRational.encode Z,pairBits (BinaryRational.encode w,List.replicate q true))
def threshold (x : List Bool) : ℚ := BinaryRational.decode (extractPrefix x)
def power (x : List Bool) : ℚ := BinaryRational.decode (extractPrefix (discardPrefix x))
def count : List Bool → List Bool := discardPrefix ∘ discardPrefix
noncomputable def threshold_computes : PolyComputes (fun x=>BinaryRational.encode (threshold x)) :=
  RatOps.ofWords extractPrefix_computes
noncomputable def power_computes : PolyComputes (fun x=>BinaryRational.encode (power x)) :=
  RatOps.ofWords (discardPrefix_computes.comp extractPrefix_computes)
noncomputable def count_computes : PolyComputes count := discardPrefix_computes.comp discardPrefix_computes

def step (K : ℚ) (x : List Bool) : List Bool :=
  if threshold x ≤ power x then x else
    pairBits (extractPrefix x,pairBits (BinaryRational.encode (K*power x),true::count x))
noncomputable def step_computes (K : ℚ) : PolyComputes (step K) := by
  have hi := (const_computes [true]).append count_computes
  have hh := (RatOps.le threshold_computes power_computes).cond id_computes
    (extractPrefix_computes.pair ((RatOps.mul (RatOps.const K) power_computes).pair hi))
  unfold step
  simpa only [List.singleton_append,decide_eq_true_eq,id_eq] using hh
lemma step_pack (K Z : ℚ) (q : ℕ) :
    step K (pack Z (K^q) q)=pack Z (K^(next K Z q)) (next K Z q) := by
  simp only [step,threshold,power,count,Function.comp_apply,pack,
    extractPrefix_pairBits,discardPrefix_pairBits,BinaryRational.decode_encode,next]
  split_ifs <;> simp only [pow_succ,List.replicate_succ,mul_comm]

lemma iterate_pack (K Z : ℚ) (hK : 1 < K) (hZ : 0 < Z) (j : ℕ) :
    (step K)^[j] (pack Z 1 0)=
      pack Z (K^(min j (exponent K Z))) (min j (exponent K Z)) := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply',ih,step_pack,next_min K Z hK hZ]

lemma pack_length (Z w : ℚ) (q : ℕ) :
    (pack Z w q).length=2*(BinaryRational.encode Z).length+2*(BinaryRational.encode w).length+q+2 := by
  simp only [pack,pairBits_length,List.length_replicate]
  omega

def coefficient (K : ℚ) (C : ℕ) : ℕ := 6*C*(BinaryRational.encode K).length+C+16
noncomputable def cap (K : ℚ) (C : ℕ) : PolynomialCounter
    (Polynomial.C (coefficient K C)*(Polynomial.X+1)) := PolynomialCounter.choose _
noncomputable def fuel (C : ℕ) : PolynomialCounter
    (Polynomial.C C*(Polynomial.X+1)) := PolynomialCounter.choose _

lemma iterate_length (K Z : ℚ) (hK : 1 < K) (hZ : 0 < Z) (C j : ℕ)
    (hj : j ≤ C*((BinaryRational.encode Z).length+1)) :
    ((step K)^[j] (pack Z 1 0)).length ≤
      coefficient K C*((BinaryRational.encode Z).length+1) := by
  rw [iterate_pack K Z hK hZ,pack_length]
  have hm : min j (exponent K Z) ≤ C*((BinaryRational.encode Z).length+1) :=
    (min_le_left _ _).trans hj
  have hp := BinaryRational.encode_height ((BinaryRational.input_height K).pow (min j (exponent K Z)))
  have ht := Nat.mul_le_mul_right (BinaryRational.encode K).length hm
  dsimp only [coefficient]
  nlinarith

def initial (x : List Bool) : List Bool := pairBits (x,pairBits (BinaryRational.encode 1,[]))
noncomputable def initial_computes : PolyComputes initial :=
  id_computes.pair ((const_computes (BinaryRational.encode 1)).pair (const_computes []))
noncomputable def iterated (K : ℚ) (C : ℕ) (x : List Bool) : List Bool :=
  BoundedIteration.run (step K) (pairBits ((fuel C).word x,pairBits ((cap K C).word x,initial x)))
noncomputable def iterated_computes (K : ℚ) (C : ℕ) : PolyComputes (iterated K C) :=
  ((fuel C).computes.pair ((cap K C).computes.pair initial_computes)).comp
    (BoundedIteration.run_computes (step_computes K))

lemma iterated_encode (K Z : ℚ) (hK : 1 < K) (hZ : 0 < Z) (C : ℕ) (hC : 2 ≤ K^C) :
    iterated K C (BinaryRational.encode Z)=pack Z (K^(exponent K Z)) (exponent K Z) := by
  have he := exponent_bound K Z hK hZ C (BinaryRational.encode Z).length hC
    (BinaryRational.input_height Z).le_bound
  have hinit : initial (BinaryRational.encode Z)=pack Z 1 0 := rfl
  simp only [iterated,hinit]
  rw [BoundedIteration.run_eq,iterate_pack K Z hK hZ,(fuel C).word_length]
  · simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    rw [Nat.min_eq_right (by nlinarith : exponent K Z ≤ C*((BinaryRational.encode Z).length+1))]
  · intro j hj
    rw [(cap K C).word_length]
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    apply iterate_length K Z hK hZ C j
    simpa only [(fuel C).word_length,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one] using hj

noncomputable def run (K : ℚ) (C : ℕ) (x : List Bool) : List Bool := true::count (iterated K C x)
noncomputable def run_computes (K : ℚ) (C : ℕ) : PolyComputes (run K C) := by
  have hh := (const_computes [true]).append ((iterated_computes K C).comp count_computes)
  unfold run
  simpa only [Function.comp_def,List.singleton_append] using hh
lemma run_encode (v Z : ℚ) (hv : 0 < v) (hZ : 0 < Z) (C : ℕ) (hC : 2 ≤ (1+v^2)^C) :
    run (1+v^2) C (BinaryRational.encode Z)=List.replicate (HistoryPhaseBound.limit v Z) true := by
  have hK : 1 < 1+v^2 := by nlinarith
  simp only [run,iterated_encode _ Z hK hZ C hC,count,Function.comp_apply,pack,discardPrefix_pairBits]
  rw [←to_limit,List.replicate_succ]

end MetricKMedianRecovery.BitMachine.BinaryPhaseFuel

end OAI
