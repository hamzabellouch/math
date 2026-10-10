import OAI.Computability.RandomMean.Realizer

namespace OAI

section
namespace MeanPayoff.Realizer
open TreeDevice TreeDevice.Certified BinaryData RandomTree
noncomputable def iterations (d : Digits) : ℕ := 2^(Preparation.exponent d).length
 theorem iterations_bound (G : Game) : SourceControl.rootControlBound G ≤ iterations ⟨input G⟩ := by
  rw [iterations,Preparation.exponent_length]
  exact SourceControl.rootControlBound_nat G
 theorem root_game (G : Game) : Preparation.root ⟨input G⟩=
    ((RootCode.exponent (InputCode.game G),RootCode.samples (InputCode.game G)),
      (InputCode.width (InputCode.game G),(RootCode.env (InputCode.game G),RootCode.state (InputCode.game G)))) := by
  simp only [Preparation.root,Code.comp_eval,InputCode.parse_game,Code.pair_eval]
 theorem aux_game (G : Game) : aux ⟨input G⟩=
    ((RootCode.exponent (InputCode.game G),RootCode.samples (InputCode.game G)),
      List.replicate (iterations ⟨input G⟩) (),
      (InputCode.width (InputCode.game G),(RootCode.env (InputCode.game G),RootCode.state (InputCode.game G)))) := by
  rw [aux,Preparation.aux,root_game]
  rfl
 theorem amount_game (G : Game) : amount ⟨input G⟩=sampleExponent (topWidth G).toNat*iterations ⟨input G⟩ := by
  rw [amount,Preparation.bits_length,root_game]
  rw [RootCode.exponent_length]
  rfl
 theorem answer_eval (d : Digits) (bs : List Bool) : answer d bs=
    PostCode.classify ((aux d).2.2.1,
      (RawControl.loop ((aux d).2.2.2,PostCode.samples (⟨bs⟩,aux d))).2.1.2.q) := by
  simp only [answer,PostCode.run,Code.comp_eval,PostCode.execute_eval,PostCode.returned_eval,PostCode.digits_eval]
 theorem answer_game (G : Game) (bs : List Bool) (hl : bs.length=amount ⟨input G⟩) :
    answer ⟨input G⟩ bs.reverse=
      PostCode.classify (InputCode.width (InputCode.game G),
        (RawControl.loop ((RootCode.env (InputCode.game G),RootCode.state (InputCode.game G)),
          Chunks.decode (sampleExponent (topWidth G).toNat) (iterations ⟨input G⟩) bs)).2.1.2.q) := by
  rw [answer_eval,PostCode.samples_eval,aux_game]
  simp only [List.reverse_reverse]
  rw [Chunks.run_exact]
  · rw [RootCode.exponent_length,List.length_replicate]
  · rw [RootCode.exponent_length,RootCode.samples_length]
    rfl
  · rw [RootCode.exponent_length,List.length_replicate,hl,amount_game]
 theorem answer_expect (G : Game) (f : List Bool→ℚ) :
    (FairBits.acc (amount ⟨input G⟩) []).expect (fun bs => f (answer ⟨input G⟩ bs))=
      (gameSolve G).expect (fun out => f (List.ofFn out)) := by
  rw [FairBits.acc_eq,expect_map]
  simp only [Function.comp_def,List.append_nil]
  have hh := expect_congr_all (FairBits.draw (amount ⟨input G⟩))
    (fun bs => f (answer ⟨input G⟩ bs.reverse))
    (fun bs => f (PostCode.classify (InputCode.width (InputCode.game G),
      (RawControl.loop ((RootCode.env (InputCode.game G),RootCode.state (InputCode.game G)),
        Chunks.decode (sampleExponent (topWidth G).toNat) (iterations ⟨input G⟩) bs)).2.1.2.q)))
    (all_mono _ (FairBits.length _) (fun bs hb => congrArg f (answer_game G bs hb)))
  rw [hh,amount_game]
  have he := expect_map (FairBits.draw (sampleExponent (topWidth G).toNat*iterations ⟨input G⟩))
    (Chunks.decode (sampleExponent (topWidth G).toNat) (iterations ⟨input G⟩))
    (fun cs => f (PostCode.classify (InputCode.width (InputCode.game G),
      (RawControl.loop ((RootCode.env (InputCode.game G),RootCode.state (InputCode.game G)),cs)).2.1.2.q)))
  rw [Chunks.decode_law] at he
  exact he.symm.trans (root_loop_law G _ (iterations_bound G) f)
end MeanPayoff.Realizer

end

section
namespace MeanPayoff.Realizer
open RegisterBits BinaryData TreeDevice TreeDevice.Certified
noncomputable def total (K e : ℕ) (d : Digits) : ℕ :=
  2*Compile.bound program d.bits (limit K e d)
 theorem total_formula (K e : ℕ) (d : Digits) :
    total K e d=2*(3*d.bits.length+8+limit K e d*(4*(d.bits.length+limit K e d)+16)) := by
  have hs : storeSize (RegisterBits.initial program d.bits).stack=d.bits.length := by
    simp [storeSize,RegisterBits.initial,Fin.sum_univ_succ]
  simp only [total,Compile.bound,Compile.overhead,hs]
 theorem total_bound (K e : ℕ) : PolyBound Preparation.resource (total K e) := by
  have hl := Preparation.input_bound.mono digits_length
  have hn := limit_bound K e
  apply ((PolyBound.const _ 2).mul
    ((((PolyBound.const _ 3).mul hl).add (PolyBound.const _ 8)).add
      (hn.mul ((((PolyBound.const _ 4).mul (hl.add hn)).add (PolyBound.const _ 16)))))).mono
  intro d
  rw [total_formula]
 theorem resource_quasi (d : Digits) :
    Preparation.resource d+1≤2^(25003*(Nat.clog 2 (d.bits.length+2))^2) := by
  let h := Nat.clog 2 (d.bits.length+2)
  have hh : 1≤h := by
    apply (Nat.lt_clog_iff_pow_lt (by norm_num : 1<2)).mpr
    simp only [pow_zero]
    omega
  have hl : d.bits.length≤2^h := (Nat.le_add_right _ 2).trans (Nat.le_pow_clog (by norm_num) _)
  have he : h≤25000*h^2 := by nlinarith only [hh]
  have hp := hl.trans (Nat.pow_le_pow_right (by norm_num : 1≤2) he)
  have hx : treeSize (encode d)≤4*d.bits.length+1 := by
    change treeSize (listTree boolData d.bits)≤_
    rw [Halve.listTree_boolData]
    exact RandomTable.list_size _
  have hpos : 1≤2^(25000*h^2) := Nat.one_le_pow _ _ (by norm_num)
  calc
    Preparation.resource d+1≤8*2^(25000*h^2) := by
      unfold Preparation.resource
      rw [Preparation.exponent_length]
      change treeSize (encode d)+2^(25000*h^2)+1≤_
      omega
    _ = 2^(25000*h^2+3) := by rw [pow_add]; ring
    _ ≤ 2^(25003*h^2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith only [hh])
 theorem polynomial_quasi {f : Digits→ℕ} (hf : PolyBound Preparation.resource f) :
    ∃ C : ℕ, ∀ d, f d≤2^(C*(Nat.clog 2 (d.bits.length+2))^2) := by
  obtain ⟨K,e,hf⟩ := hf
  refine ⟨K+25003*e,fun d => ?_⟩
  let h := Nat.clog 2 (d.bits.length+2)
  have hh : 1≤h := by
    apply (Nat.lt_clog_iff_pow_lt (by norm_num : 1<2)).mpr
    simp only [pow_zero]
    omega
  have hk : K≤2^K := Nat.lt_two_pow_self.le
  calc
    f d ≤ K*(Preparation.resource d+1)^e := hf d
    _ ≤ 2^K*(2^(25003*h^2))^e := Nat.mul_le_mul hk (Nat.pow_le_pow_left (resource_quasi d) e)
    _ = 2^(K+25003*h^2*e) := by rw [←pow_mul,pow_add]
    _ ≤ 2^((K+25003*e)*h^2) := by
      apply Nat.pow_le_pow_right (by norm_num)
      have hs : 1≤h^2 := by nlinarith
      have hm := Nat.mul_le_mul_left K hs
      nlinarith only [hm]
 theorem natural_quasi_real {f : Digits→ℕ} (C : ℕ)
    (hf : ∀ d, f d≤2^(C*(Nat.clog 2 (d.bits.length+2))^2)) :
    ∃ D : ℝ, 0<D ∧ ∀ d, (f d : ℝ)≤(2 : ℝ)^(D*(Real.logb 2 (d.bits.length+2))^2) := by
  refine ⟨4*C+1,by positivity,fun d => ?_⟩
  have hc := clog_real_le_twice_logb d.bits.length
  have hc0 : (0 : ℝ)≤(Nat.clog 2 (d.bits.length+2) : ℝ) := Nat.cast_nonneg _
  have hl0 : 0≤Real.logb 2 (d.bits.length+2) := by linarith only [hc,hc0]
  have hs : ((Nat.clog 2 (d.bits.length+2) : ℝ))^2≤4*(Real.logb 2 (d.bits.length+2))^2 := by
    nlinarith only [hc,hc0,hl0]
  have hm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg C : (0 : ℝ)≤C)
  have hb : (f d : ℝ)≤(2 : ℝ)^(C*(Nat.clog 2 (d.bits.length+2))^2) := by exact_mod_cast hf d
  apply hb.trans
  rw [←Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
  simp only [Nat.cast_mul,Nat.cast_pow]
  nlinarith only [hm,sq_nonneg (Real.logb 2 (d.bits.length+2))]
 theorem total_quasi (K e : ℕ) : ∃ C : ℝ, 0<C ∧ ∀ d,
    (total K e d : ℝ)≤(2 : ℝ)^(C*(Real.logb 2 (d.bits.length+2))^2) := by
  obtain ⟨C,hC⟩ := polynomial_quasi (total_bound K e)
  exact natural_quasi_real C hC
end MeanPayoff.Realizer

end

section
namespace MeanPayoff.Realizer
open RegisterBits BinaryData TreeDevice TreeDevice.Certified RandomTree
 theorem tree_halts (K e : ℕ) (h : ∀ z, postCost z≤K*(treeSize (encode z)+1)^e) (d : Digits) :
    (tree program (limit K e d) (RegisterBits.initial program d.bits)).All (fun c => c.control=none) := by
  obtain ⟨t,ht,hh,hd,_⟩ := trace K e h d
  exact ht.tree_all hh hd
 theorem tree_answer (K e : ℕ) (h : ∀ z, postCost z≤K*(treeSize (encode z)+1)^e)
    (d : Digits) (f : List Bool→ℚ) :
    (tree program (limit K e d) (RegisterBits.initial program d.bits)).expect (fun c => f c.output)=
      (FairBits.acc (amount d) []).expect (fun bs => f (answer d bs)) := by
  obtain ⟨t,ht,hh,hd,he⟩ := trace K e h d
  refine (ht.expect hh hd (fun c : Config program => f c.output)).trans ?_
  simpa only using he (fun c : Config program => f c.output)
 theorem tree_law (K e : ℕ) (h : ∀ z, postCost z≤K*(treeSize (encode z)+1)^e)
    (G : Game) (f : List Bool→ℚ) :
    (tree program (limit K e ⟨input G⟩) (RegisterBits.initial program (input G))).expect (fun c => f c.output)=
      (gameSolve G).expect (fun out => f (List.ofFn out)) := by
  exact (tree_answer K e h ⟨input G⟩ f).trans (answer_expect G f)
 theorem tree_success (K e : ℕ) (h : ∀ z, postCost z≤K*(treeSize (encode z)+1)^e) (G : Game) :
    7/8≤(tree program (limit K e ⟨input G⟩) (RegisterBits.initial program (input G))).probability
      (fun c => BinaryInput.CorrectList G c.output) := by
  classical
  unfold probability
  rw [tree_law K e h G (fun out => if BinaryInput.CorrectList G out then 1 else 0)]
  simpa only [probability,BinaryInput.correctList_ofFn] using gameSolve_success G

end MeanPayoff.Realizer

end

end OAI
