import Mathlib
import OAI.Combinatorics.KMedianRecovery.Algorithms.GlobalOuter
import OAI.Combinatorics.KMedianRecovery.Algorithms.GlobalRoundMetric

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalOuter
open LocalSearch Completion IntegralAssembly FiniteSampling Sampling.Comparison
attribute [local irreducible] BinaryGlobalCall.run BinaryIntegralAll.run BinaryIntegralDispatch.budget output words budget
lemma run_take (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (I : RationalMetricInput) (M : ℚ) (raw : List Bool) :
    BinaryGlobalCall.run v C Q d (BinaryGlobalCall.pack I M raw)=BinaryGlobalCall.run v C Q d
      (BinaryGlobalCall.pack I M (raw.take ((BinaryGlobalCall.A.budget Q).eval (BinaryGlobalCall.integralPack I M []).length))) := by
  rw [BinaryGlobalCall.run_pack,BinaryGlobalCall.run_pack,List.take_take,min_self]
lemma probability_all {m : ℕ} (E : (Fin m→Bool)→Prop) (h : ∀ seed,E seed) : probability E=1 := by
  unfold probability
  simp only [ite_eq_left (h _),average_const]

theorem finite_program (e : ℕ) : ∃ v : ℚ, ∃ C : ℕ, ∃ Q : Polynomial ℕ, ∃ d : ℕ,
    ∀ I : RationalMetricInput,
      let K := (budget Q).eval I.bits.length
      (∀ seed:Fin K→Bool,(I.cost (output v C Q d I (List.ofFn seed)):ℝ)≤6*(I.optimum:ℝ)) ∧
      1-FailureBudget.failure gamma e I.size≤probability
        (fun seed:Fin K→Bool=>(I.cost (output v C Q d I (List.ofFn seed)):ℝ)≤(2-gamma/2)*(I.optimum:ℝ)) := by
  obtain ⟨v,C,Q,d,hR⟩:=BinaryGlobalRounding.rounded_program e
  refine ⟨v,C,Q,d,?_⟩
  intro I
  dsimp only
  let := I.metric
  let K := (budget Q).eval I.bits.length
  have hp0 : 0≤(I.optimum:ℝ) := by exact_mod_cast I.optimum_nonneg
  have hf0 : 0≤FailureBudget.failure gamma e I.size := (FailureBudget.failure_pos gamma_pos _ _).le
  have hfactor : 0≤2-gamma/2 := by linarith [gamma_lt_one]
  by_cases hD : I.clients.Nonempty
  · obtain ⟨O,hOF,hO,hOk,hOC⟩:=optimum_attained I.facilities I.clients I.facilities_nonempty I.budget I.budget_pos
    rw [I.metric_cost,I.metric_optimum] at hOC
    by_cases hz : (I.optimum:ℝ)=0
    · let Z:=BinaryGlobalZero.output I.distance I.clients I.facilities I.facilities_nonempty
      have hZ:=@BinaryGlobalZero.optimum_zero_spec _ I.metric I.distance (fun _ _=>rfl) I.clients I.facilities
        I.facilities_nonempty I.budget I.budget_pos (by rw [I.metric_optimum,hz])
      have hZF : Z⊆I.facilities := BinaryGlobalZero.output_subset _ _ _ _
      have hZN : Z.Nonempty := BinaryGlobalZero.output_nonempty _ _ _ _ hD
      have hZcost : (I.cost Z:ℝ)=0 := by rw [I.metric_cost] at hZ;exact hZ.2
      have hall (seed:Fin K→Bool) : (I.cost (output v C Q d I (List.ofFn seed)):ℝ)≤0 := by
        apply (cost_le_word v C Q d I (List.ofFn seed) Z hZF hZN hZ.1 ?_).trans_eq hZcost
        rw [words,zero_bits];exact List.mem_cons_self
      constructor
      · intro seed;rw [hz,mul_zero];exact hall seed
      · have he : probability (fun seed:Fin K→Bool=>(I.cost (output v C Q d I (List.ofFn seed)):ℝ)≤(2-gamma/2)*(I.optimum:ℝ))=1 :=
          probability_all _ (fun seed=>by rw [hz,mul_zero];exact hall seed)
        rw [he];linarith
    · have hp : 0<(I.optimum:ℝ) := lt_of_le_of_ne hp0 (Ne.symm hz)
      have hcp : 0<cost I.clients O := by rw [I.metric_cost,hOC];exact hp
      obtain ⟨p,_,f,_,hm,hmP,hPm⟩:=Rounding.largest_guess I.clients O I.facilities hD hO hOF hcp
      let M:=I.distance p f
      have hM : 0<M := by
        have hm' : (0:ℝ)<(M:ℝ) := hm
        exact_mod_cast hm'
      obtain ⟨U,hRun,hFeas,hBounds⟩:=hR I hD M hM
      have hMP : (M:ℝ)≤(I.cost O:ℝ) := by
        rw [I.metric_cost] at hmP
        exact hmP
      have hPM : (I.cost O:ℝ)≤I.clients.card*(M:ℝ) := by
        rw [I.metric_cost] at hPm
        exact hPm
      obtain ⟨hAll,hProb⟩:=hBounds O hOF hO hOk hMP hPM
      let k:=(BinaryGlobalCall.A.budget Q).eval (BinaryGlobalCall.integralPack I M []).length
      have hk : k≤K := demand_bound Q I M (flat_mem I p f)
      let sub (seed:Fin K→Bool) : Fin k→Bool := fun i=>seed (Fin.castLE hk i)
      have hCall (seed:Fin K→Bool) : BinaryGlobalCall.run v C Q d (BinaryGlobalCall.pack I M (List.ofFn seed))=BinaryFinSet.encode (U (sub seed)) := by
        have hh:=run_take v C Q d I M (List.ofFn seed)
        rw [take_ofFn_cast hk] at hh
        exact hh.trans (hRun (sub seed))
      have hle (seed:Fin K→Bool) : (I.cost (output v C Q d I (List.ofFn seed)):ℝ)≤(I.cost (U (sub seed)):ℝ) := by
        have h:=hFeas (sub seed)
        apply cost_le_word v C Q d I (List.ofFn seed) (U (sub seed)) h.1 h.2.1 h.2.2
        rw [words]
        apply List.mem_cons_of_mem
        exact List.mem_map.mpr ⟨M,flat_mem I p f,hCall seed⟩
      constructor
      · intro seed;exact (hle seed).trans (by rw [←hOC];exact hAll (sub seed))
      · rw [hOC] at hProb
        apply hProb.trans
        rw [←probability_prefix hk (fun seed:Fin k→Bool=>(I.cost (U seed):ℝ)≤(2-gamma/2)*(I.optimum:ℝ))]
        exact probability_mono (fun seed hs=>(hle seed).trans hs)
  · have hd : I.clients=∅ := Finset.not_nonempty_iff_eq_empty.mp hD
    have hc (S : Finset (Fin I.pointCount)) : (I.cost S:ℝ)=0 := by
      simp only [RationalMetricInput.cost,hd,Finset.sum_empty,dite_eq_ite,ite_self,Rat.cast_zero]
    constructor
    · intro seed;rw [hc];positivity
    · rw [probability_all _ (fun seed=>by rw [hc];exact mul_nonneg hfactor hp0)]
      linarith
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalOuter
open IntegralAssembly FiniteSampling Sampling.Comparison
attribute [local irreducible] output run budget
noncomputable def algorithm (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : BinaryRandomizedAlgorithm where
  randomBits := budget Q
  run := fun p=>run v C Q d (pairBits p)
  computation := (run_computes v C Q d).reencode pairBits id (fun _=>rfl)
  finiteWorkAlphabet := by
    intro k
    change Finite Bool
    infer_instance
lemma algorithm_output (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (I : RationalMetricInput)
    (seed : (algorithm v C Q d).Seed I) :
    (algorithm v C Q d).output I seed=output v C Q d I (List.ofFn seed) := by
  change I.decodeOutput (run v C Q d (pairBits (I.bits,List.ofFn seed)))=_
  rw [run_bits,I.decode_outputBits _ (output_feasible v C Q d I (List.ofFn seed)).1]
lemma probability_eq (A : BinaryRandomizedAlgorithm) (I : RationalMetricInput) (B : ℝ) :
    A.successProbability I B=probability (fun seed:A.Seed I=>(I.cost (A.output I seed):ℝ)≤B) := by
  classical
  rw [BinaryRandomizedAlgorithm.successProbability,probability,average,Fintype.expect_eq_sum_div_card]
  simp only [BinaryRandomizedAlgorithm.Seed,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
lemma expected_eq (A : BinaryRandomizedAlgorithm) (I : RationalMetricInput) :
    A.expectedCost I=average (fun seed:A.Seed I=>(I.cost (A.output I seed):ℝ)) := by
  rw [BinaryRandomizedAlgorithm.expectedCost,average,Fintype.expect_eq_sum_div_card]
  simp only [BinaryRandomizedAlgorithm.Seed,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
theorem algorithm_guarantee : globalApplicationClaim := by
  refine ⟨gamma/4,div_pos gamma_pos (by norm_num),?_⟩
  intro a _ha
  obtain ⟨v,C,Q,d,h⟩:=finite_program ⌈a⌉₊
  refine ⟨algorithm v C Q d,?_,?_,?_⟩
  · intro I seed
    rw [algorithm_output]
    have hh:=output_feasible v C Q d I (List.ofFn seed)
    exact ⟨hh.1,hh.2.2,fun _=>hh.2.1⟩
  · intro I
    rw [probability_eq]
    simp only [algorithm_output]
    have hp0 : 0≤(I.optimum:ℝ) := by exact_mod_cast I.optimum_nonneg
    have hf:=FailureBudget.failure_le_power (g:=gamma) (a:=a) gamma_lt_one.le I.size
    apply (sub_le_sub_left hf 1).trans
    apply (h I).2.trans
    exact probability_mono (fun seed hs=>hs.trans (mul_le_mul_of_nonneg_right (by linarith [gamma_pos]) hp0))
  · intro I
    rw [expected_eq]
    simp only [algorithm_output]
    have hp0 : 0≤(I.optimum:ℝ) := by exact_mod_cast I.optimum_nonneg
    have hb0 : 0≤(2-gamma/2)*(I.optimum:ℝ) := mul_nonneg (by linarith [gamma_lt_one]) hp0
    let K := (budget Q).eval I.bits.length
    let X (seed:Fin K→Bool) : ℝ := (I.cost (output v C Q d I (List.ofFn seed)):ℝ)
    have hFail : probability (fun seed:Fin K→Bool=>(2-gamma/2)*(I.optimum:ℝ)<X seed)≤FailureBudget.failure gamma ⌈a⌉₊ I.size := by
      have he : probability (fun seed:Fin K→Bool=>(2-gamma/2)*(I.optimum:ℝ)<X seed)=
          1-probability (fun seed:Fin K→Bool=>X seed≤(2-gamma/2)*(I.optimum:ℝ)) := by
        rw [←probability_compl];exact probability_congr (fun _=>not_le.symm)
      rw [he];have hh:=(h I).2;linarith
    have hAve:=average_le_threshold_add_failure X hb0 (h I).1
    have hζ:=FailureBudget.failure_le_margin gamma_pos.le ⌈a⌉₊ I.size
    have hmargin:=FailureBudget.expectation_margin hp0 hζ
    change average X≤_
    exact hAve.trans (le_trans (by nlinarith [mul_le_mul_of_nonneg_right hFail (mul_nonneg (by norm_num : (0:ℝ)≤6) hp0)]) hmargin)
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
