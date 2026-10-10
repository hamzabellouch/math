import Mathlib
import OAI.Combinatorics.KMedianRecovery.Algorithms.IntegralAll

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch
open Completion Sampling Sampling.Comparison FiniteSampling
attribute [local irreducible] output BinaryIntegralRecovery.Guesses.output
  BinaryIntegralRecovery.Repeat.output budget BinaryIntegralRecovery.Guesses.budget
  BinaryIntegralRecovery.Fair.pack BinaryMetricAnchor.run

lemma designated_recovery (A : ℝ) (e : ℕ) : ∃ Q : Polynomial ℕ, ∃ d : ℕ,
    ∀ {n : ℕ} [PseudoMetricSpace (Fin n)]
    (δ : Fin n→ Fin n→ℕ) (_hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S T O : Finset (Fin n)) (C : Comparison D T O) (_hD : D.Nonempty)
    (k r : ℕ) (_hr : r≤ F.card) (_hSF : S⊆F) (_hS : S.Nonempty) (_hSk : S.card≤ k)
    (_hTF : T⊆F) (_hT : T.Nonempty) (_hTk : T.card≤ k) (_hOF : O⊆F)
    (_hs : BinaryMetricAnchor.run (BinaryMetricAnchor.pack (fun i j=>(δ i j:ℚ)) D F k)=BinaryFinSet.encode S)
    (_ht : BinaryMetricAnchor.run (BinaryMetricAnchor.pack (fun i j=>(δ i j:ℚ)) D F r)=BinaryFinSet.encode T)
    (Δ : ℕ) (_hΔ : 1≤Δ) (_hcap : Δ≤ Rounding.cap D.card (IntegralAssembly.gamma/16))
    (_hbound : ∀ x,∀ f∈F,δ x f≤Δ) (_hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤ dist w f)
    (N : ℕ) (g : List Bool) (_hN : N≤ g.length) (_hlog : (C.bad.card:ℝ)≤ A*Real.log ((N:ℝ)+2)),
    let δQ := fun i j=>(δ i j:ℚ)
    let K := (budget Q).eval (pack δQ D F Δ k g []).length
    (∀ seed:Fin K→ Bool,run Q d (pack δQ D F Δ k g (List.ofFn seed))=
      BinaryFinSet.encode (output Q d δQ D F S Δ k g (List.ofFn seed))) ∧
    (∀ seed:Fin K→ Bool,output Q d δQ D F S Δ k g (List.ofFn seed)⊆F ∧
      (output Q d δQ D F S Δ k g (List.ofFn seed)).Nonempty ∧
      (output Q d δQ D F S Δ k g (List.ofFn seed)).card≤ k ∧
      realCost D (output Q d δQ D F S Δ k g (List.ofFn seed))≤ realCost D S) ∧
    (1-FailureBudget.failure IntegralAssembly.gamma e N≤ probability
      (fun seed:Fin K→ Bool=>realCost D (output Q d δQ D F S Δ k g (List.ofFn seed))≤
        (197/100:ℝ)*comparisonCost D C.assign)) ∧
    average (fun seed:Fin K→ Bool=>realCost D (output Q d δQ D F S Δ k g (List.ofFn seed)))≤
      (197/100:ℝ)*comparisonCost D C.assign+realCost D S*FailureBudget.failure IntegralAssembly.gamma e N := by
  obtain ⟨Q,d,hd⟩:=BinaryIntegralRecovery.Guesses.integral_recovery A e
  refine ⟨Q,d,?_⟩
  intro n _ δ hδ D F S T O C hD k r hr hSF hS hSk hTF hT hTk hOF hs ht Δ hΔ hcap hbound hsep N g hN hlog
  dsimp only
  let δQ := fun i j=>(δ i j:ℚ)
  let KT := (R.budget Q).eval (R.pack δQ D F T Δ g []).length
  let K := (budget Q).eval (pack δQ D F Δ k g []).length
  have hKT : KT≤ K := demand_bound Q δQ D F T Δ k g r hr ht
  have hδQ : ∀ i j,(δQ i j:ℝ)=dist i j := by intro i j; simpa only [δQ,Rat.cast_natCast] using hδ i j
  obtain ⟨htrace,hgood,hprob,_⟩:=hd δ hδ D F T O C hD hTF hOF hT Δ hΔ hcap hbound hsep N g hN hlog
  let sub (seed:Fin K→ Bool) : Fin KT→ Bool := fun i=>seed (Fin.castLE hKT i)
  let U (seed:Fin KT→ Bool) := BinaryIntegralRecovery.Guesses.output Q d δQ D F T Δ g (List.ofFn seed)
  let V (seed:Fin K→ Bool) := output Q d δQ D F S Δ k g (List.ofFn seed)
  have hcall (seed:Fin K→ Bool) : call Q d (pairBits (pack δQ D F Δ k g (List.ofFn seed),r.bits))=
      BinaryFinSet.encode (U (sub seed)) := by
    rw [call_pack Q d δQ D F T Δ k g (List.ofFn seed) r ht,take_ofFn_cast hKT]
    exact htrace (sub seed)
  have hle (seed:Fin K→ Bool) : realCost D (V seed)≤ realCost D (U (sub seed)) := by
    have hh:=hgood (sub seed)
    exact cost_le_call Q d δQ hδQ D F S Δ k g (List.ofFn seed) hSF hS hSk r hr
      (U (sub seed)) hh.1 hh.2.1 (hh.2.2.1.trans hTk) (hcall seed)
  have hpoint (seed:Fin K→ Bool) : realCost D (V seed)≤ realCost D S :=
    cost_le_start Q d δQ hδQ D F S Δ k g (List.ofFn seed) hSF hS hSk
  have hp : 1-FailureBudget.failure IntegralAssembly.gamma e N≤ probability
      (fun seed:Fin K→ Bool=>realCost D (V seed)≤(197/100:ℝ)*comparisonCost D C.assign) := by
    apply le_trans hprob
    rw [←probability_prefix hKT (fun seed:Fin KT→ Bool=>realCost D (U seed)≤(197/100:ℝ)*comparisonCost D C.assign)]
    exact probability_mono (fun seed hh=>(hle seed).trans hh)
  refine ⟨fun seed=>run_output Q d δQ D F S Δ k g (List.ofFn seed) hs,?_,hp,?_⟩
  · intro seed
    have hh:=output_feasible Q d δQ D F S Δ k g (List.ofFn seed) hSF hS hSk
    exact ⟨hh.1,hh.2.1,hh.2.2,hpoint seed⟩
  · have hP := C.comparison_cost_positive hD F hOF hsep
    have hbase : (0:ℝ)≤ realCost D S := by
      rw [realCost,dite_eq_left hS]
      exact Finset.sum_nonneg (fun _ _=>distanceTo_nonneg _ _ _)
    have hf : probability (fun seed:Fin K→ Bool=>(197/100:ℝ)*comparisonCost D C.assign<realCost D (V seed))≤
        FailureBudget.failure IntegralAssembly.gamma e N := by
      have he : probability (fun seed:Fin K→ Bool=>(197/100:ℝ)*comparisonCost D C.assign<realCost D (V seed))=
          1-probability (fun seed:Fin K→ Bool=>realCost D (V seed)≤(197/100:ℝ)*comparisonCost D C.assign) := by
        rw [←probability_compl]
        exact probability_congr (fun _=>not_le.symm)
      rw [he]; linarith
    exact (average_le_threshold_add_failure (B := (197/100:ℝ)*comparisonCost D C.assign) (fun seed:Fin K→ Bool=>realCost D (V seed)) (by positivity) hpoint).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hf hbase])
end MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralAll
open Completion Sampling Sampling.Comparison FiniteSampling
attribute [local irreducible] output BinaryIntegralDispatch.output BinaryIntegralDispatch.budget
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
lemma lift_probability (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ)
    (hδ : ∀ i j,(δ i j:ℝ)=dist i j) (D F S : Finset (Fin n)) (Δ k : ℕ) (g : List Bool)
    (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤k)
    (hs : BinaryMetricAnchor.run (BinaryMetricAnchor.pack δ D F k)=BinaryFinSet.encode S)
    (B p : ℝ) (hp : p≤ probability (fun seed:Fin ((Dsp.budget Q).eval (Dsp.pack δ D F Δ k g []).length)→ Bool=>
      realCost D (BinaryIntegralDispatch.output Q d δ D F S Δ k g (List.ofFn seed))≤ B)) :
    p≤ probability (fun seed:Fin ((Dsp.budget Q).eval (Dsp.pack δ D F Δ k g []).length)→ Bool=>
      realCost D (output v C Q d δ D F S Δ k g (List.ofFn seed))≤ B) :=
  hp.trans (probability_mono (fun seed hh=>(cost_le_dispatch v C Q d δ hδ D F S Δ k g (List.ofFn seed) hSF hS hSk hs).trans hh))
end MetricKMedianRecovery.BitMachine.BinaryIntegralAll

namespace MetricKMedianRecovery.BitMachine.BinaryMetricSurplus
open LocalSearch Anchoring Surplus
variable {n : ℕ} [MetricSpace (Fin n)]
attribute [local irreducible] run BinaryCanonicalSurplus.run
lemma low_candidate (δ : Fin n→ Fin n→ℕ) (F D : Finset (Fin n))
    (k L M N C : ℕ) (v : ℚ) (hD : D.Nonempty) (hL : 0<L) (hk : 2*L<k) (hkF : k≤ F.card)
    (hN : N=D.card+F.card) (hM : 0<M) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (hfar : ∀ i∈F,∀ p∈D,1≤ dist i p) (hdiam : ∀ p∈D,∀ i∈F,δ p i≤ M)
    (hcap : ∀ p∈D,∀ i∈F,δ p i≤ Rounding.cap D.card (IntegralAssembly.gamma/16))
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)≤1/12)
    (hvc : (v:ℝ)≤ strictnessGap (200*countConstant (1/100))/1000)
    (hsmall : (v:ℝ)^2≤ strictnessGap (200*countConstant (1/100))/(6*(200*countConstant (1/100)+2)))
    (hsize : 2/(N:ℝ)≤ strictnessGap (200*countConstant (1/100))/200)
    (herror : (N:ℝ)^2/2^N≤(v:ℝ))
    (hfree : 3*(HistoryPhaseBound.limit v ((M:ℝ)+8*(D.card:ℝ)*(M:ℝ))+1)≤ L)
    (hC : 2≤(1+v^2)^C) :
    ∃ S : Finset (Fin n),run v C (pack (fun i j=>(δ i j:ℚ)) D F M (k-L) L)=BinaryFinSet.encode S ∧
      S⊆F ∧ S.Nonempty ∧ S.card=k ∧ WidthLocalMin F D S 5 ∧
      ∀ xi : ℝ,0≤ xi→ xi≤1→ optimum F D (k-2*L)≤(1+xi)*optimum F D k→
        cost D S≤(2-IntegralAssembly.gamma)*(1+xi)*optimum F D k := by
  have hsymm (i j : Fin n) : δ i j=δ j i := by exact_mod_cast ((hδ i j).trans ((dist_comm i j).trans (hδ j i).symm))
  obtain ⟨S,he,hSF,hS,hSc,hlocal,hcost⟩:=BinaryCanonicalSurplus.produce (fun i j=>δ j i) F D
    (k-L) L M N C v hD (by omega) (by omega) hN hM
    (fun p _ i _=>(hδ i p).trans (dist_comm _ _)) (fun i j=>hδ i (SortedIndex.enum D j)) hfar
    (fun p hp i hi=>by rw [hsymm];exact hdiam p hp i hi)
    (fun p hp i hi=>by rw [hsymm];exact hcap p hp i hi)
    hv hv1 hvc hsmall hsize herror hfree hC
  have hcard : S.card=k := by omega
  refine ⟨S,?_,hSF,hS,hcard,hlocal,?_⟩
  · rw [run_pack];exact he
  intro xi hxi hxi1 hsens
  have hF : F.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨O,hOF,_,hOc,hOcost⟩:=optimum_attained_exact F D hF (k-L) (by omega) (by omega)
  obtain ⟨H,hHF,hH,hHc,hHcost⟩:=optimum_attained_exact F D hF (k-2*L) (by omega) (by omega)
  have hanti : optimum F D k≤ cost D O := by
    rw [hOcost];exact optimum_antitone F D hF (by omega) (by omega)
  have hHO : cost D H≤(1+xi)*cost D O := by
    rw [hHcost];exact hsens.trans (mul_le_mul_of_nonneg_left hanti (by linarith))
  have hSO:=hcost O H xi hOF hOc hHF hH (by omega) hHO hxi1
  have hOH : cost D O≤ optimum F D (k-2*L) := by
    rw [hOcost];exact optimum_antitone F D hF (by omega) (by omega)
  have hT : 0<200*countConstant (1/100) := by linarith [PhaseSurplusProducer.countConstant_ge_ten]
  have hc:=strictnessGap_le_one hT
  have hP:=optimum_nonneg F D k
  calc
    cost D S≤(2-strictnessGap (200*countConstant (1/100))/100)*cost D O := hSO
    _≤(2-strictnessGap (200*countConstant (1/100))/100)*((1+xi)*optimum F D k) :=
      mul_le_mul_of_nonneg_left (hOH.trans hsens) (by linarith)
    _≤(2-IntegralAssembly.gamma)*(1+xi)*optimum F D k := by
      have hg:=IntegralAssembly.gamma_le_strict
      nlinarith [mul_le_mul_of_nonneg_right (by linarith : 2-strictnessGap (200*countConstant (1/100))/100≤2-IntegralAssembly.gamma)
        (mul_nonneg (by linarith : 0≤1+xi) hP)]
end MetricKMedianRecovery.BitMachine.BinaryMetricSurplus

end OAI
