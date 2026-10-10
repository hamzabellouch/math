import Mathlib
import OAI.Combinatorics.KMedianRecovery.Algorithms.IntegralDispatchGuarantee

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralAll
open LocalSearch Anchoring Completion Sampling Sampling.Comparison FiniteSampling IntegralAssembly IntegralCandidates Surplus
attribute [local irreducible] output BinaryIntegralDispatch.output BinaryIntegralDispatch.budget
  BinaryIntegralRecovery.Guesses.budget BinaryIntegralRecovery.Guesses.output BinaryMetricAnchor.run

lemma finite_program (A : ℝ) (e : ℕ) : ∃ Q : Polynomial ℕ, ∃ d : ℕ,
    ∀ {n : ℕ} [MetricSpace (Fin n)]
    (δ : Fin n→Fin n→ℕ) (_hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F : Finset (Fin n)) (k L M N C : ℕ) (v : ℚ)
    (_hD : D.Nonempty) (_hk : 0<k) (_hL : 0<L) (_hkF : k≤ F.card)
    (_hN : N=D.card+F.card) (_hM : 0<M)
    (_hcap : M≤ Rounding.cap D.card (gamma/16))
    (_hbound : ∀ x,∀ f∈F,δ x f≤ M) (_hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤ dist w f)
    (_hv : (0:ℝ)<(v:ℝ)) (_hv1 : (v:ℝ)≤ 1/12)
    (_hvc : (v:ℝ)≤ strictnessGap (200*countConstant (1/100))/1000)
    (_hsmall : (v:ℝ)^2≤ strictnessGap (200*countConstant (1/100))/(6*(200*countConstant (1/100)+2)))
    (_hsize : 2*L<k→ 2/(N:ℝ)≤ strictnessGap (200*countConstant (1/100))/200)
    (_herror : 2*L<k→ (N:ℝ)^2/2^N≤ (v:ℝ))
    (_hfree : 3*(HistoryPhaseBound.limit v ((M:ℝ)+8*(D.card:ℝ)*(M:ℝ))+1)≤ L)
    (_hC : 2≤ (1+v^2)^C) (g : List Bool) (_hg : N≤ g.length)
    (_hlog : (countBound L:ℝ)≤ A*Real.log ((N:ℝ)+2)),
    let δQ := fun i j=>(δ i j:ℚ)
    let K := (Dsp.budget Q).eval (Dsp.pack δQ D F M k g []).length
    ∃ S : Finset (Fin n),
      (∀ seed:Fin K→Bool,run v C Q d (Dsp.pack δQ D F M k g (List.ofFn seed))=
        BinaryFinSet.encode (output v C Q d δQ D F S M k g (List.ofFn seed))) ∧
      (∀ seed:Fin K→Bool,output v C Q d δQ D F S M k g (List.ofFn seed)⊆F ∧
        (output v C Q d δQ D F S M k g (List.ofFn seed)).Nonempty ∧
        (output v C Q d δQ D F S M k g (List.ofFn seed)).card≤ k ∧
        realCost D (output v C Q d δQ D F S M k g (List.ofFn seed))≤ 5*optimum F D k) ∧
      (1-FailureBudget.failure gamma e N≤ probability
        (fun seed:Fin K→Bool=>realCost D (output v C Q d δQ D F S M k g (List.ofFn seed))≤
          (2-gamma)*(1+gamma/16)*optimum F D k)) ∧
      average (fun seed:Fin K→Bool=>realCost D (output v C Q d δQ D F S M k g (List.ofFn seed)))≤
        ((2-gamma)*(1+gamma/16)+5*FailureBudget.failure gamma e N)*optimum F D k := by
  obtain ⟨Q,d,hd⟩:=BinaryIntegralDispatch.designated_recovery A e
  refine ⟨Q,d,?_⟩
  intro n _ δ hδ D F k L M N CC v hD hk hL hkF hN hM hcap hbound hsep hv hv1 hvc hsmall hsize herror hfree hCC g hg hlog
  dsimp only
  let δQ := fun i j=>(δ i j:ℚ)
  let K := (Dsp.budget Q).eval (Dsp.pack δQ D F M k g []).length
  have hδQ : ∀ i j,(δQ i j:ℝ)=dist i j := by intro i j;simpa only [δQ,Rat.cast_natCast] using hδ i j
  have hcap' (p:Fin n) (_hp:p∈D) (i:Fin n) (hi:i∈F) : δ p i≤ Rounding.cap D.card (gamma/16) :=
    (hbound p i hi).trans hcap
  obtain ⟨S,hs,hSF,hS,hSk,hlocal,hScost⟩:=BinaryMetricAnchor.produce δ hδ D F k hk hkF hcap'
  have hF : F.Nonempty := Finset.card_pos.mp (hk.trans_le hkF)
  obtain ⟨O0,hO0F,hO0,hO0k,hO0cost⟩:=optimum_attained F D hF k hk
  have hbaseline : realCost D S≤ 5*optimum F D k := by
    rw [realCost_eq]
    simpa only [hO0cost] using hScost O0 hO0 hO0F hO0k
  let V (seed:Fin K→Bool) := output v CC Q d δQ D F S M k g (List.ofFn seed)
  have hpoint (seed:Fin K→Bool) : realCost D (V seed)≤ 5*optimum F D k :=
    (cost_le_start v CC Q d δQ hδQ D F S M k g (List.ofFn seed) hSF hS hSk.le).trans hbaseline
  have hP := optimum_nonneg F D k
  have hxi : (0:ℝ)<gamma/16 := div_pos gamma_pos (by norm_num)
  have hxi1 : gamma/16≤ (1:ℝ) := by linarith [gamma_lt_one]
  have hcoef : (197/100:ℝ)≤ 2-gamma := by linarith [gamma_le_coarse]
  have hcoef0 : (0:ℝ)≤ (2-gamma)*(1+gamma/16) := by have hh:=gamma_lt_one;positivity
  have hrec (r:ℕ) (T O:Finset (Fin n)) (B:Comparison D T O)
      (hr:r≤F.card) (hTF:T⊆F) (hT:T.Nonempty) (hTk:T.card≤k) (hOF:O⊆F)
      (ht:BinaryMetricAnchor.run (BinaryMetricAnchor.pack δQ D F r)=BinaryFinSet.encode T)
      (hb:(B.bad.card:ℝ)≤ A*Real.log ((N:ℝ)+2))
      (hbCost:comparisonCost D B.assign≤ (1+gamma/16)*optimum F D k) :
      1-FailureBudget.failure gamma e N≤ probability (fun seed:Fin K→Bool=>realCost D (V seed)≤
        (2-gamma)*(1+gamma/16)*optimum F D k) := by
    have hcall:=hd δ hδ D F S T O B hD k r hr hSF hS hSk.le hTF hT hTk hOF hs ht M hM hcap hbound hsep N g hg hb
    have hp:=lift_probability v CC Q d δQ hδQ D F S M k g hSF hS hSk.le hs
      ((197/100:ℝ)*comparisonCost D B.assign) (1-FailureBudget.failure gamma e N) hcall.2.2.1
    exact hp.trans (probability_mono (fun seed hh=>hh.trans (by
      calc
        (197/100:ℝ)*comparisonCost D B.assign≤(197/100:ℝ)*((1+gamma/16)*optimum F D k) :=
          mul_le_mul_of_nonneg_left hbCost (by norm_num)
        _≤(2-gamma)*(1+gamma/16)*optimum F D k := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoef (mul_nonneg (by linarith) hP))))
  have hp : 1-FailureBudget.failure gamma e N≤ probability (fun seed:Fin K→Bool=>realCost D (V seed)≤
      (2-gamma)*(1+gamma/16)*optimum F D k) := by
    by_cases hsmallk : k≤2*L
    · obtain ⟨O,hOF,hO,hOk,hOcost⟩:=optimum_attained_exact F D hF k hk hkF
      let B := allBad D S O hO (hSk.trans hOk.symm)
      apply hrec k S O B hkF hSF hS hSk.le hOF hs
      · apply le_trans _ hlog
        have hh : B.bad.card≤countBound L := by rw [allBad_count,hOk];exact hsmallk.trans (le_max_left _ _)
        exact_mod_cast hh
      · have he : comparisonCost D B.assign=optimum F D k := (comparisonCost_nearest D O hO).trans hOcost
        rw [he];nlinarith
    · have hlarge : 2*L<k := by omega
      by_cases hsens : optimum F D (k-2*L)≤(1+gamma/16)*optimum F D k
      · obtain ⟨U,hu,hUF,hU,hUk,_,hlow⟩:=BinaryMetricSurplus.low_candidate δ F D k L M N CC v hD hL hlarge hkF hN hM hδ
          (fun i hi p hp=>by rw [dist_comm];exact hsep p hp i hi) (fun p _ i hi=>hbound p i hi) hcap'
          hv hv1 hvc hsmall (hsize hlarge) (herror hlarge) hfree hCC
        have huCost:=hlow (gamma/16) hxi.le hxi1 hsens
        have hall (seed:Fin K→Bool) : realCost D (V seed)≤ (2-gamma)*(1+gamma/16)*optimum F D k := by
          have he:=cost_le_surplus v CC Q d δQ hδQ D F S M k g (List.ofFn seed) hSF hS hSk.le L (by omega) U hUF hU hUk.le hu
          exact he.trans (by simpa only [realCost_eq] using huCost)
        have he : (fun seed:Fin K→Bool=>realCost D (V seed)≤(2-gamma)*(1+gamma/16)*optimum F D k)=(fun _=>True) := by
          funext seed;exact propext ⟨fun _=>trivial,fun _=>hall seed⟩
        rw [he];simp only [probability,ite_true,average_const]
        linarith [FailureBudget.failure_pos gamma_pos e N]
      · obtain ⟨h,hlo,hhi,_,hopt,O,hO,hOF,hOc,hOcost,hseparation⟩:=
          Sensitivity.sensitive_optimum F D hF k L hL hlarge hkF (gamma/16) hxi hxi1 (lt_of_not_ge hsens)
        obtain ⟨T,ht,hTF,hT,hTc,hTlocal,_⟩:=BinaryMetricAnchor.produce δ hδ D F h (by omega) (by omega) hcap'
        have hP1:=PhaseSurplusProducer.comparison_ge_one F D O hD hO hOF
          (fun i hi p hp=>by rw [dist_comm];exact hsep p hp i hi)
        have hbeta : (0:ℝ)<(gamma/16)/(4*L) := by positivity
        obtain ⟨B,hassign,hbad⟩:=separated_comparison F D O T hO hT (by omega) hOF hTF
          (hTc.trans hOc.symm) hTlocal ((gamma/16)/(4*L)) hbeta (by linarith) hseparation
        apply hrec h T O B (by omega) hTF hT (by omega) hOF ht
        · apply le_trans _ hlog
          have he : countConstant (1/100)/((gamma/16)/(4*(L:ℝ)))=4*countConstant (1/100)*L/(gamma/16) := by rw [div_div_eq_mul_div];ring
          rw [he] at hbad
          exact hbad.trans ((Nat.le_ceil _).trans (by exact_mod_cast (le_max_right (2*L) ⌈4*countConstant (1/100)*(L:ℝ)/(gamma/16)⌉₊)))
        · rw [hassign,comparisonCost_nearest,hOcost]
          exact hopt
  refine ⟨S,fun seed=>run_output v CC Q d δQ D F S M k g (List.ofFn seed) hs,?_,hp,?_⟩
  · intro seed
    have hh:=output_feasible v CC Q d δQ D F S M k g (List.ofFn seed) hSF hS hSk.le
    exact ⟨hh.1,hh.2.1,hh.2.2,hpoint seed⟩
  · have hf : probability (fun seed:Fin K→Bool=>(2-gamma)*(1+gamma/16)*optimum F D k<realCost D (V seed))≤
        FailureBudget.failure gamma e N := by
      have he : probability (fun seed:Fin K→Bool=>(2-gamma)*(1+gamma/16)*optimum F D k<realCost D (V seed))=
          1-probability (fun seed:Fin K→Bool=>realCost D (V seed)≤(2-gamma)*(1+gamma/16)*optimum F D k) := by
        rw [←probability_compl];exact probability_congr (fun _=>not_le.symm)
      rw [he];linarith
    have hm:=average_le_threshold_add_failure (fun seed:Fin K→Bool=>realCost D (V seed)) (B := (2-gamma)*(1+gamma/16)*optimum F D k) (mul_nonneg hcoef0 hP) hpoint
    exact hm.trans (by nlinarith [mul_le_mul_of_nonneg_right hf (mul_nonneg (by norm_num : (0:ℝ)≤5) hP)])
end MetricKMedianRecovery.BitMachine.BinaryIntegralAll

end OAI
