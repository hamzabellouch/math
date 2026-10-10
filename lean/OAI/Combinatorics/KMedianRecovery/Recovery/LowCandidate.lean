import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.OptimumClusterSeparation
import OAI.Combinatorics.KMedianRecovery.Recovery.RecoveryTrialUniformExponential
import OAI.Combinatorics.KMedianRecovery.Recovery.AllBad

namespace OAI

namespace MetricKMedianRecovery.IntegralCandidates
open LocalSearch Anchoring Completion Sampling Surplus
variable {V : Type*} [MetricSpace V] [LinearOrder V] [Fintype V]

theorem low_candidate (δ : V → V → ℕ) (F D : Finset V) (k L M N : ℕ) (v : ℝ)
    (hD : D.Nonempty) (hL : 0 < L) (hk : 2*L < k) (hkF : k ≤ F.card)
    (hN : N = D.card+F.card) (hM : 0 < M)
    (hδ : ∀ p ∈ D, ∀ i ∈ F, (δ p i : ℝ) = dist p i)
    (hfar : ∀ i ∈ F, ∀ p ∈ D, 1 ≤ dist i p)
    (hdiam : ∀ p ∈ D, ∀ i ∈ F, δ p i ≤ M)
    (hv : 0 < v) (hv1 : v ≤ 1/12)
    (hvc : v ≤ strictnessGap (200*countConstant (1/100))/1000)
    (hsmall : v^2 ≤ strictnessGap (200*countConstant (1/100))/(6*(200*countConstant (1/100)+2)))
    (hsize : 2/(N:ℝ) ≤ strictnessGap (200*countConstant (1/100))/200)
    (herror : (N:ℝ)^2/2^N ≤ v)
    (hfree : 3*(HistoryPhaseBound.limit v ((M:ℝ)+8*(D.card:ℝ)*(M:ℝ))+1) ≤ L) :
    ∃ S : Finset V, S ⊆ F ∧ S.Nonempty ∧ S.card = k ∧ WidthLocalMin F D S 5 ∧
      ∀ xi : ℝ, 0 ≤ xi → xi ≤ 1 →
        optimum F D (k-2*L) ≤ (1+xi)*optimum F D k →
        cost D S ≤ (2-strictnessGap (200*countConstant (1/100))/100)*(1+xi)*optimum F D k := by
  obtain ⟨S,hSF,hS,hSc,hlocal,hcost⟩ := PhaseSurplusProducer.produce δ F D (k-L) L M N v
    hD (by omega) (by omega) hN hM hδ hfar hdiam hv hv1 hvc hsmall hsize herror hfree
  have hcard : S.card = k := by omega
  refine ⟨S,hSF,hS,hcard,hlocal,?_⟩
  intro xi hxi hxi1 hsens
  have hF : F.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨O,hOF,hO,hOc,hOcost⟩ := optimum_attained_exact F D hF (k-L) (by omega) (by omega)
  obtain ⟨H,hHF,hH,hHc,hHcost⟩ := optimum_attained_exact F D hF (k-2*L) (by omega) (by omega)
  have hanti : optimum F D k ≤ cost D O := by
    rw [hOcost]
    exact optimum_antitone F D hF (by omega) (by omega)
  have hHO : cost D H ≤ (1+xi)*cost D O := by
    rw [hHcost]
    exact hsens.trans (mul_le_mul_of_nonneg_left hanti (by linarith))
  have hSO := hcost O H xi hOF hOc hHF hH (by omega) hHO hxi1
  have hOH : cost D O ≤ optimum F D (k-2*L) := by
    rw [hOcost]
    exact optimum_antitone F D hF (by omega) (by omega)
  have hT : 0 < 200*countConstant (1/100) := by
    have hC := PhaseSurplusProducer.countConstant_ge_ten
    linarith
  have hc := strictnessGap_le_one hT
  calc
    cost D S ≤ (2-strictnessGap (200*countConstant (1/100))/100)*cost D O := hSO
    _ ≤ (2-strictnessGap (200*countConstant (1/100))/100)*((1+xi)*optimum F D k) :=
      mul_le_mul_of_nonneg_left (hOH.trans hsens) (by linarith)
    _ = _ := by ring

end MetricKMedianRecovery.IntegralCandidates
namespace MetricKMedianRecovery.IntegralAssembly
open LocalSearch Anchoring Completion Sampling Surplus FiniteSampling IntegralCandidates

noncomputable def gamma : ℝ := min (3/100) (strictnessGap (200*countConstant (1/100))/100)

lemma gamma_pos : 0 < gamma := by
  have hT : 0 < 200*countConstant (1/100) := by
    have hC := PhaseSurplusProducer.countConstant_ge_ten
    linarith
  exact lt_min (by norm_num) (div_pos (strictnessGap_pos hT) (by norm_num))
lemma gamma_le_coarse : gamma ≤ 3/100 := min_le_left _ _
lemma gamma_le_strict : gamma ≤ strictnessGap (200*countConstant (1/100))/100 := min_le_right _ _
lemma gamma_lt_one : gamma < 1 := lt_of_le_of_lt gamma_le_coarse (by norm_num)

theorem finite_experiment : ∃ c : ℝ, 0 < c ∧
    ∀ (V : Type*) [MetricSpace V] [LinearOrder V] [Fintype V],
    ∀ (δ : V → V → ℕ) (F D : Finset V) (k L L0 M N : ℕ) (v xi ζ : ℝ),
    D.Nonempty → 0 < k → 0 < L → k ≤ F.card → N = D.card+F.card → 0 < M →
    (∀ p ∈ D, ∀ i ∈ F, (δ p i : ℝ) = dist p i) →
    (∀ x, ∀ i ∈ F, dist x i ≤ M) →
    (∀ i ∈ F, ∀ p ∈ D, 1 ≤ dist i p) →
    0 < v → v ≤ 1/12 → v ≤ strictnessGap (200*countConstant (1/100))/1000 →
    v^2 ≤ strictnessGap (200*countConstant (1/100))/(6*(200*countConstant (1/100)+2)) →
    (2*L < k → 2/(N:ℝ) ≤ strictnessGap (200*countConstant (1/100))/200) →
    (2*L < k → (N:ℝ)^2/2^N ≤ v) →
    3*(HistoryPhaseBound.limit v ((M:ℝ)+8*(D.card:ℝ)*(M:ℝ))+1) ≤ L →
    0 < xi → xi ≤ 1 → 2*L ≤ L0 → 4*countConstant (1/100)*L/xi ≤ L0 →
    0 < ζ → ∀ n : ℕ, Real.log (1/ζ)/Real.exp (-c*L0) ≤ (n:ℝ) →
    ∃ run : RecoverySeed D F M L0 (D.card*M) n → Finset V,
      (∀ seed, run seed ⊆ F ∧ (run seed).Nonempty ∧ (run seed).card ≤ k ∧
        cost D (run seed) ≤ 5*optimum F D k) ∧
      1-ζ ≤ probability (fun seed => cost D (run seed) ≤ (2-gamma)*(1+xi)*optimum F D k) ∧
      average (fun seed => cost D (run seed)) ≤
        ((2-gamma)*(1+xi)+5*ζ)*optimum F D k := by
  classical
  obtain ⟨c,hc,hsuccess⟩ := Comparison.recoveryAll_uniform_guarantees
  refine ⟨c,hc,?_⟩
  intro V _ _ _ δ F D k L L0 M N v xi ζ hD hk hL hkF hN hM hδ hbound hfar hv hv1 hvc hsmall hsize herror hfree hxi hxi1 hL0 hcount hζ n hn
  have hdiam (p : V) (hp : p ∈ D) (i : V) (hi : i ∈ F) : δ p i ≤ M := by
    exact_mod_cast (hδ p hp i hi ▸ hbound p i hi)
  have hsep (p : V) (hp : p ∈ D) (i : V) (hi : i ∈ F) : (1:ℝ) ≤ dist p i := by
    rw [dist_comm]
    exact hfar i hi p hp
  have hint (p : V) (hp : p ∈ D) (i : V) (hi : i ∈ F) : ∃ d : ℕ, dist p i = (d:ℝ) :=
    ⟨δ p i,(hδ p hp i hi).symm⟩
  have hF : F.Nonempty := Finset.card_pos.mp (hk.trans_le hkF)
  have hP := optimum_nonneg F D k
  have hcoef : (197/100:ℝ) ≤ (2-gamma)*(1+xi) := by
    have hg := gamma_le_coarse
    have hg1 := gamma_lt_one
    nlinarith
  have hcoef0 : 0 ≤ (2-gamma)*(1+xi) := by linarith
  have hexperiment : ∃ run : RecoverySeed D F M L0 (D.card*M) n → Finset V,
      (∀ seed, run seed ⊆ F ∧ (run seed).Nonempty ∧ (run seed).card ≤ k ∧
        cost D (run seed) ≤ 5*optimum F D k) ∧
      1-ζ ≤ probability (fun seed => cost D (run seed) ≤ (2-gamma)*(1+xi)*optimum F D k) := by
    by_cases hsmallk : k ≤ 2*L
    · obtain ⟨S,hSF,hS,hSk,_,hScost⟩ := local_anchor δ F D k M hk hkF hδ hdiam
      let run := recoveryAll D F S hD hSF hS M (by positivity) hbound L0 (D.card*M) n
      refine ⟨run,?_,?_⟩
      · intro seed
        obtain ⟨hRF,hRc,hR,hcost⟩ := recoveryAll_feasible D F S hD hSF hS M
          (by positivity) hbound L0 (D.card*M) n seed
        rw [realCost_eq,realCost_eq] at hcost
        exact ⟨hRF,hR,hSk ▸ hRc,hcost.trans hScost⟩
      · obtain ⟨O,hOF,hO,hOk,hOcost⟩ := optimum_attained_exact F D hF k hk hkF
        let C := allBad D S O hO (hSk.trans hOk.symm)
        have hbad : C.bad.card ≤ L0 := by
          rw [allBad_count,hOk]
          exact hsmallk.trans hL0
        have hp := (hsuccess V C hD F hSF hOF hS M (by omega) hbound hsep hint L0 hbad ζ hζ n hn).1
        refine hp.trans (probability_mono (fun seed hs => ?_))
        rw [realCost_eq] at hs
        have he : comparisonCost D C.assign = optimum F D k := by
          exact (comparisonCost_nearest D O hO).trans hOcost
        rw [he] at hs
        exact hs.trans (mul_le_mul_of_nonneg_right hcoef hP)
    · have hlarge : 2*L < k := by omega
      obtain ⟨S,hSF,hS,hSk,hlocal,hlow⟩ := low_candidate δ F D k L M N v
        hD hL hlarge hkF hN hM hδ hfar hdiam hv hv1 hvc hsmall (hsize hlarge) (herror hlarge) hfree
      have hanchors : ∀ r : Fin k, ∃ A : Finset V,
          A ⊆ F ∧ A.Nonempty ∧ A.card = r.val+1 ∧ WidthLocalMin F D A 5 ∧
            cost D A ≤ 5*optimum F D (r.val+1) := by
        intro r
        exact local_anchor δ F D (r.val+1) M (by omega) (by omega) hδ hdiam
      choose A hAF hA hAc hAlocal hAcost using hanchors
      let call (r : Fin k) := recoveryAll D F (A r) hD (hAF r) (hA r) M
          (by positivity) hbound L0 (D.card*M) n
      let run (seed : RecoverySeed D F M L0 (D.card*M) n) :=
        enumeratedBest (cost D) S (fun r : Fin k => call r seed)
      have hle (seed : RecoverySeed D F M L0 (D.card*M) n) :=
        enumeratedBest_le (cost D) S (fun r : Fin k => call r seed)
      have hScost : cost D S ≤ 5*optimum F D k := by
        obtain ⟨O,hOF,hO,hOk,hOcost⟩ := optimum_attained F D hF k hk
        simpa only [hOcost] using local_five_approx F D S O hS hO hSF hlocal hOF (hSk ▸ hOk)
      refine ⟨run,?_,?_⟩
      · intro seed
        have hbudget : run seed ⊆ F ∧ (run seed).Nonempty ∧ (run seed).card ≤ k := by
          rcases enumeratedBest_mem (cost D) S (fun r : Fin k => call r seed) with he | ⟨r,he⟩
          · dsimp only [run]
            rw [he]
            exact ⟨hSF,hS,hSk.le⟩
          · dsimp only [run]
            rw [he]
            have hh := recoveryAll_feasible D F (A r) hD (hAF r) (hA r) M
              (by positivity) hbound L0 (D.card*M) n seed
            exact ⟨hh.1,hh.2.2.1,hh.2.1.trans (by rw [hAc]; omega)⟩
        exact ⟨hbudget.1,hbudget.2.1,hbudget.2.2,(hle seed).1.trans hScost⟩
      · by_cases hsens : optimum F D (k-2*L) ≤ (1+xi)*optimum F D k
        · have hcost : ∀ seed, cost D (run seed) ≤ (2-gamma)*(1+xi)*optimum F D k := by
            intro seed
            refine (hle seed).1.trans ((hlow xi hxi.le hxi1 hsens).trans ?_)
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (by linarith [gamma_le_strict]) (by linarith)) hP
          rw [probability_congr (fun seed => iff_true_intro (hcost seed))]
          simp only [probability,ite_true,average_const]
          linarith
        · obtain ⟨h,hlo,hhi,_,hopt,O,hO,hOF,hOc,hOcost,hseparation⟩ :=
            Sensitivity.sensitive_optimum F D hF k L hL hlarge hkF xi hxi hxi1 (lt_of_not_ge hsens)
          let r : Fin k := ⟨h-1,by omega⟩
          have hr : (A r).card = h := by rw [hAc]; dsimp [r]; omega
          have hP1 := PhaseSurplusProducer.comparison_ge_one F D O hD hO hOF hfar
          have hbeta : 0 < xi/(4*(L:ℝ)) := by positivity
          obtain ⟨C,hassign,hbad⟩ := separated_comparison F D O (A r) hO (hA r) (by omega)
            hOF (hAF r) (hr.trans hOc.symm) (hAlocal r) (xi/(4*L)) hbeta (by linarith) hseparation
          have hbad' : C.bad.card ≤ L0 := by
            have he : countConstant (1/100)/(xi/(4*(L:ℝ))) = 4*countConstant (1/100)*L/xi := by
              rw [div_div_eq_mul_div]
              ring
            rw [he] at hbad
            exact_mod_cast hbad.trans hcount
          have hp := (hsuccess V C hD F (hAF r) hOF (hA r) M (by omega)
            hbound hsep hint L0 hbad' ζ hζ n hn).1
          refine hp.trans (probability_mono (fun seed hs => ?_))
          rw [realCost_eq,hassign,comparisonCost_nearest,hOcost] at hs
          calc
            cost D (run seed) ≤ cost D (call r seed) := (hle seed).2 r
            _ ≤ (197/100:ℝ)*optimum F D h := hs
            _ ≤ (197/100:ℝ)*((1+xi)*optimum F D k) := mul_le_mul_of_nonneg_left hopt (by norm_num)
            _ ≤ (2-gamma)*(1+xi)*optimum F D k := by
              have hh : (197/100:ℝ) ≤ 2-gamma := by linarith [gamma_le_coarse]
              have hm := mul_le_mul_of_nonneg_right hh (mul_nonneg (by linarith : 0 ≤ 1+xi) hP)
              simpa only [mul_assoc] using hm
  obtain ⟨run,hfeasible,hprob⟩ := hexperiment
  refine ⟨run,hfeasible,hprob,?_⟩
  have hfail : probability (fun seed => (2-gamma)*(1+xi)*optimum F D k < cost D (run seed)) ≤ ζ := by
    rw [show (fun seed => (2-gamma)*(1+xi)*optimum F D k < cost D (run seed)) =
      (fun seed => ¬cost D (run seed) ≤ (2-gamma)*(1+xi)*optimum F D k) from by
        funext seed; exact propext not_le.symm,probability_compl]
    linarith
  calc
    average (fun seed => cost D (run seed)) ≤ (2-gamma)*(1+xi)*optimum F D k +
        probability (fun seed => (2-gamma)*(1+xi)*optimum F D k < cost D (run seed))*(5*optimum F D k) :=
      average_le_threshold_add_failure _ (mul_nonneg hcoef0 hP) (fun seed => (hfeasible seed).2.2.2)
    _ ≤ (2-gamma)*(1+xi)*optimum F D k + ζ*(5*optimum F D k) := by
      gcongr
    _ = _ := by ring

end MetricKMedianRecovery.IntegralAssembly

end OAI
