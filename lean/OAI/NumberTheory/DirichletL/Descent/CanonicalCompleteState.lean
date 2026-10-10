import OAI.NumberTheory.DirichletL.Descent.CanonicalShortFinite
import OAI.NumberTheory.DirichletL.Descent.CanonicalLongTotal

namespace OAI

noncomputable section

open scoped BigOperators Classical ContDiff
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve InverseReflectedPhase InverseTerminalWidths CompletedHeight
open InverseCanonicalShortAttachment InverseSecondFibers FirstPassCubeLabels SecondPassArithmetic
local notation "O"=>ActualEisensteinCubic.O
universe v

theorem actual_complete_state_from_live_bins
    (lo hi:ℝ)(hlo:0<lo)(hhi:0≤hi)(W:ℝ→ℂ)
    (hWs:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W)
    (L cstar eta eps:ℝ)(hL:0≤L)(hcstar:0<cstar)(heta:0<eta)
    (heta1:eta≤1)(hetac:eta≤cstar/100000)(heps:0<eps)(rmax K:ℕ) :
    ∃degree:ℕ,∀(q:ℕ)(_hq:q≠0),∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀{σ:Type v}[DecidableEq σ](m:O),m≠0 → ∀Z N V M z₀ margin cutoff:ℝ,
      Z₀≤Z → 0≤N → N≤L → 0≤V → V≤L → 0≤M → M≤L → z₀≤L →
      0≤cutoff → cutoff≤L → cutoff≤cstar/200 →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
    ∀labels:Finset (Ideal O),(∀I∈labels,Supported I ∧ Squarefree I ∧ (I.absNorm:ℝ)≤Z^V) →
    ∀D:ℕ,hi*Z^N≤D → ∀slots:Finset σ,slots.card≤rmax →
    ∀(lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))(H:σ→ℝ),
      (slots:Set σ).Pairwise (fun i j=>Disjoint (lists i) (lists j)) →
      (∀i∈slots,1≤H i) → (∀i∈slots,∀P∈lists i,(Ideal.absNorm P.val:ℝ)≤H i) → (∏i∈slots,H i)≤Z^z₀ →
    ∀(Ψ:O→*ℂ),(∀u,‖Ψ u‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀(theta:ℝ)(a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ),
      (∀i∈slots,∀P∈lists i,‖a i P‖≤1) → ∀E:ℝ,0≤E →
      let S:=reflectionExcludedPrimes q;
      let test:=normTwistedSource W theta;
      (∀j∈cubeLogRange hi (Z^N),
        (progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D hi (Z^N) j)).Nonempty →
        Z^(-V)*rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
          (progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D hi (Z^N) j))
          Ψ m (idealGenerator I) z test (Z^N) (Z^(cutoff-V)) slots lists a) (Z^M)≤E) →
      Z^(-(N+V))*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 (Z^M),
        ‖outsideCanonicalMarkedRow S D (reflectionExcludedPrimes_bad q) Ψ m (idealGenerator I) z
          slots lists a test (Z^N)‖^2)≤
      C*((1+‖theta‖)^degree*Z^(N+V-cstar/256)+Z^eps*E) := by
  obtain ⟨degree,hs⟩:=actual_complete_short_finite_uniform_degree lo hi hlo W hWs hW L cstar eta
    hL hcstar heta heta1 hetac rmax K
  obtain ⟨Cl,hCl,hl⟩:=actual_complete_energy_from_live_bins K hi L eps hhi hL heps
  refine ⟨degree,?_⟩
  intro q hq
  obtain ⟨Cs,Z₀,hCs,hZ₀,hshort⟩:=hs q hq
  refine ⟨2*Cs+Cl,Z₀,by positivity,hZ₀,?_⟩
  intro σ _ m hm Z N V M z₀ margin cutoff hZ hN hNL hV hVL hM hML hzL hcut hcutL hcutc
    hmN hmargin hreserve labels hlabels D hD slots hcard lists H hdis hH1 hH hprod Ψ hΨ hperiod theta a ha E hE
  dsimp only
  intro hbins
  have hz:0<Z:=zero_lt_one.trans (lt_of_lt_of_le hZ₀ hZ)
  have hZ1:1≤Z:=(hZ₀.trans_le hZ).le
  let S:=reflectionExcludedPrimes q
  let test:=normTwistedSource W theta
  let mark:=indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a
  have htest:HasCompactSupport test:=HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((normTwistedSource_support W theta).trans hWs)
  have hupper:∀x,test x≠0 → x≤hi:=fun x hx=>(hWs (normTwistedSource_support W theta hx)).2
  have hT:∀z∈nonzeroChildFrequencyBall 1 (Z^M),z≠0 ∧ (Ideal.absNorm (Ideal.span {z}):ℝ)≤Z^M := by
    intro z hz
    have hh:=(mem_nonzeroChildFrequencyBall 1 one_ne_zero (Z^M) z).mp hz
    constructor
    · intro he
      simp only [he,mul_zero,map_zero,norm_zero,pow_succ,lt_self_iff_false] at hh
      exact hh.1
    · rw [←eisEmbedding_norm_sq_eq_absNorm_span]
      simpa only [one_mul] using hh.2
  have hshortbound:Z^(-V)*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 (Z^M),
      ‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z)
        test (Z^N) (Z^(cutoff-V)) mark‖^2)≤Cs*(1+‖theta‖)^degree*Z^(N+V-cstar/256) := by
    by_cases hbig:cutoff≤V
    · have he (I:Ideal O)(z:O):markedShortCompletedSum
          (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z) test (Z^N) (Z^(cutoff-V)) mark=0:=
        short_sum_zero_of_label_large _ _ _ _ _ _ _ hZ1 hbig
      simp only [he,norm_zero,zero_pow (by decide:2≠0),Finset.sum_const_zero,mul_zero]
      positivity
    · exact hshort m hm Z N V M z₀ margin (cutoff-V) cutoff hZ hN hV hM hML hVL hzL
        (by linarith) (by linarith) hmN hmargin hreserve (by linarith) (by linarith) hcutc
        labels hlabels (nonzeroChildFrequencyBall 1 (Z^M)) hT D hD slots hcard lists H
        hdis hH1 hH hprod Ψ hΨ hperiod theta a ha
  have hb:=hl S D (reflectionExcludedPrimes_bad q) (reflectionExcludedPrimes_prime q) labels
    (fun I hI=>(hlabels I hI).1.1) Ψ m slots lists a test htest Z N V (Z^M)
    (Z^(cutoff-V)) (Cs*(1+‖theta‖)^degree*Z^(N+V-cstar/256)) E
    hZ1 (Real.rpow_pos_of_pos hz _) hNL hVL (fun I hI=>(hlabels I hI).2.2)
    hupper hD hE hshortbound hbins
  apply hb.trans
  have hA:0≤(1+‖theta‖)^degree*Z^(N+V-cstar/256):=by positivity
  have hB:0≤Z^eps*E:=by positivity
  nlinarith

end SevenEighths.InverseMoment

end

end OAI
