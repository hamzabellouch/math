import OAI.NumberTheory.DirichletL.Descent.CanonicalRankExistenceData
import OAI.NumberTheory.DirichletL.Descent.CanonicalRankFamilyGates

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseMoment
open MeasureTheory ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion InverseInitialClippedColumns InverseReflectedPhase InverseTerminalWidths
open CanonicalCubeSeparation CompletedHeight InverseMomentFirstSecondHeightCost
local notation "O"=>ActualEisensteinCubic.O

theorem rank_energy_exists_succ_of_reference
    (n:ℕ)(L cstar cutoff eta:ℝ)(K:ℕ)
    (hL:1≤L)(hcstar:0<cstar)(hcut:0<cutoff)(hcutL:cutoff≤L)
    (hcutc:cutoff≤cstar/200)(heta:0<eta)(heta1:eta≤1)
    (hetac:eta≤cstar/100000)(hetad:eta≤cutoff/32)
    (hIH:∀(W:𝓢(ℝ,ℂ))(lo hi:ℝ),0<lo→0≤hi→
      Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi→RankEnergyExists n L cstar cutoff eta K W)
    (W:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hhi:0≤hi)
    (hsW:Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi)
    (Vlog:𝓢(ℝ,ℂ))(Alog:ℝ)(hbox:∀x,Vlog x≠0→|x|≤Alog)
    (hone:∀x,|x|≤columnWindowRadius lo hi→Vlog x=1)
    (hlarge:∀window:ℝ,∃Zt:ℝ,1<Zt ∧ ∀Z:ℝ,Zt≤Z→
      2≤Z ∧ 2≤Z^eta ∧ Real.exp 1≤Z^eta ∧ 1≤eta*Real.log Z ∧
      hi≤Z^eta ∧ Real.exp Alog≤Z^eta ∧ Real.exp window≤Z^eta):
    RankEnergyExists (n+1) L cstar cutoff eta K W :=by
  have hL0:0≤L:=by linarith
  have heF:0<firstPassEpsilon L eta:=by unfold firstPassEpsilon;positivity
  have hem:0<sourceMassEpsilon L eta:=by unfold sourceMassEpsilon;positivity
  obtain ⟨w11,w12,w21,w22,af1,bf1,af2,bf2,window,bw,ds,ha1,hab1,ha2,hab2,
    hw11,hw12,hw21,hw22,hs11,hs12,hs21,hs22,hbw,hbA,hbexp,hstep⟩:=
    actual_complete_normalized_rank_step lo hi hlo hhi W hsW (W.smooth ⊤) Vlog Alog hbox hone
      L cstar eta eta 1 (sourceMassEpsilon L eta) (sourceMassEpsilon L eta) eta
      hL hcstar heta heta1 hetac heta heta1 hem hem heta K
  obtain ⟨J11,B11,hB11,ih11⟩:=hIH w11 af1 bf1 ha1 (by linarith) (subset_closure.trans hs11)
  obtain ⟨J12,B12,hB12,ih12⟩:=hIH w12 af1 bf1 ha1 (by linarith) (subset_closure.trans hs12)
  obtain ⟨J21,B21,hB21,ih21⟩:=hIH w21 af2 bf2 ha2 (by linarith) (subset_closure.trans hs21)
  obtain ⟨J22,B22,hB22,ih22⟩:=hIH w22 af2 bf2 ha2 (by linarith) (subset_closure.trans hs22)
  let J:=J11+J12+J21+J22
  let dl:=2*(InverseClippingProfiles.momentOrder (firstDegree J)+(volume:Measure ℝ).integrablePower)
  let Jout:=max ds dl
  let B:=1+hi+B11+B12+B21+B22
  have hB:1≤B:=by dsimp [B];linarith
  have hb0:0≤B:=by linarith
  have hhiB:hi≤B:=by dsimp [B];linarith
  have hBB11:B11≤B:=by dsimp [B];linarith
  have hBB12:B12≤B:=by dsimp [B];linarith
  have hBB21:B21≤B:=by dsimp [B];linarith
  have hBB22:B22≤B:=by dsimp [B];linarith
  have hj11:J11≤J:=by dsimp [J];omega
  have hj12:J12≤J:=by dsimp [J];omega
  have hj21:J21≤J:=by dsimp [J];omega
  have hj22:J22≤J:=by dsimp [J];omega
  obtain ⟨Zt,hZt,hlarge⟩:=hlarge window
  refine ⟨Jout,B,hB,?_⟩
  intro q hq
  obtain ⟨C11,Z11,hC11,hZ11,ih11⟩:=ih11 q hq
  obtain ⟨C12,Z12,hC12,hZ12,ih12⟩:=ih12 q hq
  obtain ⟨C21,Z21,hC21,hZ21,ih21⟩:=ih21 q hq
  obtain ⟨C22,Z22,hC22,hZ22,ih22⟩:=ih22 q hq
  obtain ⟨Cs,Cb,Zs,hCs,hCb,hZs,hstep⟩:=hstep (firstPassEpsilon L eta) eta heF heta J q hq
  let A:=C11+C12+C21+C22
  have hA:0≤A:=by dsimp [A];linarith
  have hCA11:C11≤A:=by dsimp [A];linarith
  have hCA12:C12≤A:=by dsimp [A];linarith
  have hCA21:C21≤A:=by dsimp [A];linarith
  have hCA22:C22≤A:=by dsimp [A];linarith
  let C:=(Cs+Cb)*(1+A)
  let Z₀:=Zs+Zt+Z11+Z12+Z21+Z22
  have hC:0<C:=by dsimp [C];positivity
  have hZ₀:1<Z₀:=by dsimp [Z₀];linarith
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ D hD σ _ slots hslots lists H a hdis hH hP ha z hz hprod base hbase hperiod
  have hZs':Zs≤Z:=by dsimp [Z₀] at hZ;linarith
  have hZt':Zt≤Z:=by dsimp [Z₀] at hZ;linarith
  have hZ11':Z11≤Z:=by dsimp [Z₀] at hZ;linarith
  have hZ12':Z12≤Z:=by dsimp [Z₀] at hZ;linarith
  have hZ21':Z21≤Z:=by dsimp [Z₀] at hZ;linarith
  have hZ22':Z22≤Z:=by dsimp [Z₀] at hZ;linarith
  obtain ⟨hZ2,h2,hExp,hlog,hhiZ,hAZ,hwin⟩:=hlarge Z hZt'
  have hZ1:1<Z:=by linarith
  have hZ0:0<Z:=by linarith
  have hD11:B11*Z^L≤D:=(mul_le_mul_of_nonneg_right hBB11 (Real.rpow_nonneg hZ0.le _)).trans hD
  have hD12:B12*Z^L≤D:=(mul_le_mul_of_nonneg_right hBB12 (Real.rpow_nonneg hZ0.le _)).trans hD
  have hD21:B21*Z^L≤D:=(mul_le_mul_of_nonneg_right hBB21 (Real.rpow_nonneg hZ0.le _)).trans hD
  have hD22:B22*Z^L≤D:=(mul_le_mul_of_nonneg_right hBB22 (Real.rpow_nonneg hZ0.le _)).trans hD
  have m11:=ih11 Z hZ11' D hD11 slots hslots lists H a hdis hH hP ha z hz hprod base hbase hperiod
  have m12:=ih12 Z hZ12' D hD12 slots hslots lists H a hdis hH hP ha z hz hprod base hbase hperiod
  have m21:=ih21 Z hZ21' D hD21 slots hslots lists H a hdis hH hP ha z hz hprod base hbase hperiod
  have m22:=ih22 Z hZ22' D hD22 slots hslots lists H a hdis hH hP ha z hz hprod base hbase hperiod
  let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) D (reflectionExcludedPrimes_bad q)
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only [CompletePoolRankMoments] at m11 m12 m21 m22 ⊢
  intro Ψ hΨ m hm N V M Qwidth hN hV hM hQ hMc hFc hmargin hnorm ss hss labels hlabels theta
  have hcap:N+V≤L:=by
    unfold rankTotalCap at hFc
    have hh:0≤15*((n+1:ℕ):ℝ)*eta:=by positivity
    linarith
  have hcm:0≤rankMargin (n+1) cstar eta:=by unfold rankMargin;positivity
  obtain ⟨hNL,hVL,hMF,hQL,hzL,hwidth,hmargin',hmL,hpuncture⟩:=
    actual_rank_state_gates m hm Z N V M Qwidth z (rankMargin (n+1) cstar eta) L
      hZ1 hN hV hM hQ hz hcm hcap hmargin hnorm
  obtain ⟨hΨnorm,hΨperiod⟩:=actual_rank_family_gates q base hbase hperiod Ψ hΨ
  have hDparent:hi*Z^N≤D:=by
    calc
      _≤B*Z^L:=mul_le_mul hhiB (Real.rpow_le_rpow_of_exponent_le hZ1.le hNL)
        (Real.rpow_nonneg hZ0.le _) hb0
      _≤D:=hD
  have hsscard:ss.card≤K:=(Finset.card_le_card hss).trans hslots
  have hssdis:(ss:Set σ).PairwiseDisjoint lists:=by
    intro i hi j hj hij
    exact hdis (hss hi) (hss hj) hij
  have hssH:∀i∈ss,1≤H i:=fun i hi=>hH i (hss hi)
  have hssP:∀i∈ss,∀P∈lists i,(Ideal.absNorm P.val:ℝ)≤H i:=fun i hi=>hP i (hss hi)
  have hssa:∀i∈ss,∀P∈lists i,‖a i P‖≤1:=fun i hi=>ha i (hss hi)
  have hssprod:(∏i∈ss,H i)≤Z^z:=canonical_rank_subslot_cap slots ss H Z z hss hH hprod
  obtain ⟨hsmallM,hsmallF,hsmallc⟩:=actual_rank_successor_caps n L cstar cutoff eta M (N+V)
    (rankMargin (n+1) cstar eta) hMc hFc le_rfl
  have lift (w:𝓢(ℝ,ℂ))(Cw:ℝ)(Jw:ℕ)(hCw:0≤Cw)(hCwA:Cw≤A)(hJw:Jw≤J)
      (mw:CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ base slots lists a w Z (rankRowCap n cutoff)
        (rankTotalCap n L eta) z (rankMargin n cstar eta) (rankLoss n eta) Cw K Jw):
      CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ base ss lists a w Z (M-3*(cutoff/2)/2)
        (N+V+15*eta) z (rankMargin (n+1) cstar eta-7*eta) (rankLoss n eta) A K J:=by
    apply canonical_rank_subslots (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ base slots ss lists a w Z _ _ z _ _ A K J hss
    apply canonical_rank_restrict (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ base slots lists a w Z
      (M-3*(cutoff/2)/2) (rankRowCap n cutoff) (N+V+15*eta) (rankTotalCap n L eta)
      z (rankMargin (n+1) cstar eta-7*eta) (rankMargin n cstar eta) (rankLoss n eta) A K J
      (by linarith) hsmallF hsmallc
    exact canonical_rank_height_constant (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ base slots lists a w Z _ _ z _ _ Cw A K Jw J
      hZ0 hCw hCwA hJw mw
  have hechild:0≤rankLoss n eta:=by unfold rankLoss;positivity
  obtain ⟨_,_,hpieta,hmass,hret,hprincipal0,hcost⟩:=actual_step_parameters L eta 0 0 (rankLoss n eta)
    hL0 heta heta1 (by linarith) (by linarith) hechild
  obtain ⟨hprincipal,hFirst,hFinal⟩:=actual_complete_step_cost L eta (rankLoss n eta) hL0 heta heta1 hechild
  have hreserve:cstar/2≤rankMargin (n+1) cstar eta:=by
    unfold rankMargin
    exact le_add_of_nonneg_right (by positivity)
  have hbound:=hstep m hm Z N V M z (rankMargin (n+1) cstar eta) cutoff (8*eta)
    (rankLoss n eta) A (rankLoss n eta+58*eta) (rankLoss n eta+60*eta) theta
    hZs' hZ2 h2 hExp hlog hN hV hM hcap hMF hzL hhiZ hAZ hwin hcut hcutL hcutc hetad hmL hmargin'
    hreserve (by simpa only [hwidth] using hpuncture) (by positivity) hpieta hmass hmass hechild
    (by linarith) hret hprincipal hcost (by linarith) hA
    labels (fun I hI=>⟨⟨(hlabels I hI).1.1,(hlabels I hI).1.2.2⟩,(hlabels I hI).1.2.1,(hlabels I hI).2⟩)
    D hDparent ss hsscard lists H hssdis hssH hssP hssprod base Ψ hΨ hΨnorm hΨperiod a hssa
    (lift w11 C11 J11 hC11.le hCA11 hj11 m11) (lift w12 C12 J12 hC12.le hCA12 hj12 m12)
    (lift w21 C21 J21 hC21.le hCA21 hj21 m21) (lift w22 C22 J22 hC22.le hCA22 hj22 m22)
  have hnextLoss:rankLoss n eta+62*eta=rankLoss (n+1) eta:=by unfold rankLoss;push_cast;ring
  have hlongexp:(rankLoss n eta+60*eta)+2*L*firstPassEpsilon L eta+eta≤rankLoss (n+1) eta:=by
    simpa only [hnextLoss] using hFinal
  have hloss0:0≤rankLoss (n+1) eta:=by unfold rankLoss;positivity
  have hlong:Cb*(1+A)*(1+‖theta‖)^dl*
      Z^(N+V+(rankLoss n eta+60*eta)+2*L*firstPassEpsilon L eta+eta)≤
      Cb*(1+A)*(1+‖theta‖)^dl*Z^(N+V+rankLoss (n+1) eta):=by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hZ1.le
    linarith
  have hh:=hbound.trans (add_le_add le_rfl hlong)
  have hmrg:=actual_complete_height_merge ds dl Z (N+V) cstar (rankLoss (n+1) eta) Cs Cb A theta
    hZ1.le hcstar.le hloss0 hCs.le hCb hA
  have hpow:(1+‖theta‖)^Jout≤(1+‖theta‖)^(2*Jout):=
    pow_le_pow_right₀ (by linarith [norm_nonneg theta]) (by omega)
  have hf:childLogTest W theta=normTwistedSource W theta:=by
    funext y
    simp only [childLogTest,normTwistedSource,mul_comm]
  rw [hf]
  apply (hh.trans hmrg).trans
  dsimp only [C,Jout]
  have hx:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (show 0≤(Cs+Cb)*(1+A) by positivity))
    (Real.rpow_nonneg hZ0.le (N+V+rankLoss (n+1) eta))
  convert hx using 1 ; ring

end SevenEighths.InverseMoment

end

end OAI
