import OAI.NumberTheory.DirichletL.Descent.CanonicalLongCosts
import OAI.NumberTheory.DirichletL.Descent.CanonicalLongHeightBin

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseMoment
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstLabelCell InverseMomentFirstSecondHeightCost CompletedHeight
open FourierBridge JointLogSeparation InverseReflectedPhase InverseTerminalWidths InverseSecondFibers
local notation "O"=>ActualEisensteinCubic.O

theorem actual_complete_state_from_children
    (lo hi:ℝ)(hlo:0<lo)(hhi:0≤hi)(W:ℝ→ℂ)
    (hsW:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W)
    (Vlog:𝓢(ℝ,ℂ))(Alog:ℝ)(hbox:∀x,Vlog x≠0 → |x|≤Alog)
    (hone:∀x,|x|≤columnWindowRadius lo hi → Vlog x=1)
    (L cstar eta tau saving em ed eps:ℝ)(hL:1≤L)(hcstar:0<cstar)(heta:0<eta)
    (heta1:eta≤1)(hetac:eta≤cstar/100000)(htau:0<tau)(htau1:tau≤1)
    (hem:0<em)(hed:0<ed)(heps:0<eps)(K:ℕ):
    ∃(ω₁₁ ω₁₂ ω₂₁ ω₂₂:𝓢(ℝ,ℂ))(af₁ bf₁ af₂ bf₂ window bw:ℝ)(shortDegree:ℕ),
      0<af₁ ∧ af₁≤bf₁ ∧ 0<af₂ ∧ af₂≤bf₂ ∧
      HasCompactSupport (ω₁₁:ℝ→ℂ) ∧ HasCompactSupport (ω₁₂:ℝ→ℂ) ∧
      HasCompactSupport (ω₂₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂₂:ℝ→ℂ) ∧
      tsupport (ω₁₁:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧ tsupport (ω₁₂:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧
      tsupport (ω₂₁:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧ tsupport (ω₂₂:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧
      1≤bw ∧ Real.exp Alog≤bw ∧ bw=Real.exp window ∧
    ∀epsFirst epsSecond:ℝ,0<epsFirst → 0<epsSecond → ∀degree:ℕ,
    ∀(q:ℕ)(hq:q≠0),∃Cs Cb Z₀:ℝ,0<Cs ∧ 0≤Cb ∧ 1<Z₀ ∧
    ∀{σ:Type}[DecidableEq σ](m:O),m≠0 →
    ∀Z N V M z₀ margin cutoff pi epschild A loss lossFinal theta:ℝ,
      Z₀≤Z → 2≤Z → 2≤Z^eta → Real.exp 1≤Z^eta → 1≤eta*Real.log Z →
      0≤N → 0≤V → 0≤M → N+V≤L → M≤N+V → z₀≤L →
      hi≤Z^eta → Real.exp Alog≤Z^eta → Real.exp window≤Z^eta →
      0≤cutoff → cutoff≤L → cutoff≤cstar/200 →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
      0≤pi → 6*eta≤pi → em*(20*(3*L+16)+30)≤pi/4 → ed*(20*(3*L+16)+30)≤pi/4 →
      0≤epschild → -saving≤48*eta+tau+pi+epschild+epsSecond →
      48*eta+tau+pi+epschild+epsSecond≤loss →
      3*eta+epsFirst*(2*L+7*eta)≤lossFinal →
      loss+(2*L+15*eta+tau)*epsFirst+epsFirst≤lossFinal → -saving≤lossFinal →
      0≤A →
    ∀labels:Finset (Ideal O),(∀I∈labels,Supported I ∧ Squarefree I ∧ (I.absNorm:ℝ)≤Z^V) →
    ∀D:ℕ,hi*Z^N≤D → ∀slots:Finset σ,slots.card≤K →
    ∀(lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))(H:σ→ℝ),
      (slots:Set σ).PairwiseDisjoint lists →
      (∀i∈slots,1≤H i) → (∀i∈slots,∀P∈lists i,(Ideal.absNorm P.val:ℝ)≤H i) → (∏i∈slots,H i)≤Z^z₀ →
    ∀(Ψ:O→*ℂ),(∀u,‖Ψ u‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ,
      (∀i∈slots,∀P∈lists i,‖a i P‖≤1) →
      let S:=reflectionExcludedPrimes q;
      let F:=InitialMeanSquare.outsideSquarefreeIdeals S D;
      let hF:=InitialMeanSquare.outsideSquarefree_admissible S D (reflectionExcludedPrimes_bad q);
      letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
      let om:=radialFromLog Vlog (Vlog.smooth ⊤) Alog hbox;
      (∀j∈cubeLogRange hi (Z^N),
        let ell:=actualCubeLength Z j;
        let Q:=progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D hi (Z^N) j);
        Q.Nonempty → ∀ξ:ℝ,∀k∈actualLongSourceKeys (poolPrimary F) (poolPrimary_ne_zero F hF)
          (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q labels Ψ m (m*excludedGenerator S)
          slots lists a om Z M (N-3*ell) ell V (Z^(cutoff-V)) ξ L eta tau,
          ChildBounds (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
            (poolPrimary_good F hF) Finset.univ Q k.1 k.2.1 k.2.2 true Ψ m slots lists a ω₁₁ ω₁₂
            Z M (N-3*ell) ell V eta tau window bw epschild A K degree) →
      (∀j∈cubeLogRange hi (Z^N),
        let ell:=actualCubeLength Z j;
        let Q:=progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D hi (Z^N) j);
        Q.Nonempty → ∀ξ:ℝ,∀k∈actualLongSourceKeys (poolPrimary F) (poolPrimary_ne_zero F hF)
          (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q labels Ψ m (m*excludedGenerator S)
          slots lists a om Z M (N-3*ell) ell V (Z^(cutoff-V)) ξ L eta tau,
          ChildBounds (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
            (poolPrimary_good F hF) Finset.univ Q k.1 k.2.1 k.2.2 false Ψ m slots lists a ω₂₁ ω₂₂
            Z M (N-3*ell) ell V eta tau window bw epschild A K degree) →
      Z^(-(N+V))*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 (Z^M),
        ‖outsideCanonicalMarkedRow S D (reflectionExcludedPrimes_bad q) Ψ m (idealGenerator I) z
          slots lists a (normTwistedSource W theta) (Z^N)‖^2)≤
      Cs*(1+‖theta‖)^shortDegree*Z^(N+V-cstar/256)+
      Cb*(1+A)*(1+‖theta‖)^(2*(InverseClippingProfiles.momentOrder (firstDegree degree)+(volume:Measure ℝ).integrablePower))*
        Z^(N+V+lossFinal+2*L*epsFirst+eps) := by
  have hL0:0≤L:=by linarith
  obtain ⟨w11,w12,w21,w22,af1,bf1,af2,bf2,window,bw,ha1,hab1,ha2,hab2,
    hw11,hw12,hw21,hw22,hs11,hs12,hs21,hs22,hbw,hbA,hbexp,hbin⟩:=
    actual_marked_bin_height lo hi hlo hhi W hsW hW Vlog Alog hbox hone L eta tau saving em ed
      hL0 heta.le heta1 htau htau1 hem hed K
  obtain ⟨ds,hstate⟩:=actual_complete_state_from_live_bins lo hi hlo hhi W hsW hW L cstar eta eps
    hL0 hcstar heta heta1 hetac heps K K
  refine ⟨w11,w12,w21,w22,af1,bf1,af2,bf2,window,bw,ds,ha1,hab1,ha2,hab2,
    hw11,hw12,hw21,hw22,hs11,hs12,hs21,hs22,hbw,hbA,hbexp,?_⟩
  intro epsFirst epsSecond heF heS degree q hq
  obtain ⟨Ccoef,C,hcoef,hC,hbin⟩:=hbin epsFirst epsSecond heF heS degree
  obtain ⟨Cs,Z₀,hCs,hZ₀,hstate⟩:=hstate q hq
  let Cb:=C*Ccoef^2*Real.exp (2*epsFirst)
  refine ⟨Cs,Cs*Cb,Z₀,hCs,by dsimp [Cb];positivity,hZ₀,?_⟩
  intro σ _ m hm Z N V M z₀ margin cutoff pi epschild A loss lossFinal theta hZ hZ2 h2 hExp hlog
    hN hV hM hFcap hMF hzcap hbZ hAZ hwin hcut hcutL hcutc hmN hmargin hreserve
    hpi hpieta hemc hedc hechild hsave hloss hprincipal hretained htail hA
    labels hlabels D hD slots hcard lists H hdis hH1 hH hprod Ψ hΨ hperiod a ha
  dsimp only
  intro hleft hright
  have hz:0<Z:=by linarith
  have hZ1:1≤Z:=by linarith
  let d:=2*(InverseClippingProfiles.momentOrder (firstDegree degree)+(volume:Measure ℝ).integrablePower)
  let E:=Cb*(1+A)*Z^(N+V+lossFinal+2*L*epsFirst)*(1+‖theta‖)^d
  have hE:0≤E:=by dsimp [E,Cb];positivity
  have hbins:∀j∈cubeLogRange hi (Z^N),
      (progressingCubes (reflectionExcludedPrimes q) D (Z^(cutoff-V))
        (activeCubeLogBin (reflectionExcludedPrimes q) D hi (Z^N) j)).Nonempty →
      Z^(-V)*rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin (reflectionExcludedPrimes q) D
        (progressingCubes (reflectionExcludedPrimes q) D (Z^(cutoff-V))
          (activeCubeLogBin (reflectionExcludedPrimes q) D hi (Z^N) j))
        Ψ m (idealGenerator I) z (normTwistedSource W theta) (Z^N) (Z^(cutoff-V)) slots lists a) (Z^M)≤E := by
    intro j hj hne
    let ell:=actualCubeLength Z j
    let S:=reflectionExcludedPrimes q
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    have hF:=InitialMeanSquare.outsideSquarefree_admissible S D (reflectionExcludedPrimes_bad q)
    let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance
    let Q:=progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D hi (Z^N) j)
    obtain ⟨hel,hr,hrL,helL,hFL,hgap,hqn⟩:=actual_long_bin_geometry S D (reflectionExcludedPrimes_bad q)
      hi Z N V cutoff eta L j (by linarith) hL heta1 hV hFcap hbZ hlog hne
    have hsN:(N-3*ell)+3*ell=N:=by ring
    have hpr:3*eta+epsFirst*(5*ell+2*(N-3*ell)+7*eta)≤lossFinal:=by
      have hNL:N≤L:=by linarith
      nlinarith
    have hh:=hbin theta S D (reflectionExcludedPrimes_bad q) (reflectionExcludedPrimes_prime q)
      Q labels Ψ m slots lists a Z M (N-3*ell) ell V (Z^(cutoff-V)) pi epschild A loss lossFinal
      hZ2 h2 hExp hM hFL (by linarith) hel hV hr hAZ
      (by intro v hv;rw [←cubeIdeal_primeProduct_norm F hF];exact (hqn v hv).1)
      (by intro v hv;rw [←cubeIdeal_primeProduct_norm F hF];exact (hqn v hv).2)
      hrL helL (by linarith) hwin hpi hpieta hemc hedc hechild (by linarith) hloss hcard
      (by linarith) hpr hretained (by linarith) hΨ hA
      (fun I hI=>(hlabels I hI).2.1) (fun I hI=>(hlabels I hI).1.1)
      (fun I hI=>((hlabels I hI).2.2).trans (Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)))
      hdis ha (by simpa only [hsN] using hD) (hleft j hj hne) (hright j hj hne)
    rw [hsN] at hh
    apply hh.trans
    have hc:=mul_le_mul_of_nonneg_right
      (actual_long_uniform_parent_cost Z ell N V L epsFirst Ccoef C A lossFinal hZ1 helL heF.le hC hA)
      (show 0≤(1+‖theta‖)^d by positivity)
    simpa only [hsN] using hc
  have hs:=hstate m hm Z N V M z₀ margin cutoff hZ hN (by linarith) hV (by linarith) hM (by linarith)
    hzcap hcut hcutL hcutc hmN hmargin hreserve labels hlabels D hD slots hcard lists H
    hdis hH1 hH hprod Ψ hΨ hperiod theta a ha E hE hbins
  apply hs.trans_eq
  dsimp [E,d]
  rw [Real.rpow_add hz (N+V+lossFinal+2*L*epsFirst) eps]
  ring

end SevenEighths.InverseMoment

end

end OAI
