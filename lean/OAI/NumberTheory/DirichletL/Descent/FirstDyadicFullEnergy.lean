import OAI.NumberTheory.DirichletL.Descent.FirstDyadicPriorityBudget
import OAI.NumberTheory.DirichletL.Descent.FirstDyadicOriginalBranches
import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveParents
import OAI.NumberTheory.DirichletL.Descent.FirstLiveCountBudget
import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveAggregate
import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstProfileUniform
open InverseAmbientProfileTower JointLogSeparation FourierBridge CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem original_dyadic_full_energy
    (om:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support om⊆Set.Icc a b) (Lcap Mmax eta tau saving:ℝ)(hcap:0≤Lcap)(hMmax:0≤Mmax)(hb:0≤b)
    (heta:0≤eta)(heta1:eta≤1)(htau:0<tau)(htau1:tau≤1):
    ∃(omega₁ omega₂:𝓢(ℝ,ℂ))(lo hi:ℝ),0<lo ∧ lo≤hi ∧
      HasCompactSupport (omega₁:ℝ→ℂ) ∧ HasCompactSupport (omega₂:ℝ→ℂ) ∧
      tsupport (omega₁:ℝ→ℂ)⊆Set.Icc lo hi ∧ tsupport (omega₂:ℝ→ℂ)⊆Set.Icc lo hi ∧
    ∀eps:ℝ,0<eps→∀J:ℕ,∃C Czero Ctail:ℝ,0≤C ∧ 0≤Czero ∧ 0≤Ctail ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
      (Z M r ell V Γ theta Benergy:ℝ)
      (_hZ:2≤Z)(_hbin:2≤Z^eta)(_hM:0≤M)(_hF:r+3*ell+V≤Lcap)(_hMcap:M≤Mmax)(_hell:0≤ell)(_hV:0≤V)(_hr: -eta≤r)
      (_hbZ:b≤Z^eta)(_hQpool:∀v∈Q,v.support⊆pool)
      (_hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
      (_hrcap:r≤Lcap)(_hellcap:ell≤Lcap)

      (_hΨ:∀u,‖Ψ u‖≤1)(_hΓ:0≤Γ)(_hB:0≤Benergy)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)(_hβ:∀I∈labels,∀v∈Q,‖β I v‖≤Γ)
      (_hlabels:∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta))
      (_hslots:(slots:Set σ).PairwiseDisjoint lists)(_hweights:∀i∈slots,∀q∈lists i,‖weights i q‖≤1),
      let mark:=fun v U=>primeMark slots lists weights (v.support∪U);
      let Y:=Z^(2*Lcap+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource om theta (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W rowMajorant (Z^M));
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 0))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj (fun q=>q.rightExponent.support) pool
          (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2)
          (fun x=>(‖commonSelector p (fun _=>1) k.2.1 x.quotientSupport‖:ℂ))
          true Ψ m slots lists weights omega₁
          ((physicalScales (Z^r) k.1 k.2.1) 7)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 1))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj (fun q=>q.leftExponent.support) pool
          (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2)
          (fun x=>(‖commonSelector p (fun _=>1) k.2.1 x.quotientSupport‖:ℂ))
          false Ψ m slots lists weights omega₂
          ((physicalScales (Z^r) k.1 k.2.1) 8)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      Z^(-r-2*ell-V)*CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
        varyingReopenedRow p hp hcop hg pool Q (β I) Ψ m (ConcretePrimeRowBridge.idealGenerator I)
          (fun v U=>mark v U*W (primeProductNorm p U)) z) (Z^M)≤
        Czero*Γ^2*Z^(M-ell+3*eta+eps*(5*ell+2*r+7*eta))+
        C*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*
          Z^((2*Lcap+15*eta+tau)*eps+eps)+Ctail*Γ^2*Z^(-saving) :=by
  obtain ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,he⟩:=original_dyadic_priority_budget om rowMajorant a b ha hs Lcap hcap hb
  refine ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro eps heps J
  obtain ⟨C,hC,hret⟩:=he eps heps J
  obtain ⟨Cz,Ct,hCz,hCt,hbranches⟩:=original_dyadic_zero_tail om b Mmax Lcap eta tau (saving+eta) eps
    (fun y hy=>(hs hy).2) hMmax hcap heta htau heps
  refine ⟨C,Cz,Ct,hC,hCz,hCt,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc hpr pool Q labels β Ψ m slots lists weights Z M r ell V Γ theta Benergy
    hZ hbin hM hF hMcap hell hV hr hbZ hQpool hQ hrcap hellcap hΨ hΓ hB hsf hn hβ hlabels hslots hweights
    mark Y cutoff W source keys hleft hright
  have hz:0<Z:=by linarith
  have hZ1:1<Z:=by linarith
  have hK:0<Z^M:=Real.rpow_pos_of_pos hz _
  have he':=original_global_physical_energy p hp hcop hg hinj hc hpr pool Q hQpool labels hn β Ψ m mark W
    (Z^M) Y hK cutoff (fun _ _ _ _ _ _ _=>Real.rpow_nonneg hz.le _)
    (fun x hx _ _=>first_dyadic_original_cap p hp pool Q Z M r ell V eta tau Lcap hZ1 hbin hM hF hQ x hx)
    (fun _=>1) (by intro i;norm_num)
  have hret':=hret p hp hg hinj hcop hc hpr pool Q labels β Ψ m slots lists weights Z M r ell V eta tau Lcap Γ
    (Z^M) theta Benergy hZ hbin hM hF hQ hrcap hellcap hcap le_rfl heta heta1 htau.le htau1 hΨ hΓ hK hB hsf hn hβ hleft hright
  obtain ⟨hz',ht'⟩:=hbranches p hp hcop hg hinj hc pool Q labels β Ψ m slots lists weights Z M r ell V Γ theta
    hZ1 hbin hM hMcap hell hV hr hF hΓ hbZ hΨ hQ hn hlabels hβ hslots hweights
  have hfactor:Z^(-r-2*ell-V)≤Z^eta:=Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith)
  have htail:Z^(-r-2*ell-V)*‖reopenedPhysicalSourceSum pool Q labels β (fun q D I=>
        canonicalCubeDualTail p hp hcop hg pool q D Ψ Ψ m m (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>mark q.rightExponent U*W (primeProductNorm p U))
          (fun U=>mark q.leftExponent U*W (primeProductNorm p U)) rowMajorant (Z^M)
          (reopenedPhysicalCutoff p q I (cutoff q D I)))‖≤Ct*Γ^2*Z^(-saving):=by
    have ht'':_≤Ct*Γ^2*Z^(-(saving+eta)):=ht'
    apply (mul_le_mul hfactor ht'' (norm_nonneg _) (Real.rpow_nonneg hz.le _)).trans
    apply le_of_eq
    rw [show Z^eta*(Ct*Γ^2*Z^(-(saving+eta)))=(Ct*Γ^2)*(Z^eta*Z^(-(saving+eta))) by ring,
      ←Real.rpow_add hz]
    congr 2
    ring
  have hall:=mul_le_mul_of_nonneg_left he' (Real.rpow_nonneg hz.le (-r-2*ell-V))
  simp only [mul_add] at hall
  apply hall.trans
  have hr':Z^(-r-2*ell-V)*((Z^M)*‖originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W rowMajorant (Z^M) Y cutoff (fun _=>1)‖)≤
      C*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*Z^((2*Lcap+15*eta+tau)*eps+eps):=by
    simpa only [mul_assoc] using hret'
  exact add_le_add (add_le_add hz' hr') htail

end SevenEighths.InverseMoment

end

end OAI
