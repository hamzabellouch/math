import OAI.NumberTheory.DirichletL.Descent.FirstDyadicLiveRadius
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

theorem original_dyadic_retained_energy
    (om Φ:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support om⊆Set.Icc a b):
    ∃(omega₁ omega₂:𝓢(ℝ,ℂ))(lo hi:ℝ),0<lo ∧ lo≤hi ∧
      HasCompactSupport (omega₁:ℝ→ℂ) ∧ HasCompactSupport (omega₂:ℝ→ℂ) ∧
      tsupport (omega₁:ℝ→ℂ)⊆Set.Icc lo hi ∧ tsupport (omega₂:ℝ→ℂ)⊆Set.Icc lo hi ∧
    ∀eps:ℝ,0<eps→∀J:ℕ,∃C:ℝ,0≤C ∧
    ∀{ι:Type}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)
      (Z M r ell V eta tau Fmax Γ K theta Benergy:ℝ)
      (_hZ:1<Z)(_hbin:2≤Z^eta)(_hM:0≤M)(_hF:r+3*ell+V≤Fmax)
      (_hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
      (_hΨ:∀u,‖Ψ u‖≤1)(_hΓ:0≤Γ)(_hK:0<K)(_hB:0≤Benergy)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)(_hβ:∀I∈labels,∀v∈Q,‖β I v‖≤Γ),
      let Y:=Z^(2*Fmax+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource om theta (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K);
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 0))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        refinedChildEnergy p hp hg hinj pool Q k.1 k.2.1 (labelGate p k.2.2) true Ψ m mark omega₁
          ((physicalScales (Z^r) k.1 k.2.1) 7)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 1))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        refinedChildEnergy p hp hg hinj pool Q k.1 k.2.1 (labelGate p k.2.2) false Ψ m mark omega₂
          ((physicalScales (Z^r) k.1 k.2.1) 8)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (Z^(-r-2*ell-V)*Z^M)*‖originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W Φ K Y cutoff (fun _=>1)‖≤
        C*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*
          Z^((2*Fmax+15*eta+tau)*eps)*(keys.card:ℝ):=by
  let g₁:=priorityLogWindow om a b ha hs true
  let g₂:=priorityLogWindow om a b ha hs false
  let M₀:=|Real.log a|+|Real.log b|
  have hm:0≤M₀:=by dsimp [M₀];positivity
  obtain ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,he⟩:=original_refined_cell_physical_budget
    g₁ g₂ Φ M₀ M₀ hm hm (priorityLogWindow_support om a b ha hs true) (priorityLogWindow_support om a b ha hs false)
  refine ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro eps heps J
  obtain ⟨Cp,Kp,hCp,hKp,hcell⟩:=he eps heps 0 J
  refine ⟨Cp*Kp,mul_nonneg hCp hKp.le,?_⟩
  intro ι _ p hp _ hg hinj hcop hc hpr pool Q labels β Ψ m mark Z M r ell V eta tau Fmax Γ K theta Benergy
    hZ hbin hM hF hQ hΨ hΓ hK hB hsf hn hβ Y cutoff W source keys hleft hright
  have hz:0<Z:=zero_lt_one.trans hZ
  have hsum:=original_retained_joint_profile_bound p hp hcop hg pool Q labels β cutoff Ψ m mark
    om a b ha hs Φ K Y (Z^r) theta (Real.rpow_pos_of_pos hz _) (fun _=>1) (by intro i;norm_num)
  have hnrm:0≤Z^(-r-2*ell-V)*Z^M:=mul_nonneg (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hz.le _)
  apply (mul_le_mul_of_nonneg_left hsum hnrm).trans
  rw [Finset.mul_sum]
  have hpoint:∀k∈keys,
      (Z^(-r-2*ell-V)*Z^M)*‖refinedCellRows p hp hcop hg pool Q labels β cutoff Ψ m mark k.1 k.2.1 (labelGate p k.2.2)
        (positiveSource g₁ 1 (-theta)) (positiveSource g₂ 1 theta) Φ K Y (physicalScales (Z^r) k.1 k.2.1)‖≤
      (Cp*Kp)*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*Z^((2*Fmax+15*eta+tau)*eps):=by
    intro k hk
    let T₁:=(physicalScales (Z^r) k.1 k.2.1) 7
    let T₂:=(physicalScales (Z^r) k.1 k.2.1) 8
    have hT₁:0<T₁:=physicalScales_pos _ (Real.rpow_pos_of_pos hz _) _ _ 7
    have hT₂:0<T₂:=physicalScales_pos _ (Real.rpow_pos_of_pos hz _) _ _ 8
    have hY:0<firstCellRadius Z M r ell V eta tau k.1 k.2.2:=Real.rpow_pos_of_pos hz _
    have hl:=hleft k hk
    have hr:=hright k hk
    have heta:0≤eta:=by
      apply (Real.rpow_le_rpow_left_iff hZ).mp
      rw [Real.rpow_zero]
      linarith
    have hL:0≤eta*Real.log Z:=mul_nonneg heta (Real.log_nonneg hZ.le)
    have he' := hcell p hp hg hinj hcop hc hpr pool Q labels β cutoff Ψ m mark Γ Y
      (firstCellRadius Z M r ell V eta tau k.1 k.2.2) hΨ hΓ hY hsf hn hβ k.1 k.2.1 (labelGate p k.2.2)
      (fun x hx I _=>first_dyadic_refined_cutoff p pool Q k.1 k.2.2 Z M r ell V eta tau x hx I)
      T₁ T₂ K theta (eta*Real.log Z) hT₁ hT₂ hK hL Benergy Z M r ell V (dyadicExponent Z (k.1 3))
      (dyadicExponent Z (k.1 0)) (dyadicExponent Z (k.1 1)) (dyadicExponent Z (k.1 2))
      (dyadicExponent Z (k.1 4)) (dyadicExponent Z k.2.1) (dyadicExponent Z (k.1 5)) eta
      hB hz (physicalScales_rpow Z r hZ k.1 k.2.1) rfl hl hr
    have hrad:=first_live_cell_radius_cap p hp pool Q labels Y _ Z M r ell V eta tau Fmax hZ hbin hM hF hQ k hk
    have hpow:=Real.rpow_le_rpow hY.le hrad heps.le
    rw [←Real.rpow_mul hz.le] at hpow
    simp only [pow_zero,div_one,norm_neg] at he'
    calc
      _≤(Γ^2*Kp*(firstCellRadius Z M r ell V eta tau k.1 k.2.2)^eps*Benergy)*
          (Cp*((1+‖theta‖)^InverseClippingProfiles.momentOrder J*(1+‖theta‖)^InverseClippingProfiles.momentOrder J)):=he'
      _≤(Γ^2*Kp*Z^((2*Fmax+15*eta+tau)*eps)*Benergy)*
          (Cp*((1+‖theta‖)^InverseClippingProfiles.momentOrder J*(1+‖theta‖)^InverseClippingProfiles.momentOrder J)):=by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity)) hB
      _=_:=by rw [show 2*InverseClippingProfiles.momentOrder J=InverseClippingProfiles.momentOrder J+InverseClippingProfiles.momentOrder J by omega,pow_add];ring
  calc
    _≤∑_k∈keys,(Cp*Kp)*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*Z^((2*Fmax+15*eta+tau)*eps):=
      Finset.sum_le_sum hpoint
    _=_:=by simp [mul_comm]

end SevenEighths.InverseMoment

end

end OAI
