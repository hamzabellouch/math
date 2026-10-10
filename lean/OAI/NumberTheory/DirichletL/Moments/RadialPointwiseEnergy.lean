import OAI.NumberTheory.DirichletL.Moments.RadialEligibleEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentRadialPointwiseEnergy
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentActiveDivisorShell CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentSlotRatios CenteredMomentUniformDivisorShell
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

lemma inverse_reduction (s:Data ι) (D:Ideal O) (hD:Squarefree D)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) (ha:a∈s.toSource.active D)
    (Z:ℝ) (hZ:1<Z) :
    1/formalReductionFactor D a s.P≤Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ) := by
  have hh:=s.toSource.active_pair_weight s.toSource D hD a a ha ha Z hZ
  rw [show formalReductionFactor D a s.P*formalReductionFactor D a s.P=
    (formalReductionFactor D a s.P)^2 by ring,Real.sqrt_sq (s.reduction_pos D a).le] at hh
  convert hh using 1
  congr 2
  ring

 theorem actual_pointwise_divisor (N:ℕ) (hι:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀(s:Data ι) (r:Radial) (D:Ideal O),Squarefree D →
      ∀E Z:ℝ,0≤E → 1<Z → (∀a∈s.toSource.active D,childEnergy s r D a≤E) →
      energy s r D≤C*(Ideal.absNorm D:ℝ)^(2*ε)*Z^(s.toSource.allowance Z)*
        (s.profileFactor*E)/(Ideal.absNorm D:ℝ) := by
  obtain ⟨C₁,hC₁,henergy⟩:=CenteredMomentRadialEligibleEnergy.actual_source_from_children N hι ε hε
  obtain ⟨C₂,hC₂,hcard⟩:=CenteredMomentDivisorEnergy.allocation_card_small_power (ι:=ι⊕Fin 2) (N+2) (by omega) ε hε
  refine ⟨C₁*C₂,by positivity,?_⟩
  intro s r D hD E Z hE hZ hc
  have hn:0<(Ideal.absNorm D:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)
  have hp:0≤(Ideal.absNorm D:ℝ)^ε:=Real.rpow_nonneg hn.le _
  have hsz:((s.toSource.active D).card:ℝ)≤C₂*(Ideal.absNorm D:ℝ)^ε:=by
    apply (show ((s.toSource.active D).card:ℝ)≤Fintype.card (Allocation D (Finset.univ:Finset (ι⊕Fin 2))) by
      exact_mod_cast Finset.card_le_univ _).trans
    apply hcard D hD.ne_zero Finset.univ
    simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
    omega
  have hs:(∑a∈s.toSource.active D,1/formalReductionFactor D a s.P)≤
      (C₂*(Ideal.absNorm D:ℝ)^ε)*(Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ)):=by
    calc
      _≤∑a∈s.toSource.active D,Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ):=
        Finset.sum_le_sum (fun a ha=>inverse_reduction s D hD a ha Z hZ)
      _=((s.toSource.active D).card:ℝ)*(Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ)):=by simp
      _≤_:=mul_le_mul_of_nonneg_right hsz (div_nonneg (Real.rpow_nonneg (by linarith) _) hn.le)
  apply (henergy s r D hD E hE hc).trans
  calc
    _≤C₁*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
        ((C₂*(Ideal.absNorm D:ℝ)^ε)*(Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ))):=
      mul_le_mul_of_nonneg_left hs (mul_nonneg (mul_nonneg (mul_nonneg hC₁.le hp) s.profile_nonneg) hE)
    _=_:=by
      have he:(Ideal.absNorm D:ℝ)^ε*(Ideal.absNorm D:ℝ)^ε=(Ideal.absNorm D:ℝ)^(2*ε):=by
        rw [←Real.rpow_add hn];congr 1;ring
      calc
        _=(C₁*C₂)*((Ideal.absNorm D:ℝ)^ε*(Ideal.absNorm D:ℝ)^ε)*
          Z^(s.toSource.allowance Z)*(s.profileFactor*E)/(Ideal.absNorm D:ℝ):=by ring
        _=_:=by rw [he]

end SevenEighths.CenteredMomentRadialPointwiseEnergy

end

end OAI
