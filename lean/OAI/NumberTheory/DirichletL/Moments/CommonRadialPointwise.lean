import OAI.NumberTheory.DirichletL.Moments.CommonRadialSource
import OAI.NumberTheory.DirichletL.Moments.CommonRadialCost
import OAI.NumberTheory.DirichletL.Moments.RadialPointwiseUniform

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonRadialPointwise
open CenteredMomentCommonRadialSource CenteredMomentCommonRadialData CenteredMomentCommonRadialCost
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

 def profileCost (s:Input ι) : ℝ :=
  ((∏i,s.M i)^2*(max 1 s.upper)^Fintype.card ι)*s.toData.profileFactor

omit [DecidableEq ι] in
lemma profileCost_nonneg (s:Input ι) : 0≤profileCost s :=
  mul_nonneg (mul_nonneg (sq_nonneg _) (by positivity)) s.toData.profile_nonneg

 theorem actual_common_source_pointwise (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0:ℝ,0<C0 ∧ ∀(s:Input ι),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      ∀(r:Radial) (C:Ideal O) (hC:Supported C) (R seed L:Ideal O),seed∣C → Squarefree L →
      ∀E Z:ℝ,0≤E → 1<Z → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm L:ℝ)≤Z^B →
      (∀b:actualAllocations s.pools C,∀a∈(commonData s C R b).toSource.active L,
        childEnergy (commonData s C R b) r L a≤E) →
      sourceEnergy s r C hC R seed L≤C0*Z^δ*(profileCost s*E)/
        ((Ideal.absNorm C:ℝ)*Ideal.absNorm L) := by
  obtain ⟨C₁,hC₁,hchild⟩:=CenteredMomentRadialPointwiseUniform.actual_uniform_divisor lo hi B (δ/2) hB (by linarith)
  obtain ⟨C₂,hC₂,hcount⟩:=card_squared_subpower (ι:=ι) B (δ/2) hB (by linarith)
  refine ⟨C₁*C₂,by positivity,?_⟩
  intro s hlo hhi r C hC R seed L hseed hL E Z hE hZ hNC hNL hc
  have hnC:0<(Ideal.absNorm C:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hnL:0<(Ideal.absNorm L:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hL.ne_zero)
  have hz:0<Z:=zero_lt_one.trans hZ
  have heach (b:actualAllocations s.pools C):
      energy (commonData s C R b) r L≤C₁*Z^(δ/2)*(s.toData.profileFactor*E)/(Ideal.absNorm L:ℝ):=by
    have hh:=hchild (liveIndices b.val) (commonData s C R b)
      (fun i=>hlo i.val) (fun i=>hhi i.val) r L hL E Z hE hZ hNL (hc b)
    apply hh.trans
    apply div_le_div_of_nonneg_right _ hnL.le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_right (common_profile_le s C R b) hE
  have hh:sourceEnergy s r C hC R seed L≤commonCost s C*
      (((actualAllocations s.pools C).card:ℝ)*(C₁*Z^(δ/2)*(s.toData.profileFactor*E)/(Ideal.absNorm L:ℝ))):=by
    apply (original_source_common_bound s r C hC R seed L hseed).trans
    apply mul_le_mul_of_nonneg_left _ (commonCost_nonneg s C)
    apply (Finset.sum_le_sum (fun b _=>heach b)).trans_eq
    simp
  apply hh.trans
  have hc2:=hcount s C hC.1 Z hZ hNC
  calc
    _=((actualAllocations s.pools C).card:ℝ)^2*
        (C₁*Z^(δ/2)*(profileCost s*E)/((Ideal.absNorm C:ℝ)*Ideal.absNorm L)):=by
      unfold commonCost profileCost
      ring
    _≤(C₂*Z^(δ/2))*(C₁*Z^(δ/2)*(profileCost s*E)/
        ((Ideal.absNorm C:ℝ)*Ideal.absNorm L)):=
      mul_le_mul_of_nonneg_right hc2 (div_nonneg (mul_nonneg (by positivity)
        (mul_nonneg (profileCost_nonneg s) hE)) (mul_nonneg hnC.le hnL.le))
    _=_:=by
      have hp:Z^(δ/2)*Z^(δ/2)=Z^δ:=by rw [←Real.rpow_add hz];congr 1;ring
      calc
        _=(C₁*C₂)*(Z^(δ/2)*Z^(δ/2))*(profileCost s*E)/
          ((Ideal.absNorm C:ℝ)*Ideal.absNorm L):=by ring
        _=_:=by rw [hp]

end SevenEighths.CenteredMomentCommonRadialPointwise

end

end OAI
