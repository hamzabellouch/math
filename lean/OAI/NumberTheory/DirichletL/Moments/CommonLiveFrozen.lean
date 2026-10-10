import OAI.NumberTheory.DirichletL.Moments.CommonHeightEnvelope
import OAI.NumberTheory.DirichletL.Moments.CommonRadialSource
import OAI.NumberTheory.DirichletL.Moments.CommonRadialCost
import OAI.NumberTheory.DirichletL.Moments.RadialPointwiseUniform

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCommonLiveFrozen
open CenteredMomentCommonRadialSource CenteredMomentCommonRadialData CenteredMomentCommonRadialCost
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
open CanonicalQuadraticSieve
open CenteredMomentCommonRadialPointwise CenteredMomentCommonRawScale CenteredMomentCommonRawCost
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentFirstSectors CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow
open CenteredMomentRestrictedSourceNormalization CenteredMomentSecondLiveEnergy
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

lemma source_mask_energy (keep:O→Prop) (Q:Finset (Ideal O)) (C L:Ideal O)
    (c f:Ideal O→ℂ) (W:𝓢(ℝ,ℂ)) (K:ℝ):
    CenteredMomentRestrictedSource.sourceRestrictedEnergy keep Q
      (fun I=>if IsCoprime C I ∧ L∣I then c I else 0) f W K =
    CenteredMomentRestrictedSource.sourceRestrictedEnergy keep Q
      (fun I=>if IsCoprime C I then c I else 0)
      (fun I=>(if L∣I then 1 else 0)*f I) W K := by
  unfold CenteredMomentRestrictedSource.sourceRestrictedEnergy
  congr 1
  funext I
  dsimp only
  by_cases hc:IsCoprime C (I:Ideal O) <;> by_cases hl:L∣(I:Ideal O) <;> simp [hc,hl]

theorem original_source_weighted (s:Input ι) (r:Radial) (C:Ideal O) (hC:Supported C)
    (R seed L:Ideal O) (hseed:seed∣C) :
    sourceEnergy s r C hC R seed L≤((actualAllocations s.pools C).card:ℝ)*
      ∑B:actualAllocations s.pools C,
        (‖frozenCoefficient B.val C R s.ν s.W s.P‖^2/rawReduction B.val s.P)*
          energy (commonData s C R B) r L := by
  have hh:=normalized_restricted_child_energy s.pools s.pools_ne
    (fun i I hI=>s.prime i I hI) C R seed hC hseed s.ν s.W s.P s.W₁ s.W₂
    s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 (s.X₁*s.X₂) (mul_pos s.X₁_pos s.X₂_pos)
    s.P_pos (fun I=>(if L∣I then 1 else 0)*heightCoeff s.η s.t I)
    r.keep r.profile r.scale r.scale_pos r.nonneg
  simp_rw [live_divisor_energy] at hh
  dsimp only [sourceEnergy]
  rw [source_mask_energy]
  apply hh.trans_eq
  apply congrArg (fun x:ℝ=>((actualAllocations s.pools C).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  exact congrArg (fun x:ℝ=>(‖frozenCoefficient B.val C R s.ν s.W s.P‖^2/rawReduction B.val s.P)*x)
    (live_source_eq s r C R L B)

 theorem actual_common_source_pointwise (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0:ℝ,0<C0 ∧ ∀(s:Input ι),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      ∀(r:Radial) (C:Ideal O) (hC:Supported C) (R seed L:Ideal O),seed∣C → Squarefree L →
      ∀E Z:ℝ,0≤E → 1<Z → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm L:ℝ)≤Z^B →
      (∀b:actualAllocations s.pools C,frozenCoefficient b.val C R s.ν s.W s.P≠0 → ∀a∈(commonData s C R b).toSource.active L,
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
  have hprof:=s.toData.profile_nonneg
  have heach (b:actualAllocations s.pools C) (hlive:frozenCoefficient b.val C R s.ν s.W s.P≠0):
      energy (commonData s C R b) r L≤C₁*Z^(δ/2)*(s.toData.profileFactor*E)/(Ideal.absNorm L:ℝ):=by
    have hh:=hchild (liveIndices b.val) (commonData s C R b)
      (fun i=>hlo i.val) (fun i=>hhi i.val) r L hL E Z hE hZ hNL (hc b hlive)
    apply hh.trans
    apply div_le_div_of_nonneg_right _ hnL.le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_right (common_profile_le s C R b) hE
  have hh:sourceEnergy s r C hC R seed L≤commonCost s C*
      (((actualAllocations s.pools C).card:ℝ)*(C₁*Z^(δ/2)*(s.toData.profileFactor*E)/(Ideal.absNorm L:ℝ))):=by
    apply (original_source_weighted s r C hC R seed L hseed).trans
    unfold commonCost
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    calc
      _≤∑b:actualAllocations s.pools C,
          (((∏i,s.M i)^2*(max 1 s.upper)^Fintype.card ι)/(C.absNorm:ℝ))*
            (C₁*Z^(δ/2)*(s.toData.profileFactor*E)/(L.absNorm:ℝ)):=by
        apply Finset.sum_le_sum
        intro b hb
        by_cases hzero:frozenCoefficient b.val C R s.ν s.W s.P=0
        · simp only [hzero,norm_zero,zero_pow (by decide:2≠0),zero_div,zero_mul]
          positivity
        · have hcost:=frozen_normalized_cost (ι:=ι) b.val (alloc_ne s C b) C R hC.1
            (Finset.mem_filter.mp b.property).2 s.ν s.W s.P s.M s.P_pos s.ν_bound
            s.W_bound s.M_ge_one s.lower s.upper s.lower_pos s.slot_support
          exact mul_le_mul hcost (heach b hzero)
            (CenteredMomentRadialEligibleEnergy.energy_nonneg _ _ _) (by positivity)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul];ring
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

end SevenEighths.CenteredMomentCommonLiveFrozen

end

end OAI
