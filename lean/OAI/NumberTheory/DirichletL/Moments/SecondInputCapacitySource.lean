import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedCapacityCommon
import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceSupport

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondInputCapacitySource
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAllocatedChildCapacity
open CenteredMomentFirstAmplifiedCapacityCommon CenteredMomentSourceLiveColumn
open CenteredMomentSecondCapacitySourceShift CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentFirstPhysicalSourceSupport CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonHeightEnvelope
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

def lowerFactor (N:ℕ)(slotLower plainLower:ℝ):ℝ:=
  (min 1 slotLower)^N*plainLower^2

lemma lowerFactor_pos (N:ℕ)(slotLower plainLower:ℝ)(hs:0<slotLower)(hp:0<plainLower):
    0<lowerFactor N slotLower plainLower:=by unfold lowerFactor;positivity

theorem actual_lower_support (N:ℕ)(slotLower plainLower:ℝ)(hs:0<slotLower)(hp:0<plainLower)
    (s:Input ι)(hc:Fintype.card ι≤N)(hlo:slotLower≤s.lower)
    (hW₁:∀x,s.W₁ x≠0→plainLower≤x)(hW₂:∀x,s.W₂ x≠0→plainLower≤x)
    (R seed I:Ideal O)(hne:coefficient s R seed I≠0):
    lowerFactor N slotLower plainLower*volume s≤(I.absNorm:ℝ):=by
  have hm:0≤min 1 slotLower:=(lt_min zero_lt_one hs).le
  have hprod:(min 1 slotLower)^N≤∏i,s.lo i:=by
    apply (pow_le_pow_of_le_one hm (min_le_left _ _) hc).trans
    have hh:=Finset.prod_le_prod₀ (s:=Finset.univ) (f:=fun _:ι=>min 1 slotLower)
      (g:=fun i=>s.lo i) (fun _ _=>hm)
      (fun i _=>(min_le_right _ _).trans (hlo.trans (s.lower_le i)))
    simpa only [Finset.prod_const,Finset.card_univ] using hh
  have hh:=original_column_lower s R seed I plainLower plainLower hp.le hp.le hW₁ hW₂ hne
  change (∏i,s.lo i)*plainLower*plainLower*volume s≤(I.absNorm:ℝ) at hh
  apply le_trans _ hh
  have hv:0≤volume s:=(volume_pos s).le
  unfold lowerFactor
  nlinarith [mul_le_mul_of_nonneg_right hprod (mul_nonneg (sq_nonneg plainLower) hv)]

lemma upper_log_cost (N:ℕ)(b Z:ℝ)(hb:1≤b)(hZ:1<Z)
    (s:Input ι)(hc:Fintype.card ι≤N)(hhi:s.upper≤b):
    (Fintype.card ι:ℝ)*Real.logb Z (max 1 s.upper)≤(N:ℝ)*Real.logb Z b:=by
  have hs:0<max 1 s.upper:=lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hl:=Real.logb_le_logb_of_le hZ hs (max_le hb hhi)
  have hn:(Fintype.card ι:ℝ)≤N:=by exact_mod_cast hc
  exact (mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg _)).trans
    (mul_le_mul_of_nonneg_right hn (Real.logb_nonneg hZ hb))

def fixedLoss (N:ℕ)(slotLower plainLower b Z:ℝ):ℝ:=
  Real.logb Z (4/((fixedFactor:ℝ)*(lowerFactor N slotLower plainLower)^2))+
    (N:ℝ)*Real.logb Z b

theorem actual_common_input_shift (N:ℕ)(slotLower plainLower b:ℝ)
    (hs:0<slotLower)(hp:0<plainLower)(hb:1≤b)
    (s:Input ι)(hc:Fintype.card ι≤N)(hlo:slotLower≤s.lower)(hhi:s.upper≤b)
    (hW₁:∀x,s.W₁ x≠0→plainLower≤x)(hW₂:∀x,s.W₂ x≠0→plainLower≤x)
    (R0 seed:Ideal O)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(B:actualAllocations s.pools C)
    (hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (U:Finset (CommonIndex C D))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (K Z qref:ℝ)(n:Fin 4→ℤ)(hq:0<qref)(hK:0<K)(hZ:1<Z)
    (hne:physicalBlock s.η s.t S (coefficient s R0 seed) C D hC hD U R rows W K n≠0):
    Real.logb Z (preVolume (commonData (withHeight s s.η s.t) C R0 B))-
      Real.logb Z (envelopeRef qref C D U n)≤
      Real.logb Z K-Real.logb Z qref-Real.logb Z (volume s)+
        fixedLoss N slotLower plainLower b Z+Real.logb Z (ratioPenalty n):=by
  have hlow:=fun I hI=>actual_lower_support N slotLower plainLower hs hp s hc hlo hW₁ hW₂ R0 seed I hI
  have hh:=common_raw_reference_shift s s.η s.t S (coefficient s R0 seed) C D R0 hC hD hCD
    B hB U R rows W K (lowerFactor N slotLower plainLower) Z qref n hq hK
    (lowerFactor_pos N slotLower plainLower hs hp) hZ hlow hne
  have hu:=upper_log_cost N b Z hb hZ s hc hhi
  unfold fixedLoss
  linarith

theorem actual_common_input_shift_right (N:ℕ)(slotLower plainLower b:ℝ)
    (hs:0<slotLower)(hp:0<plainLower)(hb:1≤b)
    (s:Input ι)(hc:Fintype.card ι≤N)(hlo:slotLower≤s.lower)(hhi:s.upper≤b)
    (hW₁:∀x,s.W₁ x≠0→plainLower≤x)(hW₂:∀x,s.W₂ x≠0→plainLower≤x)
    (R0 seed:Ideal O)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(B:actualAllocations s.pools D)
    (hB:frozenCoefficient B.val D R0 s.ν s.W s.P≠0)
    (U:Finset (CommonIndex C D))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (K Z qref:ℝ)(n:Fin 4→ℤ)(hq:0<qref)(hK:0<K)(hZ:1<Z)
    (hne:physicalBlock s.η s.t S (coefficient s R0 seed) C D hC hD U R rows W K n≠0):
    Real.logb Z (preVolume (commonData (withHeight s s.η s.t) D R0 B))-
      Real.logb Z (envelopeRef qref C D U n)≤
      Real.logb Z K-Real.logb Z qref-Real.logb Z (volume s)+
        fixedLoss N slotLower plainLower b Z+Real.logb Z (ratioPenalty n):=by
  have hlow:=fun I hI=>actual_lower_support N slotLower plainLower hs hp s hc hlo hW₁ hW₂ R0 seed I hI
  have hh:=common_raw_reference_shift_right s s.η s.t S (coefficient s R0 seed) C D R0 hC hD hCD
    B hB U R rows W K (lowerFactor N slotLower plainLower) Z qref n hq hK
    (lowerFactor_pos N slotLower plainLower hs hp) hZ hlow hne
  have hu:=upper_log_cost N b Z hb hZ s hc hhi
  unfold fixedLoss
  linarith

theorem fixed_loss_eventually (N:ℕ)(slotLower plainLower b ε:ℝ)
    (hs:0<slotLower)(hp:0<plainLower)(hb:1≤b)(hε:0<ε):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ fixedLoss N slotLower plainLower b Z≤ε:=by
  have ha:=lowerFactor_pos N slotLower plainLower hs hp
  have hf:0<(fixedFactor:ℝ):=by exact_mod_cast fixedFactor_pos
  have hb0:0<b:=zero_lt_one.trans_le hb
  let A:ℝ:=4/((fixedFactor:ℝ)*(lowerFactor N slotLower plainLower)^2)*b^N
  have hA:0<A:=by dsimp [A];positivity
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) A,eventually_gt_atTop (1:ℝ)] with Z hg hZ
  refine ⟨hZ,?_⟩
  have hl:=Real.logb_le_logb_of_le hZ hA hg
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hl
  dsimp [A] at hl
  rw [Real.logb_mul (by positivity) (pow_pos hb0 N).ne',Real.logb_pow] at hl
  exact hl

end SevenEighths.CenteredMomentSecondInputCapacitySource

end

end OAI
