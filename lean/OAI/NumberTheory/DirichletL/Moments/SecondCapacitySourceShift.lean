import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalScalar
import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalLedger
import OAI.NumberTheory.DirichletL.Moments.FirstSourceConductorCaps

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondCapacitySourceShift
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondNonexceptionalScalar CenteredMomentSecondPhysicalLedger
open CenteredMomentSectorLocalization CenteredMomentSourceBlockWindows
open CenteredMomentSecondPhysicalCost CenteredMomentSecondRadicalBudget
open CenteredMomentSupport CenteredMomentSecondWholeKernel ConcretePrimeRowBridge CenteredMomentSourceRow
local notation "O"=>HeckeFamily.O

theorem effective_upper (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0):
    dyadicScale (n 0)≤4*secondEffectiveScale C D
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K:=by
  unfold physicalBlock at hne
  obtain ⟨z,hzr,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero hne
  split_ifs at hz with hpart
  · obtain ⟨I,hI,hIs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hz
    obtain ⟨J,hJ,hterm⟩:=Finset.exists_ne_zero_of_sum_ne_zero hIs
    have hk: ((_:ℂ)*((_:ℝ):ℂ))≠0:=(mul_ne_zero_iff.mp hterm).2
    have hw: (_:ℝ)≠0:=Complex.ofReal_ne_zero.mp (mul_ne_zero_iff.mp hk).2
    have h0:=(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hw).1).1).1
    have hh:=(dyadicWeight_support (n 0) h0).1
    linarith
  · exact False.elim (hz rfl)

lemma adjusted_row_lower (k h x y:ℝ)(hk:0<k)(hh:0<h)(hx:0<x)(hy:0<y):
    x*y/k≤h*max 1 (1/(k*h/(x*y))):=by
  calc
    _=h*(1/(k*h/(x*y))):=by field_simp
    _≤_:=mul_le_mul_of_nonneg_left (le_max_right _ _) hh.le

lemma scalar_capacity_shift (Z F q U V H K a c d k h x y:ℝ)
    (hZ:1<Z)(hF:0<F)(hq:0<q)(hU:1≤U)(hV:0<V)(hH:0<H)(hK:0<K)(ha:0<a)
    (hc:0<c)(hd:0<d)(hk:0<k)(hh:0<h)(hx:0<x)(hy:0<y)
    (g:ℝ)(hg:0<g)(hgc:g≤c)
    (hscale:k≤4*(K*g*V/(c*d)))(hleft:a*H/c≤x)(hright:a*H/d≤y):
    Real.logb Z (H/c)-Real.logb Z (F*q*U*V*h*max 1 (1/(k*h/(x*y))))≤
      Real.logb Z K-Real.logb Z q-Real.logb Z H+Real.logb Z (4/(F*a^2)):=by
  have hu:0<U:=zero_lt_one.trans_le hU
  have hl:=Real.logb_le_logb_of_le hZ (div_pos (mul_pos ha hH) hc) hleft
  have hr:=Real.logb_le_logb_of_le hZ (div_pos (mul_pos ha hH) hd) hright
  have hs:=Real.logb_le_logb_of_le hZ hk hscale
  have hg':=Real.logb_le_logb_of_le hZ hg hgc
  have hu':0≤Real.logb Z U:=Real.logb_nonneg hZ hU
  have hrow:=Real.logb_le_logb_of_le hZ (div_pos (mul_pos hx hy) hk)
    (adjusted_row_lower k h x y hk hh hx hy)
  have hm:0<max 1 (1/(k*h/(x*y))):=lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  simp (disch := positivity) only [Real.logb_mul,Real.logb_div,Real.logb_pow] at hl hr hs hrow ⊢
  linarith

def adjustedEnvelope (η:Character)(C D:Ideal O)(U:Finset (CommonIndex C D))(n:Fin 4→ℤ):ℝ:=
  childEnvelope η C D U n*
    max 1 (1/(dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))))

def adjustedEnvelopeRef (qref:ℝ)(C D:Ideal O)(U:Finset (CommonIndex C D))(n:Fin 4→ℤ):ℝ:=
  (fixedFactor:ℝ)*qref*(∏P∈U,P.val).absNorm*
    (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm*dyadicScale (n 1)*
    max 1 (1/(dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))))

theorem actual_capacity_shift_reference (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K H a Z qref:ℝ)(n:Fin 4→ℤ)
    (hq:0<qref)(hK:0<K)(hH:0<H)(ha:0<a)(hZ:1<Z)
    (hlower:∀I:Ideal O,β I≠0→a*H≤(I.absNorm:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0):
    Real.logb Z (H/(C.absNorm:ℝ))-Real.logb Z (adjustedEnvelopeRef qref C D U n)≤
      Real.logb Z K-Real.logb Z qref-Real.logb Z H+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2)):=by
  have hc:=CenteredMomentFirstScale.norm_pos C hC.1
  have hd:=CenteredMomentFirstScale.norm_pos D hD.1
  have hg:=CenteredMomentFirstScale.norm_pos (Ideal.span {commonFrequencyGenerator C D})
    (Ideal.span_singleton_eq_bot.not.mpr (commonFrequencyGenerator_ne_zero C D hC))
  have hv:=CenteredMomentFirstScale.norm_pos (Ideal.span {nonunitFrequencyGenerator C D U})
    (Ideal.span_singleton_eq_bot.not.mpr (nonunitFrequencyGenerator_ne_zero C D hC U))
  have hu:=common_product_pos C D hC U
  have hu1:1≤((∏P∈U,P.val).absNorm:ℝ):=by exact_mod_cast (show 1≤(∏P∈U,P.val).absNorm from by exact_mod_cast hu)
  have hf:0<(fixedFactor:ℝ):=by exact_mod_cast fixedFactor_pos
  have hdiv:Ideal.span {commonFrequencyGenerator C D}∣C:=by
    have hh:=Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr (commonFrequencyGenerator_dvd C D hC hD hCD).1
    simpa only [primary_span_supported C hC] using hh
  have hgc:=CenteredMomentFirstSourceConductorCaps.divisor_norm_le _ C hC.1 hdiv
  have hh:=physicalBlock_scale_lower η t S β C D hC hD U R rows W K n a H ha hlower hne
  have hl:a*H/(C.absNorm:ℝ)≤dyadicScale (n 2):=by
    have hv':=(le_div_iff₀ ha).mp hh.1
    convert hv' using 1 ; ring
  have hr:a*H/(D.absNorm:ℝ)≤dyadicScale (n 3):=by
    have hv':=(le_div_iff₀ ha).mp hh.2
    convert hv' using 1 ; ring
  have hs:=effective_upper η t S β C D hC hD U R rows W K n hne
  have he:secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K=
      K*(Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)*
        Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U})/((C.absNorm:ℝ)*D.absNorm):=by
    simp only [secondEffectiveScale,map_mul,norm_mul,mul_pow,
      ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    ring
  rw [he] at hs
  exact scalar_capacity_shift Z (fixedFactor:ℝ) qref
    ((∏P∈U,P.val).absNorm:ℝ) ((Ideal.span {nonunitFrequencyGenerator C D U}).absNorm:ℝ)
    H K a (C.absNorm:ℝ) (D.absNorm:ℝ) (dyadicScale (n 0)) (dyadicScale (n 1))
    (dyadicScale (n 2)) (dyadicScale (n 3)) hZ hf hq hu1 hv hH hK ha hc hd
    (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _)
    ((Ideal.span {commonFrequencyGenerator C D}).absNorm:ℝ) hg hgc hs hl hr

theorem actual_capacity_shift_reference_right (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K H a Z qref:ℝ)(n:Fin 4→ℤ)
    (hq:0<qref)(hK:0<K)(hH:0<H)(ha:0<a)(hZ:1<Z)
    (hlower:∀I:Ideal O,β I≠0→a*H≤(I.absNorm:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0):
    Real.logb Z (H/(D.absNorm:ℝ))-Real.logb Z (adjustedEnvelopeRef qref C D U n)≤
      Real.logb Z K-Real.logb Z qref-Real.logb Z H+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2)):=by
  have hc:=CenteredMomentFirstScale.norm_pos C hC.1
  have hd:=CenteredMomentFirstScale.norm_pos D hD.1
  have hg:=CenteredMomentFirstScale.norm_pos (Ideal.span {commonFrequencyGenerator C D})
    (Ideal.span_singleton_eq_bot.not.mpr (commonFrequencyGenerator_ne_zero C D hC))
  have hv:=CenteredMomentFirstScale.norm_pos (Ideal.span {nonunitFrequencyGenerator C D U})
    (Ideal.span_singleton_eq_bot.not.mpr (nonunitFrequencyGenerator_ne_zero C D hC U))
  have hu:=common_product_pos C D hC U
  have hu1:1≤((∏P∈U,P.val).absNorm:ℝ):=by exact_mod_cast (show 1≤(∏P∈U,P.val).absNorm from by exact_mod_cast hu)
  have hf:0<(fixedFactor:ℝ):=by exact_mod_cast fixedFactor_pos
  have hdiv:Ideal.span {commonFrequencyGenerator C D}∣D:=by
    have hh:=Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr (commonFrequencyGenerator_dvd C D hC hD hCD).2
    simpa only [primary_span_supported D hD] using hh
  have hgc:=CenteredMomentFirstSourceConductorCaps.divisor_norm_le _ D hD.1 hdiv
  have hh:=physicalBlock_scale_lower η t S β C D hC hD U R rows W K n a H ha hlower hne
  have hl:a*H/(C.absNorm:ℝ)≤dyadicScale (n 2):=by
    have hv':=(le_div_iff₀ ha).mp hh.1
    convert hv' using 1 ; ring
  have hr:a*H/(D.absNorm:ℝ)≤dyadicScale (n 3):=by
    have hv':=(le_div_iff₀ ha).mp hh.2
    convert hv' using 1 ; ring
  have hs:=effective_upper η t S β C D hC hD U R rows W K n hne
  have he:secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K=
      K*(Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)*
        Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U})/((C.absNorm:ℝ)*D.absNorm):=by
    simp only [secondEffectiveScale,map_mul,norm_mul,mul_pow,
      ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    ring
  rw [he] at hs
  have hs':dyadicScale (n 0)≤4*(K*(Ideal.span {commonFrequencyGenerator C D}).absNorm*
      (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm/((D.absNorm:ℝ)*C.absNorm)):=by
    simpa only [mul_comm (C.absNorm:ℝ) (D.absNorm:ℝ)] using hs
  have hh':=scalar_capacity_shift Z (fixedFactor:ℝ) qref
    ((∏P∈U,P.val).absNorm:ℝ) ((Ideal.span {nonunitFrequencyGenerator C D U}).absNorm:ℝ)
    H K a (D.absNorm:ℝ) (C.absNorm:ℝ) (dyadicScale (n 0)) (dyadicScale (n 1))
    (dyadicScale (n 3)) (dyadicScale (n 2)) hZ hf hq hu1 hv hH hK ha hd hc
    (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _)
    ((Ideal.span {commonFrequencyGenerator C D}).absNorm:ℝ) hg hgc hs' hr hl
  simpa only [adjustedEnvelopeRef,mul_comm (dyadicScale (n 3)) (dyadicScale (n 2))] using hh'

theorem actual_capacity_shift (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K H a Z:ℝ)(n:Fin 4→ℤ)
    (hK:0<K)(hH:0<H)(ha:0<a)(hZ:1<Z)
    (hlower:∀I:Ideal O,β I≠0→a*H≤(I.absNorm:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0):
    Real.logb Z (H/(C.absNorm:ℝ))-Real.logb Z (adjustedEnvelope η C D U n)≤
      Real.logb Z K-Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z H+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2)):=
  actual_capacity_shift_reference η t S β C D hC hD hCD U R rows W K H a Z
    (η.modulus.absNorm:ℝ) n (CenteredMomentFirstScale.norm_pos η.modulus η.modulus_ne_bot)
    hK hH ha hZ hlower hne

end SevenEighths.CenteredMomentSecondCapacitySourceShift

end

end OAI
