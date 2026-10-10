import OAI.NumberTheory.DirichletL.Moments.PlainGlobalEnergy
import OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceFamily

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentNaturalCoreFloor
open HeckeFamily HeckeRowClosure CenteredMomentCoreFloor CenteredMomentPlainGlobalEnergy
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentRadialEligibleEnergy (Radial)
open QuadraticInitialBound ConcreteTraceCRT
local notation "O"=>HeckeFamily.O

 theorem natural_zero_all_lengths_floor (a b:ℝ)(ha:0<a):
    ∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
    ∀(W₁ W₂:SchwartzMap ℝ ℂ),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b→
    ∀(η:Character)(Q:Ideal O)(r:Radial)(bΦ:ℝ),0≤bΦ→
      (Function.support (r.profile:ℝ→ℂ)⊆Set.Iic bΦ)→
      (∀z,r.keep z→z≠0)→
      (∀z,r.keep z→¬FixedInducingRow η Q fixedBadMask 1 z)→
    ∀(Z m q ρ t X₁ X₂:ℝ),1≤Z→0≤m→0≤q→
      r.scale=Z^m→m+q≤ρ→1≤X₁→1≤X₂→
      (η.modulus.absNorm:ℝ)≤Z^q→
    zeroEnergy η fixedBadMask 1 t W₁ W₂ X₁ X₂ r≤
      C*bΦ^4*diagonalControl r.profile*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*(3+|t|)^8*Z^(m+q+4*ρ):=by
  obtain ⟨S,C,hC,hfloor⟩:=zero_all_lengths_floor a b ha
  let F:ℝ:=fixedConductorFactor
  have hF:0<F:=by
    unfold F fixedConductorFactor
    norm_cast
    apply Nat.mul_pos
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0)))
  refine ⟨S,C*F^4,mul_pos hC (pow_pos hF _),?_⟩
  intro W₁ W₂ hs₁ hs₂ η Q r bΦ hbΦ hΦsupp hz hex Z m q ρ t X₁ X₂ hZ hm hq hscale hwidth hX₁ hX₂ hη
  let r':Radial:={r with keep:=fun z=>r.keep z ∧ r.profile (‖eisEmbedding z‖^2/r.scale)≠0}
  let χ:O→Character:=fun z=>if hz:z≠0 then (naturalRow η z hz).character else η
  have hrow (z:O)(h:r'.keep z):∀n,elementCoeff (χ z) n=
      CanonicalRowCompletion.rowTwist (elementHom η) fixedBadMask 1 (1*z) n:=by
    have hz0:=hz z h.1
    simpa only [χ,dite_eq_left hz0,one_mul] using (naturalRow η z hz0).element
  have hnon (z:O)(h:r'.keep z):(χ z).residue≠1:=
    CenteredMomentNonprincipalGate.actual_row_nonprincipal η (χ z) Q fixedBadMask 1 z
      (hrow z h) (hex z h.1)
  have hmod (z:O)(h:r'.keep z):((χ z).modulus.absNorm:ℝ)≤(F*bΦ)*Z^(m+q):=by
    have hz0:=hz z h.1
    have hs:‖eisEmbedding z‖^2/r.scale≤bΦ:=hΦsupp h.2
    have hn:((Ideal.span {z}).absNorm:ℝ)≤bΦ*Z^m:=by
      rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
      rw [←hscale]
      exact (div_le_iff₀ r.scale_pos).mp hs
    have hh:=(naturalRow η z hz0).modulus_power_bound Z q m bΦ
      (zero_lt_one.trans_le hZ) hbΦ hη hn
    simpa only [χ,dite_eq_left hz0,add_comm q m] using hh
  have he:=hfloor W₁ W₂ hs₁ hs₂ η fixedBadMask 1 r' χ hnon hrow
    Z m q ρ (F*bΦ) t X₁ X₂ hZ hm hq (mul_nonneg hF.le hbΦ) hscale hwidth hX₁ hX₂ hmod
  have heq:zeroEnergy η fixedBadMask 1 t W₁ W₂ X₁ X₂ r=
      zeroEnergy η fixedBadMask 1 t W₁ W₂ X₁ X₂ r':=by
    unfold zeroEnergy
    apply tsum_congr
    intro z
    by_cases hk:r.keep z
    · by_cases hp:r.profile (‖eisEmbedding z‖^2/r.scale)=0
      · simp [r',hk,hp]
      · simp [r',hk,hp]
    · simp [r',hk]
  rw [heq]
  exact he.trans_eq (by dsimp [r'];ring)

end SevenEighths.CenteredMomentNaturalCoreFloor

end

end OAI
