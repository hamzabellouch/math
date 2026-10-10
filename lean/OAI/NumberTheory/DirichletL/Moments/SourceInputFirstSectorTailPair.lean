import OAI.NumberTheory.DirichletL.Moments.SourceInputFirstTailScale

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceInputFirstSectorTail
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson ConcretePrimeRowBridge
open CenteredMomentFirstReduced CenteredMomentSectorLocalization CenteredMomentCorrelation
open CenteredMomentCommonSupport CenteredMomentCanonicalFirst CenteredMomentSupportedCorrelation
open CenteredMomentFirstScale CenteredMomentFirstDiscarded CenteredMomentActive
open CenteredMomentCompleteCommon IdealMobiusDivisorSum CenteredMomentFirstDiscardedEnergy
open CenteredMomentSourceInputFirstTailUniform
local notation "O"=>ActualEisensteinCubic.O

lemma local_tail_denominator_mono (Tlocal Tupper H Z ξ:ℝ)(A:ℕ)(B:ℝ)
    (hT:0<Tlocal)(hupper:Tlocal≤Tupper)(hB:0≤B)(hZ:0≤Z):
    B/((min 1 (kernelReference Tlocal H))^2*(1+Z^(ξ/4))^A)≤
      B/((min 1 (kernelReference Tupper H))^2*(1+Z^(ξ/4))^A):=by
  have hu:0<Tupper:=hT.trans_le hupper
  have hk:kernelReference Tupper H≤kernelReference Tlocal H:=by
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hT hupper
  have hm:0<min 1 (kernelReference Tupper H):=lt_min zero_lt_one (kernelReference_pos _ _ hu)
  have hp:0≤Z^(ξ/4):=Real.rpow_nonneg hZ _
  apply div_le_div_of_nonneg_left hB (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact pow_le_pow_left₀ hm.le (min_le_min_left 1 hk) 2

theorem local_discarded_pair_bound (A : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ),0<C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (I J : Ideal O)
        (hI : CanonicalQuadraticSieve.Supported I) (hJ : CanonicalQuadraticSieve.Supported J)
        (K X HN Tsec Z Csec ξ : ℝ),
      0<K → 0<X → 1<Z → 1≤Csec →
      (Ideal.absNorm I:ℝ)≤Real.exp HN*X → (Ideal.absNorm J:ℝ)≤Real.exp HN*X →
      X^2/K≤Tsec →
      (2*HN/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖∑ E∈inactiveSubsets I J,canonicalDiscardedTerm I J hI hJ E W K
        (firstNominalScale I J (∏ P∈E,P.val) K X) Z ξ‖ ≤
      (Ideal.absNorm I:ℝ)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := canonical_discarded_term_bound A
  obtain ⟨D,hD,hsub⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨s,D*C,mul_pos hD hC,?_⟩
  intro W I J hI hJ K X HN Tsec Z Csec ξ hK hX hZ hCs hi hj hsec hthreshold
  have hc : ((inactiveSubsets I J).card:ℝ)≤D*(Ideal.absNorm I:ℝ)^ε := by
    apply le_trans _ (hsub I hI.1)
    exact_mod_cast inactiveSubsets_card I J
  calc
    _ ≤ ∑ E∈inactiveSubsets I J,‖canonicalDiscardedTerm I J hI hJ E W K
        (firstNominalScale I J (∏ P∈E,P.val) K X) Z ξ‖ := norm_sum_le _ _
    _ ≤ ∑ _E∈inactiveSubsets I J,
        K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A) :=
      Finset.sum_le_sum (fun E hE => by
        let Tlocal:=firstNominalScale I J (∏ P∈E,P.val) K X
        have hE0:(∏ P∈E,P.val)≠(0:Ideal O):=by
          have he:=primeSubsetGenerator_ne_zero (fun P:CommonIndex I J=>P.val) E
          have hh:=Ideal.span_singleton_eq_bot.not.mpr he
          simpa only [primeSubsetGenerator,span_idealGenerator,Ideal.zero_eq_bot] using hh
        have hTl:0<Tlocal:=firstNominalScale_pos I J _ hE0 K X hK hX
        have hTu:Tlocal≤Tsec:=(first_nominal_scale_le I J E K X hK).trans hsec
        have hh:=ht W I J hI hJ E K X HN Tlocal Z Csec ξ hK hX hZ hCs hi hj le_rfl hthreshold
        exact hh.trans (local_tail_denominator_mono Tlocal Tsec HN Z ξ A
          (K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)) hTl hTu (by positivity) (zero_lt_one.trans hZ).le))
    _ = ((inactiveSubsets I J).card:ℝ)*
        (K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A)) := by simp
    _ ≤ (D*(Ideal.absNorm I:ℝ)^ε)*
        (K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

end SevenEighths.CenteredMomentSourceInputFirstSectorTail

end

end OAI
