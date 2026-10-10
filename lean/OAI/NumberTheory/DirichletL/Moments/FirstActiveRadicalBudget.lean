import OAI.NumberTheory.DirichletL.Moments.FirstInactiveRadicalMass

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstActiveRadicalBudget
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentActive
open CenteredMomentRankinRadical CenteredMomentFirstInactiveRadicalMass
open CenteredMomentSupportedCorrelation
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentActiveSource CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonRadialData
local notation "O"=>ActualEisensteinCubic.O

lemma active_exponent_budget (i j:ℕ)(hi:0 < i)(hj:0 < j):
    2+(if netExponent i j≠0 then 1 else 0) ≤ i+j:=by
  unfold netExponent
  split_ifs <;> omega

theorem radical_squared_active_dvd (I J:Ideal O):
    commonRadical I J^2*Ideal.span {activeConductor I J}∣commonPart I J*commonPart J I:=by
  have hr:commonRadical I J=∏P:CommonIndex I J,P.val:=by
    exact (Finset.prod_coe_sort (s:=commonSupport I J) (f:=fun P=>P)).symm
  have ha:Ideal.span {activeConductor I J}=
      ∏P:CommonIndex I J,if netExponent (leftExponent I J P) (rightExponent I J P)≠0 then P.val else 1:=by
    rw [activeConductor,span_finitePrimeModulus]
    change (∏P:ActiveIndex I J,P.val.val)=_
    rw [Finset.prod_coe_sort]
    simp only [ActiveIndex,CenteredMomentActive.activeSupport,Finset.prod_filter]
  rw [hr,ha,←Finset.prod_pow,←Finset.prod_mul_distrib,
    commonPart_left_product,commonPart_right_product,←Finset.prod_mul_distrib]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  have hh:=active_exponent_budget (leftExponent I J P) (rightExponent I J P)
    (leftExponent_pos I J P) (rightExponent_pos I J P)
  rw [←pow_add]
  convert pow_dvd_pow P.val hh using 1
  split_ifs <;> simp [pow_succ]

theorem radical_active_norm (I J:Ideal O)(hI:I≠0)(hJ:J≠0):
    (Ideal.absNorm (commonRadical I J):ℝ)^2*
      (Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)≤(I.absNorm:ℝ)*J.absNorm:=by
  have hd:commonRadical I J^2*Ideal.span {activeConductor I J}∣I*J:=
    (radical_squared_active_dvd I J).trans (mul_dvd_mul (commonPart_dvd I J hI) (commonPart_dvd J I hJ))
  have hn:=Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (mul_ne_zero hI hJ)))
    (map_dvd Ideal.absNorm hd)
  simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using (show
    (Ideal.absNorm (commonRadical I J^2*Ideal.span {activeConductor I J}):ℝ)≤
      (Ideal.absNorm (I*J):ℝ) by exact_mod_cast hn)

theorem active_root_le_radical (I J:Ideal O)(hI:I≠0)(hJ:J≠0):
    Real.sqrt (Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)/
      Real.sqrt ((I.absNorm:ℝ)*J.absNorm)≤1/(Ideal.absNorm (commonRadical I J):ℝ):=by
  have hR:0<(Ideal.absNorm (commonRadical I J):ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonRadical_ne_zero I J))
  have hN:0<(I.absNorm:ℝ)*J.absNorm:=mul_pos
    (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
    (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ))
  have hh:=Real.sqrt_le_sqrt (radical_active_norm I J hI hJ)
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hR.le] at hh
  exact (div_le_div_iff₀ (Real.sqrt_pos.mpr hN) hR).mpr (by simpa [mul_comm] using hh)

theorem actual_first_weighted_mass (B ε:ℝ)(hB:0≤B)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀Z:ℝ,2≤Z→∀seed:Ideal O,Squarefree seed→seed≠0→
      ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
      (∀I∈S,β I≠0→seed∣I)→(∀I∈S,β I≠0→(I.absNorm:ℝ)≤Z^B)→
      ∀a:ℝ,0≤a→
      (∑p:ActiveLabel S β,∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,
        inactiveWeight p.val.1 p.val.2 E a*
          (Real.sqrt (Ideal.absNorm (Ideal.span {activeConductor p.val.1 p.val.2}):ℝ)/
            Real.sqrt ((p.val.1.absNorm:ℝ)*p.val.2.absNorm)))≤C*Z^ε/(seed.absNorm:ℝ):=by
  obtain ⟨C,hC,hb⟩:=actual_inactive_radical_mass B ε hB hε
  refine ⟨C,hC,?_⟩
  intro Z hZ seed hs hs0 S β hm hn a ha
  apply le_trans _ (hb Z hZ seed hs hs0 S β hm hn a ha)
  apply Finset.sum_le_sum
  intro p hp
  have hsupp:=commonLabels_supported (activeSource S β) _ _ p.property
  apply Finset.sum_le_sum
  intro E hE
  exact (mul_le_mul_of_nonneg_left (active_root_le_radical _ _ hsupp.1.1 hsupp.2.1)
    (inactiveWeight_nonneg _ _ E a)).trans_eq (by ring)

theorem original_first_weighted_mass (B ε:ℝ)(hB:0≤B)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀Z:ℝ,2≤Z→∀(ι:Type*)[Fintype ι][DecidableEq ι](s:Input ι),
      s.W₁ 0=0→s.W₂ 0=0→sourceRadius s≤Z^B→
      ∀puncture seed:Ideal O,Squarefree seed→seed≠0→∀a:ℝ,0≤a→
      (∑p:ActiveLabel (finiteColumns (Fintype.piFinset s.pools)) (coefficient s puncture seed),
        ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,
          inactiveWeight p.val.1 p.val.2 E a*
            (Real.sqrt (Ideal.absNorm (Ideal.span {activeConductor p.val.1 p.val.2}):ℝ)/
              Real.sqrt ((p.val.1.absNorm:ℝ)*p.val.2.absNorm)))≤C*Z^ε/(seed.absNorm:ℝ):=by
  obtain ⟨C,hC,hb⟩:=actual_first_weighted_mass B ε hB hε
  refine ⟨C,hC,?_⟩
  intro Z hZ ι _ _ s hz₁ hz₂ hcap puncture seed hs hs0 a ha
  exact hb Z hZ seed hs hs0 _ _
    (fun I _ hI=>original_column_mask s puncture seed I hI)
    (fun I _ hI=>(original_column_norm s puncture seed I hz₁ hz₂ hI).2.trans hcap) a ha

end SevenEighths.CenteredMomentFirstActiveRadicalBudget

end

end OAI
