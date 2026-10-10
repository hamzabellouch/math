import Mathlib
import OAI.NumberTheory.Jacobsthal.Paths.TagIntersectionError
import OAI.NumberTheory.Jacobsthal.Paths.TagRelativeAlgebra
import OAI.NumberTheory.Jacobsthal.Primes.TagSubbinPrimeLower
import OAI.NumberTheory.Jacobsthal.Sieve.EulerProductRatio

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosStoppedTagSieve

open scoped BigOperators

noncomputable def primeFactor (p : ℕ) : ℝ := 1-1/((p:ℝ)-1)
noncomputable def eulerWeight (S : Finset ℕ) : ℝ := ∏ p∈S,primeFactor p

lemma shifted_nonneg (k : ℕ) : 0 ≤ (1:ℝ)-1/((k:ℝ)+2) := by
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hh : (0:ℝ) < (k:ℝ)+2 := by positivity
  have h := (div_le_one hh).mpr (show (1:ℝ) ≤ (k:ℝ)+2 by linarith)
  linarith

lemma shifted_le_one (k : ℕ) : (1:ℝ)-1/((k:ℝ)+2) ≤ 1 := by
  have : (0:ℝ) ≤ 1/((k:ℝ)+2) := by positivity
  linarith

lemma shifted_product (N : ℕ) :
    (∏ k∈Finset.range N,((1:ℝ)-1/((k:ℝ)+2)))=1/((N:ℝ)+1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.prod_range_succ,ih]
    push_cast
    have h1 : (N:ℝ)+1 ≠ 0 := by positivity
    have h2 : (N:ℝ)+2 ≠ 0 := by positivity
    field_simp
    ring

theorem eulerWeight_lower (P : ℝ) (hP : 3 ≤ P) (S : Finset ℕ)
    (hS : ∀ p∈S,3 ≤ p ∧ (p:ℝ) ≤ P) : 1/P ≤ eulerWeight S := by
  classical
  have hP0 : 0 ≤ P := by linarith
  have hf : 3 ≤ ⌊P⌋₊ := (Nat.le_floor_iff hP0).mpr (by exact_mod_cast hP)
  let N := ⌊P⌋₊-2
  have hsub : (S.image (fun p : ℕ => (p-3:ℕ)) : Finset ℕ) ⊆ Finset.range N := by
    intro k hk
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hk
    have hpl : p ≤ ⌊P⌋₊ := (Nat.le_floor_iff hP0).mpr (hS p hp).2
    have hp3 := (hS p hp).1
    apply Finset.mem_range.mpr
    dsimp [N]
    omega
  have hnP : (N:ℝ)+1 ≤ P := by
    dsimp [N]
    rw [Nat.cast_sub (by omega)]
    have hfl := Nat.floor_le hP0
    norm_num only [Nat.cast_ofNat]
    linarith
  have hprod := Finset.prod_le_prod_of_subset_of_le_one₀ hsub
    (fun k _ => shifted_nonneg k) (fun k _ _ => shifted_le_one k)
  have himage : (∏ k∈(S.image (fun p : ℕ => (p-3:ℕ)) : Finset ℕ),((1:ℝ)-1/((k:ℝ)+2)))=eulerWeight S := by
    rw [Finset.prod_image (fun p hp q hq he => by have := (hS p hp).1; have := (hS q hq).1; omega)]
    apply Finset.prod_congr rfl
    intro p hp
    dsimp [primeFactor]
    rw [Nat.cast_sub (hS p hp).1]
    norm_num only [Nat.cast_ofNat]
    ring
  rw [himage,shifted_product] at hprod
  exact (one_div_le_one_div_of_le (by positivity) hnP).trans hprod

end ErdosStoppedTagSieve



namespace ErdosStoppedTagSieve


lemma primeFactor_nonneg (p : ℕ) (hp : 2 ≤ p) : 0 ≤ primeFactor p := by
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hden : 0 < (p:ℝ)-1 := by linarith
  have hh := (div_le_one hden).mpr (show (1:ℝ) ≤ (p:ℝ)-1 by linarith)
  unfold primeFactor
  linarith

lemma primeFactor_le_one (p : ℕ) (hp : 2 ≤ p) : primeFactor p ≤ 1 := by
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp
  have h : (0:ℝ) ≤ 1/((p:ℝ)-1) := div_nonneg (by norm_num) (by linarith)
  unfold primeFactor
  linarith

lemma eulerWeight_nonneg (S : Finset ℕ) (hS : ∀ p∈S,2 ≤ p) : 0 ≤ eulerWeight S :=
  Finset.prod_nonneg (fun p hp => primeFactor_nonneg p (hS p hp))

lemma eulerWeight_le_one (S : Finset ℕ) (hS : ∀ p∈S,2 ≤ p) : eulerWeight S ≤ 1 :=
  Finset.prod_le_one₀ (fun p hp => primeFactor_nonneg p (hS p hp))
    (fun p hp => primeFactor_le_one p (hS p hp))

lemma eulerWeight_eq_zero_of_two (S : Finset ℕ) (hS : 2∈S) : eulerWeight S=0 := by
  apply Finset.prod_eq_zero hS
  norm_num [primeFactor]

lemma odd_of_eulerWeight_ne_zero (S : Finset ℕ) (hS : ∀ p∈S,2 ≤ p)
    (hne : eulerWeight S≠0) : ∀ p∈S,3 ≤ p := by
  intro p hp
  have hp2 := hS p hp
  by_contra h
  have he : p=2 := by omega
  subst p
  exact hne (eulerWeight_eq_zero_of_two S hp)

lemma reciprocal_totient_density_le (p : ℕ) (hp : 2 ≤ p) : 1/((p:ℝ)-1) ≤ 2/(p:ℝ) := by
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp
  apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
  linarith





open scoped BigOperators
open Erdos970Dependency.SiegelWalfisz
open NumberTheoryLean
attribute [local instance] Classical.propDecidable

noncomputable def basePrimes (R V : ℝ) (Q : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (intervalPrimes R V 1 0).filter (fun p => p%Q∈A)
noncomputable def survivorPrimes (R V : ℝ) (Q : ℕ) (S A : Finset ℕ)
    (rho : (t : ℕ) → ZMod t) : Finset ℕ :=
  (basePrimes R V Q A).filter (fun p => ∀ t∈S,(p:ZMod t)≠rho t)

lemma actual_intersection_mass (R V : ℝ) (Q : ℕ) (T A : Finset ℕ)
    (rho : (t : ℕ) → ZMod t) :
    BonferroniBlocks.intersectionMass (basePrimes R V Q A) (fun _ => 1)
      (fun t p => (p:ZMod t)=rho t) T = ((intersectionPrimes R V Q T A rho).card:ℝ) := by
  simp only [BonferroniBlocks.intersectionMass,BonferroniBlocks.intersectionValue,one_mul]
  have he : (basePrimes R V Q A).filter (fun p => ∀ t∈T,(p:ZMod t)=rho t)=intersectionPrimes R V Q T A rho := by
    ext p
    simp only [basePrimes,intersectionPrimes,Finset.mem_filter]
    tauto
  rw [← he]
  rw [Finset.natCast_card_filter (R := ℝ)]
  apply Finset.sum_congr rfl
  intro p _hp
  split_ifs <;> rfl

lemma actual_survivor_mass (R V : ℝ) (Q : ℕ) (S A : Finset ℕ)
    (rho : (t : ℕ) → ZMod t) :
    (∑ p∈basePrimes R V Q A, (1:ℝ)*BonferroniBlocks.survives S (fun t => (p:ZMod t)=rho t))=
      ((survivorPrimes R V Q S A rho).card:ℝ) := by
  simp only [BonferroniBlocks.survives,one_mul,survivorPrimes]
  rw [Finset.natCast_card_filter (R := ℝ)]
  apply Finset.sum_congr rfl
  intro p _hp
  split_ifs <;> rfl

theorem finite_tag_sieve_error :
    ∃ c C X₀ : ℝ,0 < c ∧ 0 < C ∧ 3 ≤ X₀ ∧
      ∀ R V : ℝ,X₀ ≤ R → 0 ≤ V → V ≤ R → ∀ Q : ℕ,0 < Q →
      ∀ S A : Finset ℕ,∀ rho : (t : ℕ) → ZMod t,
      (∀ t∈S,t.Prime) → (∀ t∈S,3 ≤ t) → (∀ t∈S,Q.Coprime t) →
      (∀ a∈A,a<Q) → (∀ a∈A,a.Coprime Q) → (∀ t∈S,rho t≠0) →
      ∀ u s : ℝ,3 ≤ u → 480024 ≤ s → (∀ t∈S,(t:ℝ) ≤ u) →
      (Q:ℝ)*u^s ≤ Real.exp (c*cubeHeight R) →
      let X : ℝ := ((intervalPrimes R V 1 0).card:ℝ)*(A.card:ℝ)/(Q.totient:ℝ)
      |((survivorPrimes R V Q S A rho).card:ℝ)-X*eulerWeight S| ≤
        X*eulerWeight S*Real.exp (-s/96)+(A.card:ℝ)*C*R*(u^s)*Real.exp (-c*cubeHeight R) := by
  obtain ⟨c,C,X₀,hc,hC,hX₀,hAP⟩ := intersection_prime_error
  refine ⟨c,C,X₀,hc,hC,hX₀,?_⟩
  intro R V hR hV hVR Q hQ S A rho hPrime hOdd hQS hA hAc hrho u s hu hs hsize hlevel X
  let g : ℕ → ℝ := fun t => 1/((t:ℝ)-1)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hR0 : 0 ≤ R := by have := hX₀.trans hR; linarith
  have hg : ∀ t∈S,0 ≤ g t := by
    intro t ht
    have htR : (3:ℝ) ≤ t := by exact_mod_cast hOdd t ht
    exact div_nonneg (by norm_num) (by linarith)
  have hdim : ∀ t∈S,g t ≤ 2/(t:ℝ) := fun t ht => reciprocal_totient_density_le t (by have := hOdd t ht; omega)
  have htwo : 2∈S → g 2 ≤ 1/2 := by intro h; have := hOdd 2 h; omega
  have hf := RealFundamentalSieve.fundamental_lemma (basePrimes R V Q A) (fun _ => 1)
    (fun _ _ => by norm_num) (fun t p => (p:ZMod t)=rho t) u s S X g
    (by linarith) hs hX hPrime hsize hg hdim htwo
  have hEuler : (∏ t∈S,(1-g t))=eulerWeight S := rfl
  rw [actual_survivor_mass,hEuler] at hf
  have hRem : ∀ d∈RealFundamentalSieve.levelDivisors S u s,
      |FundamentalBlockEstimate.integerRemainder (basePrimes R V Q A) (fun _ => 1)
        (fun t p => (p:ZMod t)=rho t) X g d| ≤ (A.card:ℝ)*C*R*Real.exp (-c*cubeHeight R) := by
    intro d hd
    obtain ⟨hdP,hdL⟩ := Finset.mem_filter.mp hd
    have hddiv := Nat.dvd_of_mem_divisors hdP
    have hsq := IntervalBoundingSieve.squarefree_primeSet_product S hPrime
    have hdsq := hsq.squarefree_of_dvd hddiv
    have hsub : d.primeFactors ⊆ S := by
      rw [← Nat.primeFactors_prod hPrime]
      exact Nat.primeFactors_mono hddiv hsq.ne_zero
    have hm : (Q*(∏ t∈d.primeFactors,t):ℕ) ≤ Real.exp (c*cubeHeight R) := by
      rw [Nat.prod_primeFactors_of_squarefree hdsq,Nat.cast_mul]
      exact (mul_le_mul_of_nonneg_left hdL (Nat.cast_nonneg Q)).trans hlevel
    have hh := hAP R V hR hV hVR Q hQ d.primeFactors A rho
      (fun t ht => hPrime t (hsub ht)) (fun t ht => hQS t (hsub ht))
      hA hAc (fun t ht => hrho t (hsub ht)) hm
    unfold FundamentalBlockEstimate.integerRemainder BonferroniBlocks.intersectionRemainder
    rw [actual_intersection_mass]
    exact hh
  have hSum : (∑ d∈RealFundamentalSieve.levelDivisors S u s,
      |FundamentalBlockEstimate.integerRemainder (basePrimes R V Q A) (fun _ => 1)
        (fun t p => (p:ZMod t)=rho t) X g d|) ≤
      (A.card:ℝ)*C*R*(u^s)*Real.exp (-c*cubeHeight R) := by
    calc
      _ ≤ ∑ _d∈RealFundamentalSieve.levelDivisors S u s,
        (A.card:ℝ)*C*R*Real.exp (-c*cubeHeight R) := Finset.sum_le_sum hRem
      _ = ((RealFundamentalSieve.levelDivisors S u s).card:ℝ)*((A.card:ℝ)*C*R*Real.exp (-c*cubeHeight R)) := by
        rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ (u^s)*((A.card:ℝ)*C*R*Real.exp (-c*cubeHeight R)) :=
        mul_le_mul_of_nonneg_right (SmallSieveFinite.realLevelDivisors_card_le S u s (by linarith)) (by positivity)
      _ = _ := by ring
  exact hf.trans (add_le_add le_rfl hSum)

end ErdosStoppedTagSieve



namespace ErdosStoppedTagSieve

open _root_.Filter
open scoped Topology BigOperators
open Erdos970Dependency.SiegelWalfisz ErdosUnitLifts

theorem unit_lift_sieve_lower_eventually (Cs K xi gamma : ℝ)
    (hCs : 0 ≤ Cs) (hK : 0 ≤ K) (hxi : 0 < xi) (hgamma : 0 < gamma) :
    ∀ᶠ w : ℝ in atTop,3 ≤ w ∧ ∀ P R V : ℝ,3 ≤ P → P ≤ Real.exp (K*(Real.log w)^3) →
      Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R →
      xi/(16*w^(2*Cs+10)) ≤ V/R → V/R ≤ w^(-(2*Cs+10)) →
      ∀ D : ℕ,0 < D → (D:ℝ) ≤ w^Cs → ∀ A B : ℤ,∀ residue : ℕ → ℤ,
      IsUnit (A:ZMod D) → IsUnit (B:ZMod D) → ∀ S : Finset ℕ,∀ rho : (t : ℕ) → ZMod t,
      (∀ t∈S,t.Prime) → (∀ t∈S,(t:ℝ) ≤ P) → (∀ t∈S,¬t∣D) → (∀ t∈S,rho t≠0) →
      (1-gamma)*(((intervalPrimes R V 1 0).card:ℝ)/(D:ℝ))*eulerWeight S ≤
        ((survivorPrimes R V (D*radical D) S (actualClasses D A B residue) rho).card:ℝ) := by
  obtain ⟨c,C,X₀,hc,hC,hX₀,hSieve⟩ := finite_tag_sieve_error
  let s : ℝ := max 480024 (-96*Real.log (gamma/2))
  have hs : 480024 ≤ s := le_max_left _ _
  have hs0 : 0 ≤ s := by linarith
  have hrel : Real.exp (-s/96) ≤ gamma/2 := by
    have hh := le_max_right (480024:ℝ) (-96*Real.log (gamma/2))
    change -96*Real.log (gamma/2) ≤ s at hh
    calc
      _ ≤ Real.exp (Real.log (gamma/2)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := Real.exp_log (by positivity)
  obtain ⟨Wn,_hWn,hNlower⟩ := moving_subbin_prime_lower Cs xi hCs hxi
  have hMod := eventually_moving_exponential_domination (2*Cs) s K c (by linarith) hs0 hK hc
  have hRate := eventually_moving_error (4*Cs+10) (s+1) K c (64*C/xi) (gamma/2)
    (by linarith) (by linarith) hK hc (by positivity) (by positivity)
  filter_upwards [eventually_ge_atTop (max Wn X₀),hMod,hRate] with w hw hwMod hwRate
  refine ⟨hwMod.1,?_⟩
  intro P R V hP hPcap hRscale hlo hhi D hD hDw A B residue hAunit hBunit S rho hPrime hsize hSD hrho
  let Q := D*radical D
  let Cls := actualClasses D A B residue
  let N : ℝ := (intervalPrimes R V 1 0).card
  have hw3 := hwMod.1
  have hw0 : 0 < w := by linarith
  have hP0 : 0 < P := by linarith
  have hD0 : (0:ℝ) < D := by exact_mod_cast hD
  have hQ : 0 < Q := Nat.mul_pos hD (radical_pos D)
  obtain ⟨hR0,hV0,hVR,hN,hN0⟩ := hNlower w R V ((le_max_left _ _).trans hw) hRscale hlo hhi
  have hRw : w ≤ R := (moving_lower_ge_self (by linarith)).trans hRscale
  have hRX : X₀ ≤ R := ((le_max_right _ _).trans hw).trans hRw
  have hR3 : 3 ≤ R := hw3.trans hRw
  have hL : 0 < Real.log R := Real.log_pos (by linarith)
  have hWnonneg : 0 ≤ eulerWeight S := eulerWeight_nonneg S (fun t ht => (hPrime t ht).two_le)
  by_cases hzero : eulerWeight S=0
  · rw [hzero,mul_zero]
    exact Nat.cast_nonneg _
  have hOdd : ∀ t∈S,3 ≤ t := odd_of_eulerWeight_ne_zero S (fun t ht => (hPrime t ht).two_le) hzero
  have hEW : 1/P ≤ eulerWeight S := eulerWeight_lower P hP S (fun t ht => ⟨hOdd t ht,hsize t ht⟩)
  have hQS : ∀ t∈S,Q.Coprime t := by
    intro t ht
    have hdt := ((hPrime t ht).coprime_iff_not_dvd.mpr (hSD t ht)).symm
    exact Nat.coprime_mul_iff_left.mpr ⟨hdt,Nat.Coprime.coprime_dvd_left (radical_dvd D) hdt⟩
  have hCls : ∀ a∈Cls,a<Q ∧ a.Coprime Q := fun a ha =>
    actualClasses_reduced D hD A B residue hAunit hBunit a ha
  have hlevel : (Q:ℝ)*P^s ≤ Real.exp (c*cubeHeight R) :=
    (mul_le_mul_of_nonneg_right (lift_modulus_bound hw0 hD hDw) (Real.rpow_nonneg hP0.le s)).trans
      (hwMod.2 P R (by linarith) hPcap hRscale)
  have hf := hSieve R V hRX hV0.le hVR Q hQ S Cls rho hPrime hOdd hQS
    (fun a ha => (hCls a ha).1) (fun a ha => (hCls a ha).2) hrho P s hP hs hsize hlevel
  have hXeq : N*(Cls.card:ℝ)/(Q.totient:ℝ)=N/(D:ℝ) := by
    calc
      _ = N*((Cls.card:ℝ)/(Q.totient:ℝ)) := by ring
      _ = N*(1/(D:ℝ)) := by rw [actualClasses_fraction_real D hD A B residue hBunit]
      _ = _ := by ring
  dsimp only at hf
  change |((survivorPrimes R V Q S Cls rho).card:ℝ)-(N*(Cls.card:ℝ)/(Q.totient:ℝ))*eulerWeight S| ≤ _ at hf
  rw [hXeq] at hf
  have hNV : xi*R/(64*w^(2*Cs+10)*Real.log R) ≤ N := by
    have hv := (le_div_iff₀ hR0).mp hlo
    have hh := div_le_div_of_nonneg_right hv (show 0 ≤ 4*Real.log R by positivity)
    have he : ((xi/(16*w^(2*Cs+10)))*R)/(4*Real.log R)=xi*R/(64*w^(2*Cs+10)*Real.log R) := by ring
    rw [he] at hh
    exact hh.trans hN
  have hCard : (Cls.card:ℝ) ≤ D := by exact_mod_cast actualClasses_card_le D hD A B residue hBunit
  have hrem := relative_remainder_bound (Cls.card:ℝ) (D:ℝ) (w^Cs) N (eulerWeight S)
    (w^(2*Cs+10)) P (Real.log R) R C (P^s) (Real.exp (-c*cubeHeight R)) xi
    (Nat.cast_nonneg _) hCard hD0 hDw (by positivity) hP0 hL hR0 hC.le
    (Real.rpow_nonneg hP0.le s) (Real.exp_pos _).le hxi hNV hEW
  have hwPower : (w^Cs)^2*w^(2*Cs+10)=w^(4*Cs+10) := by
    rw [← Real.rpow_mul_natCast hw0.le,← Real.rpow_add hw0]
    congr 1
    norm_num
    ring
  have hPPower : P*(P^s)=P^(s+1) := by rw [Real.rpow_add_one hP0.ne']; ring
  have hshape : (64*C/xi)*(w^Cs)^2*w^(2*Cs+10)*P*(P^s)*Real.log R*Real.exp (-c*cubeHeight R)=
      (64*C/xi)*w^(4*Cs+10)*P^(s+1)*Real.log R*Real.exp (-c*cubeHeight R) := by
    calc
      _ = (64*C/xi)*((w^Cs)^2*w^(2*Cs+10))*(P*(P^s))*Real.log R*Real.exp (-c*cubeHeight R) := by ring
      _ = _ := by rw [hwPower,hPPower]
  rw [hshape] at hrem
  have hr := hwRate.2 P R (by linarith) hPcap hRscale
  have hmu : 0 ≤ (N/(D:ℝ))*eulerWeight S := mul_nonneg (div_nonneg hN0.le hD0.le) hWnonneg
  have hrem' := hrem.trans (mul_le_mul_of_nonneg_left hr hmu)
  have hrel' := mul_le_mul_of_nonneg_left hrel hmu
  have hAbs := hf.trans (add_le_add hrel' hrem')
  have hLower := (abs_le.mp hAbs).1
  change (1-gamma)*(N/(D:ℝ))*eulerWeight S ≤ ((survivorPrimes R V Q S Cls rho).card:ℝ)
  nlinarith

end ErdosStoppedTagSieve


end Erdos970

end OAI
