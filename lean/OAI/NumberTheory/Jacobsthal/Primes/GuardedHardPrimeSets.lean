import OAI.NumberTheory.Jacobsthal.Estimates.FullEndpointData
import OAI.NumberTheory.Jacobsthal.Estimates.FullPatternSurvivors
import OAI.NumberTheory.Jacobsthal.Estimates.SourceFullPatternDomination
import OAI.NumberTheory.Jacobsthal.Probability.FullPatternVariance
import OAI.NumberTheory.Jacobsthal.Probability.StableModelMoments

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosVarianceWeighted
open ErdosInverseCells
attribute [local instance] Classical.propDecidable

theorem subset_card_of_fraction (A P : Finset ℕ) (hAP : A ⊆ P) (rho : ℝ)
    (hfrac : (A.card : ℝ)/(P.card : ℝ) ≤ rho) : (A.card : ℝ) ≤ rho*(P.card : ℝ) := by
  by_cases hP : P.card = 0
  · have hP0 := Finset.card_eq_zero.mp hP
    have hA0 : A = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun a ha => by simpa [hP0] using hAP ha)
    simp only [hA0,Finset.card_empty,Nat.cast_zero,hP,mul_zero,le_refl]
  · have hPC : (0 : ℝ) < P.card := by exact_mod_cast Nat.pos_of_ne_zero hP
    exact (div_le_iff₀ hPC).mp hfrac

theorem harmonic_transfer (A P : Finset ℕ) (hAP : A ⊆ P) (R theta rho : ℝ)
    (hR : 0 < R) (htheta : 0 ≤ theta) (hrho : 0 ≤ rho)
    (hbin : ∀ p ∈ P,R < (p : ℝ) ∧ (p : ℝ) ≤ (1+theta)*R)
    (hcard : (A.card : ℝ) ≤ rho*(P.card : ℝ)) :
    harmonicMass A ≤ rho*(1+theta)*harmonicMass P := by
  have htop : 0 < (1+theta)*R := by positivity
  have hupper : harmonicMass A ≤ (A.card : ℝ)/R := by
    calc
      _ ≤ ∑ _p ∈ A,R⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        have h := (hbin p (hAP hp)).1
        exact (inv_le_inv₀ (hR.trans h) hR).mpr h.le
      _ = _ := by rw [Finset.sum_const,nsmul_eq_mul];ring
  have hlower : (P.card : ℝ)/((1+theta)*R) ≤ harmonicMass P := by
    calc
      _ = ∑ _p ∈ P,((1+theta)*R)⁻¹ := by rw [Finset.sum_const,nsmul_eq_mul];ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        have h := hbin p hp
        exact (inv_le_inv₀ htop (hR.trans h.1)).mpr h.2
  calc
    _ ≤ (A.card : ℝ)/R := hupper
    _ ≤ (rho*(P.card : ℝ))/R := div_le_div_of_nonneg_right hcard hR.le
    _ = rho*(1+theta)*((P.card : ℝ)/((1+theta)*R)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hlower (by positivity)

theorem harmonic_transfer_two (A P : Finset ℕ) (hAP : A ⊆ P) (R theta rho : ℝ)
    (hR : 0 < R) (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1) (hrho : 0 ≤ rho)
    (hbin : ∀ p ∈ P,R < (p : ℝ) ∧ (p : ℝ) ≤ (1+theta)*R)
    (hcard : (A.card : ℝ) ≤ rho*(P.card : ℝ)) :
    harmonicMass A ≤ 2*rho*harmonicMass P := by
  have hh := harmonic_transfer A P hAP R theta rho hR htheta hrho hbin hcard
  have hc := harmonicMass_nonneg P
  have hmul := mul_le_mul_of_nonneg_left (show 1+theta ≤ 2 by linarith) (mul_nonneg hrho hc)
  nlinarith

end ErdosVarianceWeighted


section

open _root_.Filter
namespace ErdosVarianceUniformMoments
open NumberTheoryLean ErdosVarianceMoments ErdosVarianceSmallModel ErdosRandomVariance
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def modelBadEvent (J : ℕ) (w : ℝ) (H qA : ℕ) (C0 : ℤ)
    (beta delta : ∀ t : ℕ,ZMod t) (eta : ℝ) (v : ModelPoint w H) : Prop :=
  eta*((J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊) ≤
    |indicatorSum (Finset.range J) (modelIndicator w H C0 qA beta delta) v-
      (J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊|

theorem uniform_model_chebyshev (a eta tau : ℝ) (ha : 0 < a) (heta : 0 < eta) (htau : 0 < tau) :
    ∃ Cs : ℝ,0 < Cs ∧ ∀ xi : ℝ,0 < xi → ∀ᶠ w : ℝ in atTop,2 ≤ w ∧
      ∀ (R : ℝ),0 < R → ∀ (H qA : ℕ),0 < H → ∀ (C0 : ℤ),Int.gcd C0 (H : ℤ) = 1 →
        ∀ (beta delta : ∀ t : ℕ,ZMod t),
        (∀ t ∈ coprimePrimes w H,qA.Coprime t) →
        xi*w^Cs ≤ modelLength R xi (H : ℝ) (C0 : ℝ) →
        ∀ J : ℕ,w^a ≤ (J : ℝ) →
          modelMass R xi w H C0 (modelBadEvent J w H qA C0 beta delta eta) ≤ tau := by
  let zeta := min 1 (tau*eta^2/8)
  have hzeta : 0 < zeta := lt_min zero_lt_one (by positivity)
  have hzeta1 : zeta ≤ 1 := min_le_left _ _
  let eps := tau*eta^2/2
  have heps : 0 < eps := by dsimp [eps];positivity
  obtain ⟨Cs,hCs,huniform⟩ := uniform_joint_model_relative zeta hzeta
  refine ⟨Cs,hCs,?_⟩
  intro xi hxi
  filter_upwards [huniform xi hxi,stable_source_chebyshev a eps ha heps] with w hw hstable
  refine ⟨hw.1,?_⟩
  intro R hR H qA hH C0 hC0 beta delta hqA hscale J hJ
  have hmom := model_moment_bounds R xi w H qA C0 beta delta zeta
    (hw.2 R hR H qA hH C0 hC0 beta delta hqA hscale)
  have hh := hstable.2 J hJ (ModelPoint w H) (modelUniverse R xi w H C0)
    (fun _ => atomWeight R xi w H C0) (modelIndicator w H C0 qA beta delta) zeta eta
    (fun _ _ => (atomWeight_pos R xi w H C0 hR hxi.le hH).le) hzeta.le hzeta1 heta
    (fun j _ v _ => modelIndicator_binary w H C0 qA beta delta j v)
    hmom.1 (fun j _ => hmom.2.1 j) (fun j _ => hmom.2.2.1 j)
    (fun i _ j _ _ => hmom.2.2.2 i j)
  have hV : sieveProduct (variancePrimes w) = SmallSieveFinite.smallEuler ⌊w⌋₊ := by
    rw [variancePrimes_eq_cutoff,actual_sieveProduct]
  rw [hV] at hh
  have hbudget : (eps+4*zeta)/eta^2 ≤ tau := by
    apply (div_le_iff₀ (sq_pos_of_pos heta)).mpr
    have hz : zeta ≤ tau*eta^2/8 := min_le_right _ _
    dsimp [eps]
    linarith
  exact hh.trans hbudget

end ErdosVarianceUniformMoments

end


namespace ErdosVarianceSmallPrime
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceEffective ErdosVarianceCommon
  ErdosVarianceMoments ErdosVarianceUniformMoments ErdosInverseCells ErdosRandomVariance
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem common_deviation_mem_primeEvent (P : Finset ℕ) (J : ℕ) (w : ℝ)
    (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hPLarge : ∀ p ∈ P,w < (p : ℝ))
    (hQLarge : ∀ t ∈ qf.primeFactors,w < (t : ℝ)) (p : ℕ) [NeZero p]
    (hpGood : p ∈ goodPrimes P (effectiveModulus a r qf)) (eta : ℝ)
    (hdev : eta*((J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊) ≤
      |((commonSurvivors J w a r qf p (Finset.mem_filter.mp hpGood).2).card : ℝ)-
        (J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊|) :
    p ∈ actualPrimeEvent P w (effectiveModulus a r qf) (effectiveIntercept a r qf) hw hP hPLarge
      (modelBadEvent J w (effectiveModulus a r qf) (alignedCofactor (fun t => (a t : ℤ)) r qf)
        (effectiveIntercept a r qf) (actualDivisorTarget a qf) (actualCoprimeTarget a r) eta) := by
  apply Finset.mem_image.mpr
  refine ⟨⟨p,hpGood⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
  change eta*((J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊) ≤
    |(∑ j ∈ Finset.range J,actualModelIndicator w a r qf j
      (primePoint P w (effectiveModulus a r qf) (effectiveIntercept a r qf) hw hP hPLarge ⟨p,hpGood⟩))-
        (J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊|
  rw [← common_card_eq_model_sum P J w a r qf hq hw hP hPLarge hQLarge p hpGood]
  exact hdev

end ErdosVarianceSmallPrime



namespace ErdosVarianceSmallPrime
open NumberTheoryLean ErdosInverseCounts ErdosInverseAlignment ErdosVarianceCommon
attribute [local instance] Classical.propDecidable

noncomputable def badAligningPrimes (P : Finset ℕ) (Y : ℕ) (w : ℝ) (a : ℕ → ℕ)
    (r : ℚ) (qf : ℕ) (eps : ℝ) : Finset ℕ :=
  P.filter (fun p => aligns (fun t => (a t : ℤ)) r p ∧
    eps < |(modulusCount Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a (p*qf) : ℝ)/
      referenceCount Y w p qf-1|)

theorem mem_badAligningPrimes (P : Finset ℕ) (Y : ℕ) (w : ℝ) (a : ℕ → ℕ)
    (r : ℚ) (qf : ℕ) (eps : ℝ) (p : ℕ) :
    p ∈ badAligningPrimes P Y w a r qf eps ↔ p ∈ P ∧
      aligns (fun t => (a t : ℤ)) r p ∧
      eps < |(modulusCount Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a (p*qf) : ℝ)/
        referenceCount Y w p qf-1| := Finset.mem_filter

end ErdosVarianceSmallPrime



namespace ErdosVarianceLargePrime
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceEffective ErdosVarianceCommon
  ErdosVarianceMoments ErdosVarianceLargeMap
attribute [local instance] Classical.propDecidable

noncomputable def fullPatternBadEvent (J : ℕ) (w : ℝ) (H qA : ℕ)
    (beta delta : ∀ t : ℕ,ZMod t) (eta : ℝ) (v : ErdosLargePatternLaw.FullPattern w H) : Prop :=
  eta*((J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊) ≤
    |(ErdosLargePatternLaw.survivorCount w H qA J beta delta v : ℝ)-
      (J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊|

theorem common_deviation_mem_full_event (P : Finset ℕ) (J : ℕ) (w : ℝ)
    (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hPLarge : ∀ p ∈ P,w < (p : ℝ))
    (hQLarge : ∀ t ∈ qf.primeFactors,w < (t : ℝ)) (p : ℕ) [NeZero p]
    (hpGood : p ∈ goodPrimes P (effectiveModulus a r qf)) (eta : ℝ)
    (hdev : eta*((J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊) ≤
      |((commonSurvivors J w a r qf p (Finset.mem_filter.mp hpGood).2).card : ℝ)-
        (J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊|) :
    p ∈ fullPrimeEvent P w (effectiveModulus a r qf) (effectiveIntercept a r qf) hw hP hPLarge
      (fullPatternBadEvent J w (effectiveModulus a r qf) (alignedCofactor (fun t => (a t : ℤ)) r qf)
        (actualDivisorTarget a qf) (actualCoprimeTarget a r) eta) := by
  apply Finset.mem_image.mpr
  refine ⟨⟨p,hpGood⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
  change eta*((J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊) ≤
    |(ErdosLargePatternLaw.survivorCount w (effectiveModulus a r qf)
      (alignedCofactor (fun t => (a t : ℤ)) r qf) J (actualDivisorTarget a qf) (actualCoprimeTarget a r)
      (actualFullPattern P w (effectiveModulus a r qf) (effectiveIntercept a r qf) hw hP hPLarge ⟨p,hpGood⟩) : ℝ)-
        (J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊|
  rw [full_count_eq_common P J w a r qf hq hw hP hPLarge hQLarge p hpGood]
  exact hdev

end ErdosVarianceLargePrime


section

open _root_.Filter
namespace ErdosVarianceSmallPrime
open NumberTheoryLean ErdosInverseBoxHeight ErdosInversePrimeBin ErdosInverseEuler
  ErdosVarianceSmallModel ErdosVarianceEffective ErdosVarianceCommon ErdosVarianceMoments
  ErdosVarianceUniformMoments ErdosInverseAlignment
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem source_small_H_bad_prime_fraction (alpha aStar eps sigma : ℝ)
    (halpha : 0 < alpha) (ha : 0 < aStar) (heps : 0 < eps) (hsigma : 0 < sigma) :
    ∃ Cs : ℝ,0 < Cs ∧ ∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧
      ∀ xi : ℝ,0 < xi → xi ≤ xi0 → ∀ᶠ z : ℝ in atTop,
      ∀ (R theta : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf : ℕ),Squarefree qf →
        z^alpha ≤ R → xi/4 ≤ theta → theta ≤ xi →
        (∀ t ∈ qf.primeFactors,sourceW z < (t : ℝ)) →
        (∀ p ∈ primeBin R theta,qf.Coprime p ∧
          3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*qf))/Real.log (sourceW z)) →
        (effectiveModulus a r qf : ℝ) ≤ R^((4 : ℝ)/5) →
        effectiveSize a r qf R/(effectiveModulus a r qf : ℝ) ≤ (sourceZ z)^12 →
        (sourceW z)^Cs ≤ effectiveSize a r qf R →
        ((badAligningPrimes (primeBin R theta) (sourceY z) (sourceW z) a r qf eps).card : ℝ)/
          ((primeBin R theta).card : ℝ) ≤ sigma := by
  obtain ⟨C,hC,hdom⟩ := source_effective_point_domination alpha halpha
  obtain ⟨Cs,hCs,hmodel⟩ := uniform_model_chebyshev (5*aStar/8) (eps/2) (sigma/C)
    (by positivity) (by positivity) (div_pos hsigma hC)
  obtain ⟨xi0,hxi0,hxi01,hcommon⟩ := source_actual_bad_to_common aStar eps ha heps
  refine ⟨Cs,hCs,xi0,hxi0,hxi01,?_⟩
  intro xi hxi hxib
  have hxi1 := hxib.trans hxi01
  filter_upwards [hdom xi hxi hxi1,hcommon xi hxi hxib,
    sourceW_tendsto_atTop.eventually (hmodel xi hxi),eventually_gt_atTop (0 : ℝ)]
    with z hzdom hzcommon hzmodel hz0
  intro R theta a r qf hq hRlo hthetal hthetau hQLarge hgeometry hHsmall hratio hhard
  have hR : 0 < R := (Real.rpow_pos_of_pos hz0 alpha).trans_le hRlo
  have htheta : 0 ≤ theta := (by positivity : (0 : ℝ) ≤ xi/4).trans hthetal
  let P := primeBin R theta
  let H := effectiveModulus a r qf
  let C0 := effectiveIntercept a r qf
  let qA := alignedCofactor (fun t => (a t : ℤ)) r qf
  let beta := actualDivisorTarget a qf
  let delta := actualCoprimeTarget a r
  let J := commonLength (sourceY z) qf R xi
  let E := modelBadEvent J (sourceW z) H qA C0 beta delta (eps/2)
  obtain ⟨hw,hP,hPLarge,hdomE⟩ := hzdom R theta a r qf hq hRlo hthetal hthetau hHsmall hratio
  have hHp : 0 < H := effectiveModulus_pos a r qf
  have hC0 : Int.gcd C0 (H : ℤ) = 1 := effective_coordinates_gcd a r qf hq
  have hqA : ∀ t ∈ coprimePrimes (sourceW z) H,qA.Coprime t := by
    intro t ht
    have hc := LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1
    have htw := (Nat.le_floor_iff hw).mp hc.2
    exact aligned_coefficient_coprime_small a r qf hq (sourceW z) hQLarge t hc.1 htw
  have hY : xi*(sourceW z)^Cs ≤ modelLength R xi (H : ℝ) (C0 : ℝ) := by
    exact (mul_le_mul_of_nonneg_left hhard hxi.le).trans
      (modelLength_bounds R xi (H : ℝ) (C0 : ℝ) hR hxi.le hxi1 (by exact_mod_cast hHp)).2
  have hmap (p : ℕ) (hp : p ∈ badAligningPrimes P (sourceY z) (sourceW z) a r qf eps) :
      (sourceW z)^(5*aStar/8) ≤ (J : ℝ) ∧
      p ∈ actualPrimeEvent P (sourceW z) H C0 hw hP hPLarge E := by
    obtain ⟨hpP,halign,hbad⟩ := (mem_badAligningPrimes P (sourceY z) (sourceW z) a r qf eps p).mp hp
    have hprime := hP p hpP
    let : NeZero p := ⟨hprime.ne_zero⟩
    have hqp := (hgeometry p hpP).1
    have hgood : p ∈ goodPrimes P H := Finset.mem_filter.mpr
      ⟨hpP,aligned_isolated_coprime_effective a r qf hq p hprime hqp halign⟩
    have hbin := (mem_primeBin hR.le htheta p).mp hpP
    have hpu : (p : ℝ) ≤ (1+xi)*R := hbin.2.2.trans (by nlinarith)
    have hh := hzcommon a r qf hq p hprime hqp (Finset.mem_filter.mp hgood).2 R hR
      hbin.2.1 hpu (hPLarge p hpP) hQLarge (hgeometry p hpP).2 halign hbad
    refine ⟨hh.1,?_⟩
    exact common_deviation_mem_primeEvent P J (sourceW z) a r qf hq hw hP hPLarge hQLarge p hgood
      (eps/2) hh.2.le
  by_cases hempty : badAligningPrimes P (sourceY z) (sourceW z) a r qf eps = ∅
  · change ((badAligningPrimes P (sourceY z) (sourceW z) a r qf eps).card : ℝ)/(P.card : ℝ) ≤ sigma
    rw [hempty,Finset.card_empty,Nat.cast_zero,zero_div]
    exact hsigma.le
  obtain ⟨p,hp⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hJ := (hmap p hp).1
  have hmass : modelMass R xi (sourceW z) H C0 E ≤ sigma/C :=
    hzmodel.2 R hR H qA hHp C0 hC0 beta delta hqA hY J hJ
  have hsub : badAligningPrimes P (sourceY z) (sourceW z) a r qf eps ⊆
      actualPrimeEvent P (sourceW z) H C0 hw hP hPLarge E := fun p hp => (hmap p hp).2
  have hcard : ((badAligningPrimes P (sourceY z) (sourceW z) a r qf eps).card : ℝ) ≤
      (actualPrimeEvent P (sourceW z) H C0 hw hP hPLarge E).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hh := (div_le_div_of_nonneg_right hcard (Nat.cast_nonneg P.card)).trans
    ((hdomE E).trans (mul_le_mul_of_nonneg_left hmass hC.le))
  have hc : C*(sigma/C) = sigma := by field_simp
  exact hh.trans_eq hc

end ErdosVarianceSmallPrime

end

section

open _root_.Filter
namespace ErdosVarianceLargePrime
open NumberTheoryLean ErdosInverseBoxHeight ErdosInversePrimeBin ErdosInverseEuler
  ErdosVarianceSmallModel ErdosVarianceEffective ErdosVarianceCommon ErdosVarianceMoments
  ErdosVarianceLargeMap ErdosVarianceSmallPrime ErdosInverseAlignment
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem source_large_H_bad_prime_fraction (alpha aStar eps sigma : ℝ)
    (halpha : 0 < alpha) (ha : 0 < aStar) (heps : 0 < eps) (hsigma : 0 < sigma) :
    ∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧ ∀ xi : ℝ,0 < xi → xi ≤ xi0 → ∀ᶠ z : ℝ in atTop,
      ∀ (R theta : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf : ℕ),Squarefree qf →
        z^alpha ≤ R → xi/4 ≤ theta → theta ≤ xi →
        (∀ t ∈ qf.primeFactors,sourceW z < (t : ℝ)) →
        (∀ p ∈ primeBin R theta,qf.Coprime p ∧
          3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*qf))/Real.log (sourceW z)) →
        R^((4 : ℝ)/5) ≤ (effectiveModulus a r qf : ℝ) →
        (effectiveModulus a r qf : ℝ) ≤ R*(sourceZ z)^11 →
        effectiveSize a r qf R/(effectiveModulus a r qf : ℝ) ≤ (sourceZ z)^12 →
        ((badAligningPrimes (primeBin R theta) (sourceY z) (sourceW z) a r qf eps).card : ℝ)/
          ((primeBin R theta).card : ℝ) ≤ sigma := by
  obtain ⟨C,hC,hdom⟩ := source_full_pattern_domination alpha halpha
  have hmodel := ErdosLargePatternLaw.uniform_pattern_chebyshev (5*aStar/8) (eps/2) (sigma/(2*C))
    (by positivity) (by positivity) (by positivity)
  obtain ⟨xi0,hxi0,hxi01,hcommon⟩ := source_actual_bad_to_common aStar eps ha heps
  refine ⟨xi0,hxi0,hxi01,?_⟩
  intro xi hxi hxib
  have hxi1 := hxib.trans hxi01
  filter_upwards [hdom xi hxi hxi1 (sigma/2) (by positivity),hcommon xi hxi hxib,
    sourceW_tendsto_atTop.eventually hmodel] with z hzdom hzcommon hzmodel
  intro R theta a r qf hq hRlo hthetal hthetau hQLarge hgeometry hHlarge hHupper hratio
  have hR1 : 1 < R := (Real.one_lt_rpow hzdom.1 halpha).trans_le hRlo
  have hR : 0 < R := by linarith
  have htheta : 0 ≤ theta := (by positivity : (0 : ℝ) ≤ xi/4).trans hthetal
  let P := primeBin R theta
  let H := effectiveModulus a r qf
  let C0 := effectiveIntercept a r qf
  let qA := alignedCofactor (fun t => (a t : ℤ)) r qf
  let beta := actualDivisorTarget a qf
  let delta := actualCoprimeTarget a r
  let J := commonLength (sourceY z) qf R xi
  let E := fullPatternBadEvent J (sourceW z) H qA beta delta (eps/2)
  have hH1 : (1 : ℝ) < H := (Real.one_lt_rpow hR1 (by norm_num : (0 : ℝ) < 4/5)).trans_le hHlarge
  have hH2 : 2 ≤ H := by
    have hh : 1 < H := by exact_mod_cast hH1
    omega
  have hC0 : Int.gcd C0 (H : ℤ) = 1 := effective_coordinates_gcd a r qf hq
  obtain ⟨hw,hP,hPLarge,hdomE⟩ := hzdom.2 R theta hRlo hthetal hthetau H C0 hH2 hC0 hHlarge hHupper hratio
  have hqA : ∀ t ∈ coprimePrimes (sourceW z) H,qA.Coprime t := by
    intro t ht
    have hc := LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1
    exact aligned_coefficient_coprime_small a r qf hq (sourceW z) hQLarge t hc.1 ((Nat.le_floor_iff hw).mp hc.2)
  have hmap (p : ℕ) (hp : p ∈ badAligningPrimes P (sourceY z) (sourceW z) a r qf eps) :
      (sourceW z)^(5*aStar/8) ≤ (J : ℝ) ∧ p ∈ fullPrimeEvent P (sourceW z) H C0 hw hP hPLarge E := by
    obtain ⟨hpP,halign,hbad⟩ := (mem_badAligningPrimes P (sourceY z) (sourceW z) a r qf eps p).mp hp
    have hprime := hP p hpP
    let : NeZero p := ⟨hprime.ne_zero⟩
    have hqp := (hgeometry p hpP).1
    have hgood : p ∈ goodPrimes P H := Finset.mem_filter.mpr
      ⟨hpP,aligned_isolated_coprime_effective a r qf hq p hprime hqp halign⟩
    have hbin := (mem_primeBin hR.le htheta p).mp hpP
    have hpu : (p : ℝ) ≤ (1+xi)*R := hbin.2.2.trans (by nlinarith)
    have hh := hzcommon a r qf hq p hprime hqp (Finset.mem_filter.mp hgood).2 R hR
      hbin.2.1 hpu (hPLarge p hpP) hQLarge (hgeometry p hpP).2 halign hbad
    exact ⟨hh.1,common_deviation_mem_full_event P J (sourceW z) a r qf hq hw hP hPLarge hQLarge p hgood
      (eps/2) hh.2.le⟩
  by_cases hempty : badAligningPrimes P (sourceY z) (sourceW z) a r qf eps = ∅
  · change ((badAligningPrimes P (sourceY z) (sourceW z) a r qf eps).card : ℝ)/(P.card : ℝ) ≤ sigma
    rw [hempty,Finset.card_empty,Nat.cast_zero,zero_div]
    exact hsigma.le
  obtain ⟨p,hp⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hJ := (hmap p hp).1
  have hmass : patternEventWeight (sourceW z) H E ≤ sigma/(2*C) :=
    hzmodel.2 H qA beta delta hqA J hJ
  have hsub : badAligningPrimes P (sourceY z) (sourceW z) a r qf eps ⊆
      fullPrimeEvent P (sourceW z) H C0 hw hP hPLarge E := fun p hp => (hmap p hp).2
  have hcard : ((badAligningPrimes P (sourceY z) (sourceW z) a r qf eps).card : ℝ) ≤
      (fullPrimeEvent P (sourceW z) H C0 hw hP hPLarge E).card := by exact_mod_cast Finset.card_le_card hsub
  have hh := (div_le_div_of_nonneg_right hcard (Nat.cast_nonneg P.card)).trans
    ((hdomE E).trans (add_le_add (mul_le_mul_of_nonneg_left hmass hC.le) le_rfl))
  have hc : C*(sigma/(2*C))+sigma/2 = sigma := by field_simp;ring
  exact hh.trans_eq hc

end ErdosVarianceLargePrime

end

section

open _root_.Filter
namespace ErdosVarianceLargePrime
open NumberTheoryLean ErdosInverseBoxHeight ErdosInversePrimeBin ErdosInverseEuler
  ErdosVarianceEffective ErdosVarianceSmallPrime
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem source_hard_bad_prime_fraction (alpha aStar eps sigma Cmin : ℝ)
    (halpha : 0 < alpha) (ha : 0 < aStar) (heps : 0 < eps) (hsigma : 0 < sigma) :
    ∃ Cs : ℝ,0 < Cs ∧ Cmin ≤ Cs ∧ ∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧
      ∀ xi : ℝ,0 < xi → xi ≤ xi0 → ∀ᶠ z : ℝ in atTop,
      ∀ (R theta : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf : ℕ),Squarefree qf →
        z^alpha ≤ R → xi/4 ≤ theta → theta ≤ xi →
        (∀ t ∈ qf.primeFactors,sourceW z < (t : ℝ)) →
        (∀ p ∈ primeBin R theta,qf.Coprime p ∧
          3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*qf))/Real.log (sourceW z)) →
        (effectiveModulus a r qf : ℝ) ≤ R*(sourceZ z)^11 →
        effectiveSize a r qf R/(effectiveModulus a r qf : ℝ) ≤ (sourceZ z)^12 →
        (sourceW z)^Cs ≤ effectiveSize a r qf R →
        ((badAligningPrimes (primeBin R theta) (sourceY z) (sourceW z) a r qf eps).card : ℝ)/
          ((primeBin R theta).card : ℝ) ≤ sigma := by
  obtain ⟨Cs0,hCs0,xiS,hxiS,hxiS1,hsmall⟩ := source_small_H_bad_prime_fraction alpha aStar eps sigma halpha ha heps hsigma
  obtain ⟨xiL,hxiL,hxiL1,hlarge⟩ := source_large_H_bad_prime_fraction alpha aStar eps sigma halpha ha heps hsigma
  let Cs := max Cs0 (max 1 Cmin)
  have hCs : 0 < Cs := hCs0.trans_le (le_max_left _ _)
  have hCmin : Cmin ≤ Cs := (le_max_right 1 Cmin).trans (le_max_right _ _)
  refine ⟨Cs,hCs,hCmin,min xiS xiL,lt_min hxiS hxiL,(min_le_left _ _).trans hxiS1,?_⟩
  intro xi hxi hxib
  have hxS := hxib.trans (min_le_left xiS xiL)
  have hxL := hxib.trans (min_le_right xiS xiL)
  filter_upwards [hsmall xi hxi hxS,hlarge xi hxi hxL,sourceW_tendsto_atTop.eventually_ge_atTop 1]
    with z hzsmall hzlarge hW
  intro R theta a r qf hq hRlo hthetal hthetau hQLarge hgeometry hHupper hratio hhard
  by_cases hcase : (effectiveModulus a r qf : ℝ) ≤ R^((4 : ℝ)/5)
  · have hhard0 : (sourceW z)^Cs0 ≤ effectiveSize a r qf R :=
      (Real.rpow_le_rpow_of_exponent_le hW (le_max_left Cs0 (max 1 Cmin))).trans hhard
    exact hzsmall R theta a r qf hq hRlo hthetal hthetau hQLarge hgeometry hcase hratio hhard0
  · exact hzlarge R theta a r qf hq hRlo hthetal hthetau hQLarge hgeometry
      (le_of_lt (lt_of_not_ge hcase)) hHupper hratio

end ErdosVarianceLargePrime

end


namespace ErdosVarianceWeighted
open NumberTheoryLean ErdosInverseBoxHeight ErdosInversePrimeBin ErdosVarianceEffective ErdosVarianceSmallPrime
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

def hardCandidate (z R : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (Cs : ℝ) : Prop :=
  (effectiveModulus a r qf : ℝ) ≤ R*(sourceZ z)^11 ∧
  effectiveSize a r qf R/(effectiveModulus a r qf : ℝ) ≤ (sourceZ z)^12 ∧
  (sourceW z)^Cs ≤ effectiveSize a r qf R

noncomputable def guardedHardPrimes (z R theta : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (Cs eps : ℝ) : Finset ℕ :=
  if hardCandidate z R a r qf Cs then
    badAligningPrimes (primeBin R theta) (sourceY z) (sourceW z) a r qf eps else ∅

noncomputable def rawHardPrimeUnion (Q : Finset ℚ) (z R theta : ℝ) (a : ℕ → ℕ) (qf : ℕ) (Cs eps : ℝ) : Finset ℕ :=
  Q.biUnion (fun r => guardedHardPrimes z R theta a r qf Cs eps)

theorem guardedHardPrimes_subset (z R theta : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (Cs eps : ℝ) :
    guardedHardPrimes z R theta a r qf Cs eps ⊆ primeBin R theta := by
  unfold guardedHardPrimes
  split_ifs
  · exact Finset.filter_subset _ _
  · exact Finset.empty_subset _

theorem rawHardPrimeUnion_subset (Q : Finset ℚ) (z R theta : ℝ) (a : ℕ → ℕ) (qf : ℕ) (Cs eps : ℝ) :
    rawHardPrimeUnion Q z R theta a qf Cs eps ⊆ primeBin R theta := by
  exact Finset.biUnion_subset.mpr (fun r _ => guardedHardPrimes_subset z R theta a r qf Cs eps)

theorem mem_rawHardPrimeUnion (Q : Finset ℚ) (z R theta : ℝ) (a : ℕ → ℕ) (qf : ℕ) (Cs eps : ℝ) (p : ℕ) :
    p ∈ rawHardPrimeUnion Q z R theta a qf Cs eps ↔ ∃ r ∈ Q,
      hardCandidate z R a r qf Cs ∧
      p ∈ badAligningPrimes (primeBin R theta) (sourceY z) (sourceW z) a r qf eps := by
  simp only [rawHardPrimeUnion,Finset.mem_biUnion]
  apply exists_congr
  intro r
  apply and_congr_right
  intro _hr
  by_cases h : hardCandidate z R a r qf Cs <;> simp [guardedHardPrimes,h]

theorem rawHardPrimeUnion_card (Q : Finset ℚ) (z R theta : ℝ) (a : ℕ → ℕ) (qf : ℕ) (Cs eps sigma : ℝ)
    (h : ∀ r ∈ Q,((guardedHardPrimes z R theta a r qf Cs eps).card : ℝ) ≤
      sigma*((primeBin R theta).card : ℝ)) :
    ((rawHardPrimeUnion Q z R theta a qf Cs eps).card : ℝ) ≤
      sigma*(Q.card : ℝ)*((primeBin R theta).card : ℝ) := by
  have hc := Finset.card_biUnion_le (s := Q) (t := fun r => guardedHardPrimes z R theta a r qf Cs eps)
  calc
    _ ≤ ∑ r ∈ Q,((guardedHardPrimes z R theta a r qf Cs eps).card : ℝ) := by exact_mod_cast hc
    _ ≤ ∑ _r ∈ Q,sigma*((primeBin R theta).card : ℝ) := Finset.sum_le_sum h
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul];ring

end ErdosVarianceWeighted


end Erdos970

end OAI
