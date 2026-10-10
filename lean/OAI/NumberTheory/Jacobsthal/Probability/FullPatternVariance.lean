import OAI.NumberTheory.Jacobsthal.Estimates.ConditionalPatternCounts
import OAI.NumberTheory.Jacobsthal.Primes.StableSourceChebyshev

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosLargePatternLaw
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceMoments

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem four_coordinate_count {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (P : A → B → Prop) (Q : C → D → Prop) (n m : ℕ)
    (hP : ∀ a,(Finset.univ.filter (P a)).card=n)
    (hQ : ∀ c,(Finset.univ.filter (Q c)).card=m) :
    (Finset.univ.filter (fun v : A × B × C × D => P v.1 v.2.1 ∧ Q v.2.2.1 v.2.2.2)).card =
      Fintype.card A*n*Fintype.card C*m := by
  have hi (a : A) (b : B) (c : C) (d : D) :
      (if P a b ∧ Q c d then 1 else 0 : ℕ)=(if P a b then 1 else 0)*(if Q c d then 1 else 0) := by
    by_cases hp : P a b <;> by_cases hq : Q c d <;> simp [hp,hq]
  have hp (a : A) : (∑ b : B,if P a b then 1 else 0)=n := by
    simpa only [Finset.card_filter] using hP a
  have hq (c : C) : (∑ d : D,if Q c d then 1 else 0)=m := by
    simpa only [Finset.card_filter] using hQ c
  have hd (a : A) (b : B) (c : C) :
      (∑ d : D,(if P a b then 1 else 0)*(if Q c d then 1 else 0)) =
      (if P a b then 1 else 0)*m := by
    calc
      _ = (if P a b then 1 else 0)*(∑ d : D,if Q c d then 1 else 0) :=
        (Finset.mul_sum _ _ _).symm
      _ = _ := by rw [hq]
  simp only [Finset.card_filter,Fintype.sum_prod_type,hi]
  simp_rw [hd]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
  have hb (a : A) : (∑ b : B,Fintype.card C*((if P a b then 1 else 0)*m)) =
      Fintype.card C*(n*m) := by
    calc
      _ = Fintype.card C*(∑ b : B,(if P a b then 1 else 0)*m) := (Finset.mul_sum _ _ _).symm
      _ = Fintype.card C*((∑ b : B,if P a b then 1 else 0)*m) :=
        congrArg (fun x => Fintype.card C*x) (Finset.sum_mul _ _ _).symm
      _ = _ := by rw [hp]
  simp_rw [hb]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
  ring

theorem joint_condition_card (w : ℝ) (H qA : ℕ) (beta delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t) :
    (Finset.univ.filter (jointCondition w H qA beta delta S)).card =
      (divisorModulus w H).totient*(∏ t ∈ divisorPrimes w H,(t-(positionResidues S t).card))*
      (coprimeModulus w H).totient*(∏ t ∈ coprimePrimes w H,(t-(positionResidues S t).card)) := by
  have he : Finset.univ.filter (jointCondition w H qA beta delta S) =
      Finset.univ.filter (fun v : FullPattern w H =>
        divisorCondition w H beta S v.1 v.2.1 ∧ coprimeCondition w H qA delta S v.2.2.1 v.2.2.2) := by
    apply Finset.filter_congr
    rintro ⟨p0,k0,p1,m1⟩ _
    exact joint_condition_split w H qA beta delta S p0 k0 p1 m1
  rw [he,four_coordinate_count _ _ _ _
    (divisor_condition_card w H beta S) (fun p1 => coprime_condition_card w H qA delta S p1 hqA)]
  simp only [ZMod.card_units_eq_totient]

theorem joint_density_split (w : ℝ) (H : ℕ) (S : Finset ℕ) :
    jointDensity (divisorPrimes w H) S*jointDensity (coprimePrimes w H) S =
      jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) S := by
  unfold jointDensity divisorPrimes coprimePrimes
  exact Finset.prod_filter_mul_prod_filter_not _ _ _

theorem joint_expectation (w : ℝ) (H qA : ℕ) (beta delta : ∀ t : ℕ,ZMod t) (S : Finset ℕ)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t) :
    expectation w H (fun v => if jointCondition w H qA beta delta S v then 1 else 0) =
      jointDensity (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) S := by
  have h0 : ∀ t ∈ divisorPrimes w H,t.Prime := fun t ht =>
    (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1
  have h1 : ∀ t ∈ coprimePrimes w H,t.Prime := fun t ht =>
    (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1
  have hc : (∑ v : FullPattern w H,if jointCondition w H qA beta delta S v then (1 : ℝ) else 0) =
      ((Finset.univ.filter (jointCondition w H qA beta delta S)).card : ℝ) := by
    simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  have hT0 : (divisorModulus w H : ℝ) ≠ 0 := by exact_mod_cast (divisorModulus_pos w H).ne'
  have hT1 : (coprimeModulus w H : ℝ) ≠ 0 := by exact_mod_cast (coprimeModulus_pos w H).ne'
  have hP0 : ((divisorModulus w H).totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (divisorModulus_pos w H)).ne'
  have hP1 : ((coprimeModulus w H).totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (coprimeModulus_pos w H)).ne'
  rw [expectation,← Finset.mul_sum,hc,joint_condition_card w H qA beta delta S hqA]
  simp only [Nat.cast_mul]
  rw [product_allowed_eq_density _ S h0,product_allowed_eq_density _ S h1]
  change weight w H*(((divisorModulus w H).totient : ℝ)*
    ((divisorModulus w H : ℝ)*jointDensity (divisorPrimes w H) S)*
    ((coprimeModulus w H).totient : ℝ)*
    ((coprimeModulus w H : ℝ)*jointDensity (coprimePrimes w H) S)) = _
  rw [← joint_density_split w H S]
  unfold weight
  field_simp

end ErdosLargePatternLaw



open _root_.Filter
namespace ErdosLargePatternLaw
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceMoments ErdosRandomVariance

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem single_expectation (w : ℝ) (H qA : ℕ) (beta delta : ∀ t : ℕ,ZMod t) (j : ℕ)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t) :
    expectation w H (indicator w H qA beta delta j) =
      sieveProduct (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) := by
  have h := joint_expectation w H qA beta delta {j} hqA
  have he : (fun v => if jointCondition w H qA beta delta {j} v then (1 : ℝ) else 0) =
      indicator w H qA beta delta j := by
    funext v
    simp only [jointCondition,Finset.mem_singleton,forall_eq,indicator]
  rw [he,jointDensity_singleton] at h
  exact h

theorem pair_expectation (w : ℝ) (H qA : ℕ) (beta delta : ∀ t : ℕ,ZMod t) (i j : ℕ)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t) :
    expectation w H (fun v => indicator w H qA beta delta i v*indicator w H qA beta delta j v) =
      pairKernel (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) i j := by
  have h := joint_expectation w H qA beta delta {i,j} hqA
  have he : (fun v => indicator w H qA beta delta i v*indicator w H qA beta delta j v) =
      (fun v => if jointCondition w H qA beta delta {i,j} v then 1 else 0) := by
    funext v
    simp only [jointCondition,Finset.forall_mem_insert,Finset.mem_singleton,forall_eq,indicator]
    by_cases hi : survives w H qA beta delta i v <;>
      by_cases hj : survives w H qA beta delta j v <;> simp [hi,hj]
  rw [he,h,jointDensity_pair]

theorem count_variance (w : ℝ) (H qA J : ℕ) (beta delta : ∀ t : ℕ,ZMod t)
    (hqA : ∀ t ∈ coprimePrimes w H,qA.Coprime t) :
    expectation w H (fun v => ((survivorCount w H qA J beta delta v : ℝ)-
      (J : ℝ)*sieveProduct (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊))^2) ≤
      (J : ℝ)*sieveProduct (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) := by
  have hs (j : ℕ) := single_expectation w H qA beta delta j hqA
  have hp (i j : ℕ) := pair_expectation w H qA beta delta i j hqA
  have hh := stable_prime_variance (Finset.univ : Finset (FullPattern w H)) (fun _ => weight w H)
    J (indicator w H qA beta delta) (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊)
    (fun p hp => (LargePrimeDeletion.mem_cutoffPrimes.mp hp).1) 0 (le_refl _)
    (fun j _ v _ => indicator_binary w H qA beta delta j v)
    (by simpa only [add_zero] using (weight_sum w H).le)
    (fun j _ => by simpa only [sub_zero,one_mul,expectation,weightedMoment] using (hs j).ge)
    (fun j _ => by simpa only [add_zero,one_mul,expectation,weightedMoment] using (hs j).le)
    (fun i _ j _ _ => by simpa only [add_zero,one_mul,expectation,weightedMoment] using (hp i j).le)
  simpa only [mul_zero,zero_mul,one_mul,add_zero,indicatorSum,← count_eq_indicator_sum,expectation,weightedMoment] using hh

theorem uniform_pattern_chebyshev (a eta tau : ℝ) (ha : 0 < a) (heta : 0 < eta) (htau : 0 < tau) :
    ∀ᶠ w : ℝ in atTop,1 < w ∧ ∀ (H qA : ℕ) (beta delta : ∀ t : ℕ,ZMod t),
      (∀ t ∈ coprimePrimes w H,qA.Coprime t) → ∀ J : ℕ,w^a ≤ (J : ℝ) →
        (∑ v : FullPattern w H with eta*((J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊) ≤
          |(survivorCount w H qA J beta delta v : ℝ)-(J : ℝ)*SmallSieveFinite.smallEuler ⌊w⌋₊|,
            weight w H) ≤ tau := by
  have heps : 0 < tau*eta^2 := mul_pos htau (sq_pos_of_pos heta)
  filter_upwards [stable_source_chebyshev a (tau*eta^2) ha heps] with w hw
  refine ⟨hw.1,?_⟩
  intro H qA beta delta hqA J hJ
  have hcut : variancePrimes w=LargePrimeDeletion.cutoffPrimes ⌊w⌋₊ := by
    ext p
    simp only [variancePrimes,LargePrimeDeletion.mem_cutoffPrimes,Finset.mem_filter,Finset.mem_Ioc]
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨h.1.pos,h.2⟩,h.1⟩⟩
  have hs (j : ℕ) := single_expectation w H qA beta delta j hqA
  have hp (i j : ℕ) := pair_expectation w H qA beta delta i j hqA
  have hh := hw.2 J hJ (FullPattern w H) Finset.univ (fun _ => weight w H)
    (indicator w H qA beta delta) 0 eta (fun _ _ => (weight_positive w H).le)
    (le_refl _) zero_le_one heta (fun j _ v _ => indicator_binary w H qA beta delta j v)
    (by simpa only [add_zero] using (weight_sum w H).le)
    (fun j _ => by simpa only [sub_zero,one_mul,hcut,expectation,weightedMoment] using (hs j).ge)
    (fun j _ => by simpa only [add_zero,one_mul,hcut,expectation,weightedMoment] using (hs j).le)
    (fun i _ j _ _ => by simpa only [add_zero,one_mul,hcut,expectation,weightedMoment] using (hp i j).le)
  have hV : sieveProduct (variancePrimes w)=SmallSieveFinite.smallEuler ⌊w⌋₊ := by
    rw [hcut]
    simp only [sieveProduct,SmallSieveFinite.smallEuler,one_div]
  have hb : (tau*eta^2+4*0)/eta^2=tau := by
    field_simp [heta.ne']
    ring
  simpa only [hV,hb,indicatorSum,← count_eq_indicator_sum] using hh

end ErdosLargePatternLaw


end Erdos970

end OAI
