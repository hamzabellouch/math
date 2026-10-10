import Mathlib
import OAI.NumberTheory.PrimePackets.LocalModels

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
namespace PrimeDegreePackets

 
def IdealSupportedAt {K : Type*} [Field K] [NumberField K] (S : Finset ℕ)
    (I : Ideal (𝓞 K)) : Prop := ∀ p, p.Prime → p ∣ Ideal.absNorm I → p ∈ S

def IdealCoprimeTo {K : Type*} [Field K] [NumberField K] (S : Finset ℕ)
    (I : Ideal (𝓞 K)) : Prop := ∀ p ∈ S, ¬ p ∣ Ideal.absNorm I

lemma idealSupportedAt_one {K : Type*} [Field K] [NumberField K] (S : Finset ℕ) :
    IdealSupportedAt (K := K) S 1 := by
  intro p hp hd
  simp only [map_one] at hd
  exact (hp.not_dvd_one hd).elim

lemma idealCoprimeTo_one {K : Type*} [Field K] [NumberField K]
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) : IdealCoprimeTo (K := K) S 1 := by
  intro p hp
  simpa only [map_one] using (hS p hp).not_dvd_one

lemma idealSupportedAt_mul {K : Type*} [Field K] [NumberField K]
    {S : Finset ℕ} {I J : Ideal (𝓞 K)} (hI : IdealSupportedAt S I)
    (hJ : IdealSupportedAt S J) : IdealSupportedAt S (I * J) := by
  intro p hp hd
  rw [map_mul] at hd
  rcases hp.dvd_mul.mp hd with hi | hj
  · exact hI p hp hi
  · exact hJ p hp hj

lemma idealCoprimeTo_mul {K : Type*} [Field K] [NumberField K]
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {I J : Ideal (𝓞 K)}
    (hI : IdealCoprimeTo S I) (hJ : IdealCoprimeTo S J) : IdealCoprimeTo S (I * J) := by
  intro p hp
  rw [map_mul]
  exact (hS p hp).not_dvd_mul (hI p hp) (hJ p hp)

lemma idealSupportedAt_of_norm_eq_prime_pow {K : Type*} [Field K] [NumberField K]
    {S : Finset ℕ} {I : Ideal (𝓞 K)} {p e : ℕ} (hp : p.Prime) (hmem : p ∈ S)
    (hI : Ideal.absNorm I = p ^ e) : IdealSupportedAt S I := by
  intro r hr hd
  rw [hI] at hd
  have hrp : r = p := (Nat.dvd_prime hp).mp (hr.dvd_of_dvd_pow hd) |>.resolve_left hr.ne_one
  exact hrp ▸ hmem

lemma idealCoprimeTo_of_norm_eq_prime_pow {K : Type*} [Field K] [NumberField K]
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {I : Ideal (𝓞 K)} {p e : ℕ}
    (hp : p.Prime) (hmem : p ∉ S) (hI : Ideal.absNorm I = p ^ e) : IdealCoprimeTo S I := by
  intro r hr hd
  rw [hI] at hd
  have hrp : r = p := (Nat.dvd_prime hp).mp ((hS r hr).dvd_of_dvd_pow hd)
    |>.resolve_left (hS r hr).ne_one
  exact hmem (hrp ▸ hr)

 

theorem exists_ideal_support_split {K : Type*} [Field K] [NumberField K]
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (A : Ideal (𝓞 K)) : A ≠ ⊥ →
    ∃ I J : Ideal (𝓞 K), I ≠ ⊥ ∧ J ≠ ⊥ ∧ IdealSupportedAt S I ∧
      IdealCoprimeTo S J ∧ A = I * J := by
  classical
  induction A using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => simp
  | h₂ A hA =>
    intro _
    have ha : A = 1 := by simpa only [Ideal.isUnit_iff, Ideal.one_eq_top] using hA
    refine ⟨1,1,one_ne_zero,one_ne_zero,idealSupportedAt_one S,idealCoprimeTo_one S hS,?_⟩
    simpa using ha
  | h₃ A P hA hP ih =>
    intro _
    obtain ⟨I,J,hI,hJ,hsI,hcJ,hIJ⟩ := ih hA
    let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
    obtain ⟨p,e,_he,_hpP,hp,hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
    by_cases hs : p ∈ S
    · refine ⟨P*I,J,mul_ne_zero hP.ne_zero hI,hJ,
        idealSupportedAt_mul (idealSupportedAt_of_norm_eq_prime_pow hp hs hnorm) hsI,hcJ,?_⟩
      rw [hIJ,mul_assoc]
    · refine ⟨I,P*J,hI,mul_ne_zero hP.ne_zero hJ,hsI,
        idealCoprimeTo_mul hS (idealCoprimeTo_of_norm_eq_prime_pow hS hp hs hnorm) hcJ,?_⟩
      rw [hIJ,mul_left_comm]

lemma ideal_support_norm_coprime {K : Type*} [Field K] [NumberField K]
    {S : Finset ℕ} {I J : Ideal (𝓞 K)} (hI : IdealSupportedAt S I)
    (hJ : IdealCoprimeTo S J) : (Ideal.absNorm I).Coprime (Ideal.absNorm J) :=
  Nat.coprime_of_dvd (fun p hp hi => hJ p (hI p hp hi))

lemma ideal_support_relprime {K : Type*} [Field K] [NumberField K]
    {S : Finset ℕ} {I J : Ideal (𝓞 K)} (hI : IdealSupportedAt S I)
    (hJ : IdealCoprimeTo S J) : IsRelPrime I J := by
  intro D hDI hDJ
  have hd : Ideal.absNorm D = 1 := Nat.eq_one_of_dvd_coprimes (ideal_support_norm_coprime hI hJ)
    (map_dvd Ideal.absNorm hDI) (map_dvd Ideal.absNorm hDJ)
  rw [Ideal.absNorm_eq_one_iff.mp hd]
  simpa only [Ideal.one_eq_top] using (isUnit_one : IsUnit (1 : Ideal (𝓞 K)))

lemma ideal_support_split_unique {K : Type*} [Field K] [NumberField K]
    {S : Finset ℕ} {I J I' J' : Ideal (𝓞 K)} (hI0 : I ≠ ⊥)
    (hI : IdealSupportedAt S I) (hJ : IdealCoprimeTo S J)
    (hI' : IdealSupportedAt S I') (hJ' : IdealCoprimeTo S J')
    (h : I * J = I' * J') : I = I' ∧ J = J' := by
  have hi : I ∣ I' := (ideal_support_relprime hI hJ').dvd_of_dvd_mul_right
    (h ▸ dvd_mul_right I J)
  have hi' : I' ∣ I := (ideal_support_relprime hI' hJ).dvd_of_dvd_mul_right
    (h.symm ▸ dvd_mul_right I' J')
  have he : I = I' := le_antisymm (Ideal.dvd_iff_le.mp hi') (Ideal.dvd_iff_le.mp hi)
  refine ⟨he,?_⟩
  rw [← he] at h
  exact mul_left_cancel₀ hI0 h

end PrimeDegreePackets


namespace PrimeDegreePackets
open NumberField
open scoped BigOperators Pointwise NumberField nonZeroDivisors ENNReal

 
def coprimeIntegralIdeals (K : Type*) [Field K] [NumberField K] (S : Finset ℕ) :=
  {J : {I : Ideal (𝓞 K) // I ≠ ⊥} // IdealCoprimeTo S J.1}

def idealSupportMul {K : Type*} [Field K] [NumberField K] (S : Finset ℕ)
    (A : primaryIntegralIdeals K S × coprimeIntegralIdeals K S) :
    {I : Ideal (𝓞 K) // I ≠ ⊥} :=
  ⟨A.1.1.1 * A.2.1.1, mul_ne_zero A.1.1.2 A.2.1.2⟩

lemma idealSupportMul_bijective {K : Type*} [Field K] [NumberField K]
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) : Function.Bijective (idealSupportMul (K := K) S) := by
  constructor
  · rintro ⟨I,J⟩ ⟨I',J'⟩ h
    have hh := ideal_support_split_unique I.1.2 I.2 J.2 I'.2 J'.2 (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext (Subtype.ext hh.1)) (Subtype.ext (Subtype.ext hh.2))
  · intro A
    obtain ⟨I,J,hi,hj,hs,hc,he⟩ := exists_ideal_support_split S hS A.1 A.2
    exact ⟨⟨⟨⟨I,hi⟩,hs⟩,⟨⟨J,hj⟩,hc⟩⟩,Subtype.ext he.symm⟩

def idealSupportEquiv {K : Type*} [Field K] [NumberField K]
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    primaryIntegralIdeals K S × coprimeIntegralIdeals K S ≃ {I : Ideal (𝓞 K) // I ≠ ⊥} :=
  Equiv.ofBijective (idealSupportMul S) (idealSupportMul_bijective S hS)

lemma nonzeroIntegralIdealUnit_mul {K : Type*} [Field K] [NumberField K]
    (I J : {I : Ideal (𝓞 K) // I ≠ ⊥}) :
    nonzeroIntegralIdealUnit ⟨I.1*J.1,mul_ne_zero I.2 J.2⟩ =
      nonzeroIntegralIdealUnit I * nonzeroIntegralIdealUnit J := by
  apply Units.ext
  exact FractionalIdeal.coeIdeal_mul I.1 J.1

lemma completed_ideal_mul_off {K : Type*} [Field K] [NumberField K]
    (I J : {I : Ideal (𝓞 K) // I ≠ ⊥}) (p : ℕ) [Fact p.Prime]
    (hJ : ¬ p ∣ Ideal.absNorm J.1) :
    completedFractionalIdeal p ((nonzeroIntegralIdealUnit I * nonzeroIntegralIdealUnit J :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      completedFractionalIdeal p (nonzeroIntegralIdealUnit I : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [Units.val_mul,completedFractionalIdeal_mul,completed_ideal_eq_off J p hJ]
  rw [← completedFractionalIdeal_mul,mul_one]

lemma globalIdealWeight_mul_coprime {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : {I : Ideal (𝓞 K) // I ≠ ⊥})
    (J : coprimeIntegralIdeals K (saturationIndex M).primeFactors) :
    globalIdealWeight M (nonzeroIntegralIdealUnit ⟨I.1*J.1.1,mul_ne_zero I.2 J.1.2⟩) =
      globalIdealWeight M (nonzeroIntegralIdealUnit I) := by
  rw [nonzeroIntegralIdealUnit_mul]
  apply Finset.prod_congr rfl
  intro p _
  exact localIdealWeight_eq_of_completion_eq M p.val _ _ (completed_ideal_mul_off I J.1 p.val (J.2 p.val p.2))

 

theorem weighted_ideal_convolution {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (F : ℕ → ℝ≥0∞) :
    (∑' A : {I : Ideal (𝓞 K) // I ≠ ⊥},
      globalIdealWeight M (nonzeroIntegralIdealUnit A) * F (Ideal.absNorm A.1)) =
      ∑' I : primaryIntegralIdeals K (saturationIndex M).primeFactors,
        globalIdealWeight M (nonzeroIntegralIdealUnit I.1) *
          ∑' J : coprimeIntegralIdeals K (saturationIndex M).primeFactors,
            F (Ideal.absNorm I.1.1 * Ideal.absNorm J.1.1) := by
  classical
  rw [← (idealSupportEquiv (saturationIndex M).primeFactors
    (fun p hp => (Nat.mem_primeFactors.mp hp).1)).tsum_eq]
  rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro I
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro J
  change globalIdealWeight M (nonzeroIntegralIdealUnit ⟨I.1.1*J.1.1,_⟩) * F (Ideal.absNorm (I.1.1*J.1.1)) = _
  rw [globalIdealWeight_mul_coprime, map_mul]

end PrimeDegreePackets


namespace PrimeDegreePackets
open NumberField IsDiscreteValuationRing
open scoped BigOperators Pointwise NumberField nonZeroDivisors ENNReal

 
def completedOrderIdealModule {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I : Ideal (completedMaximalOrder (K := K) p)) :
    Submodule (PadicInt p) (LocalAlgebra p K) :=
  (I.restrictScalars (PadicInt p)).map (completedMaximalOrder (K := K) p).val.toLinearMap

lemma completedOrderIdealModule_le {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I : Ideal (completedMaximalOrder (K := K) p)) :
    completedOrderIdealModule p I ≤ (completedMaximalOrder (K := K) p).toSubmodule := by
  rintro _ ⟨x,_hx,rfl⟩
  exact x.2

lemma completedOrderIdealModule_saturated {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I : Ideal (completedMaximalOrder (K := K) p)) :
    (completedMaximalOrder (K := K) p).toSubmodule * completedOrderIdealModule p I =
      completedOrderIdealModule p I := by
  apply le_antisymm
  · apply Submodule.mul_le.mpr
    intro x hx y hy
    obtain ⟨z,hz,rfl⟩ := hy
    exact Submodule.mem_map.mpr ⟨(⟨x,hx⟩ : completedMaximalOrder (K := K) p) * z,
      I.mul_mem_left _ hz,rfl⟩
  · intro x hx
    have h1 : (1 : LocalAlgebra p K) ∈ (completedMaximalOrder (K := K) p).toSubmodule :=
      (completedMaximalOrder (K := K) p).one_mem
    simpa only [one_mul] using Submodule.mul_mem_mul h1 hx

lemma completedOrderIdealModule_pow_mem {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I : Ideal (completedMaximalOrder (K := K) p)) (k : ℕ)
    (hk : (p : completedMaximalOrder (K := K) p)^k ∈ I)
    {x : LocalAlgebra p K} (hx : x ∈ (completedMaximalOrder (K := K) p).toSubmodule) :
    (p : PadicInt p)^k • x ∈ completedOrderIdealModule p I := by
  refine Submodule.mem_map.mpr ⟨(p : completedMaximalOrder (K := K) p)^k * ⟨x,hx⟩,
    I.mul_mem_right _ hk,?_⟩
  rw [Algebra.smul_def, map_pow, map_natCast]
  simp only [AlgHom.toLinearMap_apply, map_mul, map_pow, map_natCast, Subalgebra.val_apply]

 

theorem patch_completedOrder_ideals {K : Type*} [Field K] [NumberField K]
    (S : Finset ℕ) [∀ p : S, Fact p.val.Prime]
    (I : ∀ p : S, Ideal (completedMaximalOrder (K := K) p.val))
    (k : S → ℕ) (hk : ∀ p, (p.val : completedMaximalOrder (K := K) p.val)^(k p) ∈ I p) :
    ∃ J : {J : Ideal (𝓞 K) // J ≠ ⊥},
      (∀ p : S, completedFractionalIdeal p.val (J.1 : FractionalIdeal (𝓞 K)⁰ K) =
        completedOrderIdealModule p.val (I p)) ∧
      ∀ (r : ℕ) (hr : r.Prime), letI : Fact r.Prime := ⟨hr⟩;
        r ∉ S → completedFractionalIdeal r (J.1 : FractionalIdeal (𝓞 K)⁰ K) =
          completedFractionalIdeal r (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  classical
  let M := fractionalIdealFullLattice (K := K) rfl (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  obtain ⟨L,hLM,hL,hLoff⟩ := patch_fullLattice_completions M rfl
    (fun p : S => p.val) Subtype.val_injective k
    (fun p => completedOrderIdealModule p.val (I p))
    (fun p => completedOrderIdealModule_le p.val (I p))
    (fun p _ hx => completedOrderIdealModule_pow_mem p.val (I p) (k p) (hk p) hx)
  have hle : saturationFractionalIdeal L ≤ 1 := by
    change Submodule.span (𝓞 K) (L.carrier : Set K) ≤ _
    exact Submodule.span_le.mpr hLM
  obtain ⟨J,hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hJ0 : J ≠ ⊥ := by
    intro hz
    have H := saturationFractionalIdeal_ne_zero L
    exact H (by simpa [hz] using hJ.symm)
  refine ⟨⟨J,hJ0⟩,?_,?_⟩
  · intro p
    rw [hJ,completed_saturation,hL p,completedOrderIdealModule_saturated]
  · intro r hr
    let : Fact r.Prime := ⟨hr⟩
    intro hnot
    rw [hJ,completed_saturation,hLoff r hr (by simpa using hnot)]
    exact (completedMaximalOrder (K := K) r).isIdempotentElem_toSubmodule.eq

lemma integralIdeal_norm_product_of_off {K : Type*} [Field K] [NumberField K]
    (J : {I : Ideal (𝓞 K) // I ≠ ⊥}) (S : Finset ℕ) [∀ p : S, Fact p.val.Prime]
    (hoff : ∀ (r : ℕ) (hr : r.Prime), letI : Fact r.Prime := ⟨hr⟩;
      r ∉ S → completedFractionalIdeal r (J.1 : FractionalIdeal (𝓞 K)⁰ K) =
        completedFractionalIdeal r (1 : FractionalIdeal (𝓞 K)⁰ K))
    (T : ∀ p : S, ActualLocalModel p.val K) :
    Ideal.absNorm J.1 = ∏ p : S, ∏ i, p.val ^ ((T p).f i *
      integralIdealValuations p.val (T p) (nonzeroIntegralIdealUnit J)
        (nonzeroIntegralIdealUnit_le_one J) i) := by
  let U := nonzeroIntegralIdealUnit J
  have H := fullLattice_relIndex_eq_prod_local
    (fractionalIdealFullLattice (n := Module.finrank ℚ K) rfl 1)
    (fractionalIdealFullLattice rfl U) rfl (fun p : S => p.val) Subtype.val_injective
    (fun p => (Ideal.absNorm J.1).factorization p.val)
    (fun p _ hx => completed_ideal_primePower_mem J p.val hx)
    (by
      intro p hp
      let : Fact p.Prime := ⟨hp⟩
      intro hnot
      exact hoff p hp (fun hd => hnot ⟨⟨p,hd⟩,rfl⟩))
  rw [fullLattice_ideal_relIndex] at H
  apply H.trans
  apply Finset.prod_congr rfl
  intro p _
  change (completedFractionalIdeal p.val (U : FractionalIdeal (𝓞 K)⁰ K)).toAddSubgroup.relIndex
    (completedFractionalIdeal p.val (1 : FractionalIdeal (𝓞 K)⁰ K)).toAddSubgroup = _
  rw [← integralCompletedIdeal_relIndex]
  exact integralCompletedIdeal_cardQuot p.val (T p) U (nonzeroIntegralIdealUnit_le_one J)

lemma integralIdeal_support_of_off {K : Type*} [Field K] [NumberField K]
    (J : {I : Ideal (𝓞 K) // I ≠ ⊥}) (S : Finset ℕ) [∀ p : S, Fact p.val.Prime]
    (hoff : ∀ (r : ℕ) (hr : r.Prime), letI : Fact r.Prime := ⟨hr⟩;
      r ∉ S → completedFractionalIdeal r (J.1 : FractionalIdeal (𝓞 K)⁰ K) =
        completedFractionalIdeal r (1 : FractionalIdeal (𝓞 K)⁰ K)) :
    ∀ r, r.Prime → r ∣ Ideal.absNorm J.1 → r ∈ S := by
  classical
  intro r hr hd
  rw [integralIdeal_norm_product_of_off J S hoff (fun p => actualLocalModel p.val K)] at hd
  obtain ⟨p,_hp,hd⟩ := (hr.prime.dvd_finsetProd_iff _).mp hd
  obtain ⟨i,_hi,hd⟩ := (hr.prime.dvd_finsetProd_iff _).mp hd
  have he : r = p.val := ((Nat.dvd_prime (Fact.out : p.val.Prime)).mp (hr.dvd_of_dvd_pow hd)).resolve_left hr.ne_one
  exact he ▸ p.2

lemma modelIdeal_pow_mem {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (T : ActualLocalModel p K) (k : T.Index → ℕ) :
    (p : completedMaximalOrder (K := K) p)^(∑ i, k i) ∈
      Ideal.comap T.equiv.toRingHom (Ideal.pi (fun i => IsLocalRing.maximalIdeal (T.Ring i)^k i)) := by
  classical
  rw [Ideal.mem_comap]
  change T.equiv ((p : completedMaximalOrder (K := K) p)^(∑ i, k i)) ∈ _
  rw [map_pow,map_natCast]
  intro i
  rw [mem_maximalIdeal_pow_iff_addVal]
  change (k i : ℕ∞) ≤ addVal (T.Ring i) ((p : T.Ring i)^(∑ j, k j))
  rw [addVal_pow, show addVal (T.Ring i) (p : T.Ring i) = T.e i from by
    simpa only [map_natCast] using T.valuation_p i]
  simp only [nsmul_eq_mul, ← Nat.cast_mul]
  exact_mod_cast (Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i)).trans
    (Nat.le_mul_of_pos_right _ (T.e_pos i))

lemma ideal_pi_injective {ι : Type*} [DecidableEq ι] (R : ι → Type*) [∀ i, CommRing (R i)] :
    Function.Injective (Ideal.pi (R := R)) := by
  intro I J h
  funext i
  ext x
  constructor
  · intro hx
    have H := h ▸ Ideal.single_mem_pi (I := I) hx
    simpa only [Pi.single_eq_same] using H i
  · intro hx
    have H := h.symm ▸ Ideal.single_mem_pi (I := J) hx
    simpa only [Pi.single_eq_same] using H i

lemma dvr_power_injective (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    Function.Injective (fun k : ℕ => IsLocalRing.maximalIdeal R ^ k) := by
  intro k l h
  exact (pow_inj_of_not_isUnit
    (by simpa only [Ideal.isUnit_iff] using (IsLocalRing.maximalIdeal.isMaximal R).ne_top)
    (fun hz => IsDiscreteValuationRing.not_isField R (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hz))).mp h

 
theorem primaryIdealValuations_surjective {K : Type*} [Field K] [NumberField K]
    (S : Finset ℕ) [∀ p : S, Fact p.val.Prime] (T : ∀ p : S, ActualLocalModel p.val K) :
    Function.Surjective (primaryIdealValuations S T) := by
  classical
  intro k
  let I (p : S) := Ideal.comap (T p).equiv.toRingHom
    (Ideal.pi (fun i => IsLocalRing.maximalIdeal ((T p).Ring i) ^ k p i))
  obtain ⟨J,hJ,hJoff⟩ := patch_completedOrder_ideals S I (fun p => ∑ i, k p i)
    (fun p => modelIdeal_pow_mem p.val (T p) (k p))
  let J' : primaryIntegralIdeals K S := ⟨J,integralIdeal_support_of_off J S hJoff⟩
  refine ⟨J', ?_⟩
  funext p
  have hc : integralCompletedIdeal p.val (nonzeroIntegralIdealUnit J) =
      (I p).restrictScalars (PadicInt p.val) := by
    change (completedFractionalIdeal p.val (J.1 : FractionalIdeal (𝓞 K)⁰ K)).comap _ = _
    rw [hJ p]
    exact Submodule.comap_map_eq_of_injective
      (Subtype.val_injective : Function.Injective
        (completedMaximalOrder (K := K) p.val).val.toLinearMap) _
  have hm : ((I p).restrictScalars (PadicInt p.val)).map (T p).equiv.toLinearMap =
      (Ideal.pi (fun i => IsLocalRing.maximalIdeal ((T p).Ring i) ^ k p i)).restrictScalars
        (PadicInt p.val) := by
    change (Submodule.comap (T p).equiv.toLinearMap
      ((Ideal.pi (fun i => IsLocalRing.maximalIdeal ((T p).Ring i) ^ k p i)).restrictScalars
        (PadicInt p.val))).map (T p).equiv.toLinearMap = _
    exact Submodule.map_comap_eq_of_surjective (T p).equiv.surjective _
  have H := integralCompletedIdeal_model p.val (T p) (nonzeroIntegralIdealUnit J)
    (nonzeroIntegralIdealUnit_le_one J)
  rw [hc,hm] at H
  have HI : Ideal.pi (fun i => IsLocalRing.maximalIdeal ((T p).Ring i) ^ k p i) =
      Ideal.pi (fun i => IsLocalRing.maximalIdeal ((T p).Ring i) ^
        primaryIdealValuations S T J' p i) := by
    ext x
    exact SetLike.ext_iff.mp H x
  have Hp := ideal_pi_injective (T p).Ring HI
  funext i
  apply dvr_power_injective ((T p).Ring i)
  exact (congrFun Hp i).symm

def primaryIdealValuationEquiv {K : Type*} [Field K] [NumberField K]
    (S : Finset ℕ) [∀ p : S, Fact p.val.Prime] (T : ∀ p : S, ActualLocalModel p.val K) :
    primaryIntegralIdeals K S ≃ (∀ p : S, (T p).Index → ℕ) :=
  Equiv.ofBijective (primaryIdealValuations S T)
    ⟨primaryIdealValuations_injective S T,primaryIdealValuations_surjective S T⟩

lemma integralIdeal_norm_eq_shell_product {K : Type*} [Field K] [NumberField K]
    (S : Finset ℕ) [∀ p : S, Fact p.val.Prime] (T : ∀ p : S, ActualLocalModel p.val K)
    (J : primaryIntegralIdeals K S) :
    (Ideal.absNorm J.1.1 : ℝ≥0∞) =
      ∏ p : S, shellNorm (T p).Ring (primaryIdealValuations S T J p) := by
  rw [integralIdeal_norm_eq_valuation_product J.1 S J.2 T]
  simp only [Nat.cast_prod, Nat.cast_pow, shellNorm]
  apply Finset.prod_congr rfl
  intro p _
  apply Finset.prod_congr rfl
  intro i _
  rw [(T p).card_residue, Nat.cast_pow, pow_mul]
  rfl

lemma ennreal_inv_prod_finite {ι : Type*} (S : Finset ι) (f : ι → ℝ≥0∞)
    (hf : ∀ i ∈ S, f i ≠ ∞) : (∏ i ∈ S, f i)⁻¹ = ∏ i ∈ S, (f i)⁻¹ :=
  ENNReal.prod_inv_distrib (fun _ _ j hj _ => Or.inr (hf j hj))

lemma inverse_shellNorm_sum {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
    (T : ActualLocalModel p K) :
    (∑' k : T.Index → ℕ, (shellNorm T.Ring k)⁻¹) = (localZinv T.Ring)⁻¹ := by
  classical
  simp only [shellNorm]
  have hprod (k : T.Index → ℕ) := ennreal_inv_prod_finite Finset.univ
    (fun i => (Nat.card (IsLocalRing.ResidueField (T.Ring i)) : ℝ≥0∞) ^ k i)
    (fun i _ => ENNReal.pow_ne_top (by simp))
  simp_rw [hprod, ENNReal.inv_pow]
  rw [ennreal_tsum_fintype_prod (fun _ : T.Index => ℕ)
    (fun i k => (Nat.card (IsLocalRing.ResidueField (T.Ring i)) : ℝ≥0∞)⁻¹ ^ k)]
  simp_rw [ENNReal.tsum_geometric]
  exact (ennreal_inv_prod_finite _ _ (fun i _ => ENNReal.sub_ne_top (by simp))).symm

 
theorem primaryIntegralIdeals_inverse_norm_series {K : Type*} [Field K] [NumberField K]
    (S : Finset ℕ) [∀ p : S, Fact p.val.Prime] (T : ∀ p : S, ActualLocalModel p.val K) :
    (∑' J : primaryIntegralIdeals K S, (Ideal.absNorm J.1.1 : ℝ≥0∞)⁻¹) =
      ∏ p : S, (localZinv (T p).Ring)⁻¹ := by
  classical
  simp_rw [integralIdeal_norm_eq_shell_product S T,
    ennreal_inv_prod_finite _ _ (fun p _ => shellNorm_ne_top (T p).Ring _)]
  calc
    _ = ∑' k : ∀ p : S, (T p).Index → ℕ, ∏ p : S, (shellNorm (T p).Ring (k p))⁻¹ :=
      (primaryIdealValuationEquiv S T).tsum_eq _
    _ = _ := by
      rw [ennreal_tsum_fintype_prod (fun p : S => (T p).Index → ℕ)
        (fun p k => (shellNorm (T p).Ring k)⁻¹)]
      simp_rw [inverse_shellNorm_sum]

end PrimeDegreePackets
end
end

end OAI
