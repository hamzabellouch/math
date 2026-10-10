import OAI.NumberTheory.Jacobsthal.Analysis.SmallModelMeasure
import OAI.NumberTheory.Jacobsthal.Estimates.ActualPatternClass
import OAI.NumberTheory.Jacobsthal.Partitions.ActualCoordinateBlocks
import OAI.NumberTheory.Jacobsthal.Sieve.PrimeFibreBrunBound

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosVarianceSmallModel
open ErdosInverseBoxHeight ErdosInverseEuler

theorem source_residue_fibre_bound (alpha : ℝ) (ha : 0 < alpha) :
    ∃ C : ℝ,0 < C ∧ ∀ xi : ℝ,0 < xi → xi ≤ 1 →
      ∀ᶠ z : ℝ in atTop,1 < z ∧
      ∀ (P : Finset ℕ) (R H C0 : ℝ) (m : ℤ) (M : ℕ) (b : ℤ),
        z^alpha ≤ R → 0 < H → 0 < M → H ≤ R^((4 : ℝ)/5) →
        (M : ℝ) ≤ H*(smallModulus (sourceW z) : ℝ) →
        totalScale R H C0/H ≤ (sourceZ z)^12 →
        (∀ p ∈ P,p.Prime ∧ R < (p : ℝ) ∧ (p : ℝ) ≤ (1+xi)*R) →
        ((residueFibre P H C0 m M b).card : ℝ) ≤
          C*primeWidth R xi H C0/((M.totient : ℝ)*Real.log R) := by
  obtain ⟨C,B,hC,hB,hBrun⟩ := residue_fibre_prime_bound
  refine ⟨50*C,by positivity,?_⟩
  intro xi hxi hxi1
  have hgrowth := tendsto_rpow_atTop (by positivity : 0 < alpha/10)
  filter_upwards [source_prime_width_lower alpha xi ha hxi hxi1,source_small_modulus_R alpha ha,
    hgrowth.eventually_ge_atTop B] with z hWidth hMod hzB
  refine ⟨hWidth.1,?_⟩
  intro P R H C0 m M b hRlo hH hM hHsmall hMbound hRatio hP
  have hz0 : 0 < z := by linarith [hWidth.1]
  have hR1 : 1 < R := (Real.one_lt_rpow hWidth.1 ha).trans_le hRlo
  have hR : 0 < R := by linarith
  have hlogR : 0 < Real.log R := Real.log_pos hR1
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hphi : (0 : ℝ) < M.totient := by exact_mod_cast Nat.totient_pos.mpr hM
  have hX := primeWidth_pos R xi H C0 hR hxi hH
  have hX19 := hWidth.2 R H C0 hRlo hH hRatio
  have hM17 : (M : ℝ) ≤ R^((17 : ℝ)/20) := by
    calc
      _ ≤ H*(smallModulus (sourceW z) : ℝ) := hMbound
      _ ≤ R^((4 : ℝ)/5)*R^((1 : ℝ)/20) :=
        mul_le_mul hHsmall (hMod.2 R hRlo) (Nat.cast_nonneg _) (Real.rpow_nonneg hR.le _)
      _ = _ := by rw [← Real.rpow_add hR];norm_num
  have hLength : R^((1 : ℝ)/10) ≤ 5*primeWidth R xi H C0/(M : ℝ) := by
    apply (le_div_iff₀ hMp).mpr
    calc
      _ ≤ R^((1 : ℝ)/10)*R^((17 : ℝ)/20) :=
        mul_le_mul_of_nonneg_left hM17 (Real.rpow_nonneg hR.le _)
      _ = R^((19 : ℝ)/20) := by rw [← Real.rpow_add hR];norm_num
      _ ≤ primeWidth R xi H C0 := hX19
      _ ≤ _ := by linarith
  have hB_R : B ≤ R^((1 : ℝ)/10) := by
    apply le_trans hzB
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hz0.le alpha) hRlo (by norm_num : (0 : ℝ) ≤ 1/10)
    simpa only [← Real.rpow_mul hz0.le,show alpha*((1 : ℝ)/10) = alpha/10 by ring] using hh
  have hLog : (1/10 : ℝ)*Real.log R ≤ Real.log (5*primeWidth R xi H C0/(M : ℝ)) := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hR (1/10)) hLength
    simpa only [Real.log_rpow hR] using hh
  calc
    _ ≤ C*(5*primeWidth R xi H C0)/
        ((M.totient : ℝ)*Real.log (5*primeWidth R xi H C0/(M : ℝ))) :=
      hBrun P R xi H C0 m M b hR hxi hxi1 hH hM (hB_R.trans hLength) hP
    _ ≤ C*(5*primeWidth R xi H C0)/((M.totient : ℝ)*((1/10 : ℝ)*Real.log R)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hLog hphi.le)
    _ = _ := by field_simp;norm_num

end ErdosVarianceSmallModel

end

section

namespace ErdosVarianceSmallModel
open ErdosVarianceEffective
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def goodPrimes (P : Finset ℕ) (H : ℕ) : Finset ℕ := P.filter (fun p => H.Coprime p)

noncomputable def primeM (P : Finset ℕ) (H : ℕ) (C0 : ℤ) (hP : ∀ p ∈ P,p.Prime)
    (p : goodPrimes P H) : ℤ := by
  letI : NeZero p.val := ⟨(hP _ (Finset.mem_filter.mp p.property).1).ne_zero⟩
  exact intervalM0 p.val H (Finset.mem_filter.mp p.property).2 C0

noncomputable def primeK (P : Finset ℕ) (H : ℕ) (C0 : ℤ) (hP : ∀ p ∈ P,p.Prime)
    (p : goodPrimes P H) : ℕ := by
  letI : NeZero p.val := ⟨(hP _ (Finset.mem_filter.mp p.property).1).ne_zero⟩
  exact intervalK p.val H (Finset.mem_filter.mp p.property).2 C0

noncomputable def primePoint (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (p : goodPrimes P H) : ModelPoint w H :=
  ⟨primeM P H C0 hP p,
    ZMod.unitOfCoprime p.val (prime_coprime_small_pattern w hw H p.val
      (hP _ (Finset.mem_filter.mp p.property).1) (hlarge _ (Finset.mem_filter.mp p.property).1)),
    (primeK P H C0 hP p : ZMod (divisorModulus w H))⟩

theorem primeMK_identity (P : Finset ℕ) (H : ℕ) (C0 : ℤ) (hP : ∀ p ∈ P,p.Prime)
    (p : goodPrimes P H) :
    (p.val : ℤ)*primeM P H C0 hP p = C0+(H : ℤ)*(primeK P H C0 hP p : ℤ) := by
  let : NeZero p.val := ⟨(hP _ (Finset.mem_filter.mp p.property).1).ne_zero⟩
  exact intervalM0_identity p.val H (Finset.mem_filter.mp p.property).2 C0

theorem primeM_bounds (P : Finset ℕ) (H : ℕ) (C0 : ℤ) (hP : ∀ p ∈ P,p.Prime) (hH : 0 < H)
    (p : goodPrimes P H) :
    (C0 : ℝ)/(p.val : ℝ) ≤ (primeM P H C0 hP p : ℝ) ∧
      (primeM P H C0 hP p : ℝ) < (C0 : ℝ)/(p.val : ℝ)+(H : ℝ) := by
  let : NeZero p.val := ⟨(hP _ (Finset.mem_filter.mp p.property).1).ne_zero⟩
  exact intervalM0_bounds p.val H (Finset.mem_filter.mp p.property).2 C0 hH

theorem primeM_coprime (P : Finset ℕ) (H : ℕ) (C0 : ℤ) (hP : ∀ p ∈ P,p.Prime)
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (p : goodPrimes P H) :
    (primeM P H C0 hP p).natAbs.Coprime H := by
  apply Nat.coprime_of_dvd
  intro t ht htm htH
  have htm' : (t : ℤ) ∣ primeM P H C0 hP p := Int.natCast_dvd.mpr htm
  have htH' : (t : ℤ) ∣ (H : ℤ) := by exact_mod_cast htH
  have hsub := dvd_sub (dvd_mul_of_dvd_right htm' (p.val : ℤ))
    (dvd_mul_of_dvd_left htH' (primeK P H C0 hP p : ℤ))
  rw [primeMK_identity,add_sub_cancel_right] at hsub
  have hdiv := Nat.dvd_gcd (Int.natCast_dvd.mp hsub) htH
  have hg : Nat.gcd C0.natAbs H = 1 := by simpa only [Int.gcd_def,Int.natAbs_natCast] using hC0
  rw [hg] at hdiv
  exact ht.not_dvd_one hdiv

theorem primePoint_mem_model (P : Finset ℕ) (R xi w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (hR : 0 < R) (hxi : 0 ≤ xi) (hH : 0 < H) (hC0 : Int.gcd C0 (H : ℤ) = 1)
    (hbin : ∀ p ∈ P,R < (p : ℝ) ∧ (p : ℝ) ≤ (1+xi)*R) (p : goodPrimes P H) :
    primePoint P w H C0 hw hP hlarge p ∈ modelUniverse R xi w H C0 := by
  have hpP := (Finset.mem_filter.mp p.property).1
  have hm := moving_interval_enclosure R xi (H : ℝ) (C0 : ℝ) (p.val : ℝ)
    (primeM P H C0 hP p) hR hxi (hbin _ hpP).1 (hbin _ hpP).2 (primeM_bounds P H C0 hP hH p)
  apply (mem_modelUniverse R xi w H C0 _).mpr
  exact ⟨hm.1,hm.2,primeM_coprime P H C0 hP hC0 p⟩

end ErdosVarianceSmallModel

end

section

namespace ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def primeFibre (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (v : ModelPoint w H) : Finset (goodPrimes P H) :=
  Finset.univ.filter (fun p => primePoint P w H C0 hw hP hlarge p = v)

theorem primeFibre_image_subset (P : Finset ℕ) (w : ℝ) (H : ℕ) [NeZero H] (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (v : ModelPoint w H) (hm : v.1.natAbs.Coprime H) :
    (primeFibre P w H C0 hw hP hlarge v).image Subtype.val ⊆
      residueFibre P (H : ℝ) (C0 : ℝ) v.1 (H*divisorModulus w H*coprimeModulus w H)
        (patternClass w H C0 hC0 v.1 hm v.2 : ℤ) := by
  intro q hq
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
  have he := (Finset.mem_filter.mp hp).2
  have hpm : primeM P H C0 hP p = v.1 := congrArg Prod.fst he
  have hp1 : (p.val : ZMod (coprimeModulus w H)) = (v.2.1 : ZMod (coprimeModulus w H)) := by
    simpa only [primePoint,ZMod.coe_unitOfCoprime] using
      congrArg (fun z : ModelPoint w H => (z.2.1 : ZMod (coprimeModulus w H))) he
  have hk0 : (primeK P H C0 hP p : ZMod (divisorModulus w H)) = v.2.2 :=
    congrArg (fun z : ModelPoint w H => z.2.2) he
  have hEquation : (p.val : ℤ)*v.1 = C0+(H : ℤ)*(primeK P H C0 hP p : ℤ) := by
    rw [← hpm]
    exact primeMK_identity P H C0 hP p
  have hbounds := primeM_bounds P H C0 hP (Nat.pos_of_ne_zero (NeZero.ne H)) p
  rw [hpm] at hbounds
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp p.property).1,hbounds⟩,?_⟩
  exact actual_pattern_class w H C0 hC0 v.1 hm v.2 p.val (primeK P H C0 hP p) hEquation hp1 hk0

theorem primeFibre_card_le_residue (P : Finset ℕ) (w : ℝ) (H : ℕ) [NeZero H] (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (v : ModelPoint w H) (hm : v.1.natAbs.Coprime H) :
    (primeFibre P w H C0 hw hP hlarge v).card ≤
      (residueFibre P (H : ℝ) (C0 : ℝ) v.1 (H*divisorModulus w H*coprimeModulus w H)
        (patternClass w H C0 hC0 v.1 hm v.2 : ℤ)).card := by
  calc
    _ = ((primeFibre P w H C0 hw hP hlarge v).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ _ := Finset.card_le_card (primeFibre_image_subset P w H C0 hw hP hlarge hC0 v hm)

end ErdosVarianceSmallModel

end

section

namespace ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def indexedPrimeEvent (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (E : ModelPoint w H → Prop) : Finset (goodPrimes P H) :=
  Finset.univ.filter (fun p => E (primePoint P w H C0 hw hP hlarge p))

noncomputable def actualPrimeEvent (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (E : ModelPoint w H → Prop) : Finset ℕ :=
  (indexedPrimeEvent P w H C0 hw hP hlarge E).image Subtype.val

theorem actualPrimeEvent_card (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (E : ModelPoint w H → Prop) :
    (actualPrimeEvent P w H C0 hw hP hlarge E).card = (indexedPrimeEvent P w H C0 hw hP hlarge E).card :=
  Finset.card_image_of_injective _ Subtype.val_injective

theorem actualPrimeEvent_card_fibres (P : Finset ℕ) (R xi w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (hR : 0 < R) (hxi : 0 ≤ xi) (hH : 0 < H) (hC0 : Int.gcd C0 (H : ℤ) = 1)
    (hbin : ∀ p ∈ P,R < (p : ℝ) ∧ (p : ℝ) ≤ (1+xi)*R) (E : ModelPoint w H → Prop) :
    (actualPrimeEvent P w H C0 hw hP hlarge E).card =
      ∑ v ∈ (modelUniverse R xi w H C0).filter E,(primeFibre P w H C0 hw hP hlarge v).card := by
  rw [actualPrimeEvent_card]
  have hmaps : (indexedPrimeEvent P w H C0 hw hP hlarge E : Set (goodPrimes P H)).MapsTo
      (primePoint P w H C0 hw hP hlarge) ((modelUniverse R xi w H C0).filter E) := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨primePoint_mem_model P R xi w H C0 hw hP hlarge hR hxi hH hC0 hbin p,
      (Finset.mem_filter.mp hp).2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro v hv
  congr 1
  ext p
  simp only [indexedPrimeEvent,primeFibre,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · exact fun hh => hh.2
  · intro he
    exact ⟨he.symm ▸ (Finset.mem_filter.mp hv).2,he⟩

end ErdosVarianceSmallModel

end

end Erdos970

end OAI
