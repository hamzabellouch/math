import Mathlib
import OAI.NumberTheory.PrimePackets.PrimeFactors

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
namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators

 

structure ActualLocalModel (p : ℕ) [Fact p.Prime] (K : Type u)
    [Field K] [NumberField K] where
  Index : Type u
  fintype : Fintype Index
  Ring : Index → Type u
  commRing : ∀ i, CommRing (Ring i)
  domain : ∀ i, IsDomain (Ring i)
  dvr : ∀ i, IsDiscreteValuationRing (Ring i)
  algebra : ∀ i, Algebra (PadicInt p) (Ring i)
  finiteResidue : ∀ i, Finite (IsLocalRing.ResidueField (Ring i))
  topology : ∀ i, TopologicalSpace (Ring i)
  topRing : ∀ i, IsTopologicalRing (Ring i)
  compactSpace : ∀ i, CompactSpace (Ring i)
  t2Space : ∀ i, T2Space (Ring i)
  secondCountable : ∀ i, SecondCountableTopology (Ring i)
  equiv : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] ∀ i, Ring i
  e : Index → ℕ
  f : Index → ℕ
  continuous_equiv : Continuous equiv
  continuous_symm : Continuous equiv.symm
  e_pos : ∀ i, 0 < e i
  f_pos : ∀ i, 0 < f i
  valuation_p : ∀ i, addVal (Ring i) (algebraMap (PadicInt p) (Ring i) p) = e i
  card_residue : ∀ i, Nat.card (IsLocalRing.ResidueField (Ring i)) = p ^ f i
  degree : ∑ i, f i * e i = Module.finrank ℚ K

attribute [instance] ActualLocalModel.fintype ActualLocalModel.commRing
  ActualLocalModel.domain ActualLocalModel.dvr ActualLocalModel.algebra
  ActualLocalModel.finiteResidue ActualLocalModel.topology ActualLocalModel.topRing
  ActualLocalModel.compactSpace ActualLocalModel.t2Space ActualLocalModel.secondCountable

lemma actualLocalModel_nonempty (p : ℕ) [Fact p.Prime] (K : Type u)
    [Field K] [NumberField K] : Nonempty (ActualLocalModel p K) := by
  obtain ⟨I,hI,R,hR,hd,hDVR,hA,hk,hT,hTR,hc,ht,hsc,E,e,f,hE,hE',he,hf,hv,hk',hef⟩ :=
    completedMaximalOrder_exists_full_local_model p K
  exact ⟨⟨I,hI,R,hR,hd,hDVR,hA,hk,hT,hTR,hc,ht,hsc,E,e,f,hE,hE',he,hf,hv,hk',hef⟩⟩

def actualLocalModel (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K] :
    ActualLocalModel p K := (actualLocalModel_nonempty p K).some

instance model_measurableSpace {p : ℕ} [Fact p.Prime] {K : Type u} [Field K] [NumberField K]
    (T : ActualLocalModel p K) (i : T.Index) : MeasurableSpace (T.Ring i) := borel _

instance model_borelSpace {p : ℕ} [Fact p.Prime] {K : Type u} [Field K] [NumberField K]
    (T : ActualLocalModel p K) (i : T.Index) : BorelSpace (T.Ring i) := ⟨rfl⟩

instance model_units_measurableSpace {p : ℕ} [Fact p.Prime] {K : Type u}
    [Field K] [NumberField K] (T : ActualLocalModel p K) :
    MeasurableSpace (∀ i, T.Ring i)ˣ := borel _

instance model_units_borelSpace {p : ℕ} [Fact p.Prime] {K : Type u}
    [Field K] [NumberField K] (T : ActualLocalModel p K) :
    BorelSpace (∀ i, T.Ring i)ˣ := ⟨rfl⟩

 
def modelAddHaarProbability {p : ℕ} [Fact p.Prime] {K : Type u} [Field K] [NumberField K]
    (T : ActualLocalModel p K) (i : T.Index) : Measure (T.Ring i) :=
  Measure.addHaarMeasure (⟨⟨Set.univ,isCompact_univ⟩,by simp⟩ :
    TopologicalSpace.PositiveCompacts (T.Ring i))

instance modelAddHaarProbability_isProbability {p : ℕ} [Fact p.Prime] {K : Type u}
    [Field K] [NumberField K] (T : ActualLocalModel p K) (i : T.Index) :
    IsProbabilityMeasure (modelAddHaarProbability T i) := by
  constructor
  exact Measure.addHaarMeasure_self

instance modelAddHaarProbability_isHaar {p : ℕ} [Fact p.Prime] {K : Type u}
    [Field K] [NumberField K] (T : ActualLocalModel p K) (i : T.Index) :
    (modelAddHaarProbability T i).IsAddHaarMeasure :=
  inferInstanceAs (Measure.addHaarMeasure _).IsAddHaarMeasure

instance model_actual_unit_probability {p : ℕ} [Fact p.Prime] {K : Type u}
    [Field K] [NumberField K] (T : ActualLocalModel p K) :
    IsProbabilityMeasure (modelUnitProbability p T.equiv) :=
  modelUnitProbability_isProbability p T.equiv T.continuous_equiv

instance model_actual_unit_haar {p : ℕ} [Fact p.Prime] {K : Type u}
    [Field K] [NumberField K] (T : ActualLocalModel p K) :
    (modelUnitProbability p T.equiv).IsHaarMeasure :=
  modelUnitProbability_isHaar p T.equiv T.continuous_equiv

 
abbrev actualValuationTuples {n : ℕ} {K : Type u} [Field K] [NumberField K]
    (M : FullLattice n K) := ∀ p : labelPrimes M, (actualLocalModel p.val K).Index → ℕ

def actualTupleWeight {n : ℕ} {K : Type u} [Field K] [NumberField K]
    (M : FullLattice n K) (k : actualValuationTuples M) : ℝ≥0∞ :=
  ∏ p : labelPrimes M, localShellProbability (actualLocalModel p.val K).Ring
    (modelUnitProbability p.val (actualLocalModel p.val K).equiv)
    (modelLocalModule M p.val (actualLocalModel p.val K).equiv) (k p)

def actualTupleNorm {n : ℕ} {K : Type u} [Field K] [NumberField K]
    (M : FullLattice n K) (k : actualValuationTuples M) : ℝ≥0∞ :=
  ∏ p : labelPrimes M, shellNorm (actualLocalModel p.val K).Ring (k p)

def actualLocalZ {n : ℕ} {K : Type u} [Field K] [NumberField K]
    (M : FullLattice n K) : ℝ≥0∞ :=
  ∏ p : labelPrimes M, (localZinv (actualLocalModel p.val K).Ring)⁻¹

lemma actualTupleNorm_ne_zero {n : ℕ} {K : Type u} [Field K] [NumberField K]
    (M : FullLattice n K) (k : actualValuationTuples M) : actualTupleNorm M k ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _p _ => shellNorm_ne_zero _ _

lemma actualTupleNorm_ne_top {n : ℕ} {K : Type u} [Field K] [NumberField K]
    (M : FullLattice n K) (k : actualValuationTuples M) : actualTupleNorm M k ≠ ∞ :=
  ENNReal.prod_ne_top fun _p _ => shellNorm_ne_top _ _

 
theorem actual_tuple_weight_sum {n : ℕ} {K : Type u} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) :
    (∑' k, actualTupleWeight M k / actualTupleNorm M k) =
      (saturationIndex M : ℝ≥0∞)⁻¹ * actualLocalZ M := by
  let T (p : labelPrimes M) := actualLocalModel p.val K
  let L (p : labelPrimes M) := modelLocalModule M p.val (T p).equiv
  let (p : labelPrimes M) : Finite ((∀ i, (T p).Ring i) ⧸ L p) :=
    modelLocalModule_finiteQuotient M hn p.val (T p).equiv
  have h := global_local_weight_sum (saturationIndex M).primeFactors
    (fun p => (T p).Index) (fun p => (T p).Ring)
    (fun p => modelAddHaarProbability (T p)) (fun p => modelUnitProbability p.val (T p).equiv)
    L (fun p => (modelLocalModule_open M hn p.val (T p).equiv (T p).continuous_symm).measurableSet)
  have hq : localIndexProduct (saturationIndex M).primeFactors (fun p => (T p).Index)
      (fun p => (T p).Ring) L = saturationIndex M := by
    unfold localIndexProduct
    dsimp only [L]
    simp_rw [modelLocalModule_cardQuot]
    exact (saturationIndex_eq_prod_integralNormalizedModule M hn).symm
  rw [hq] at h
  exact h

section
variable (n : ℕ) (S : Finset ℕ) [∀ p : S, Fact p.val.Prime]
    (ι : S → Type*) [∀ p, Fintype (ι p)]
    (R : ∀ p : S, ι p → Type*)
    [∀ p i, CommRing (R p i)] [∀ p i, IsDomain (R p i)]
    [∀ p i, IsDiscreteValuationRing (R p i)]
    [∀ p i, Algebra (PadicInt p.val) (R p i)]
    [∀ p i, TopologicalSpace (R p i)] [∀ p i, IsTopologicalRing (R p i)]
    [∀ p i, CompactSpace (R p i)] [∀ p i, T2Space (R p i)]
    [∀ p i, MeasurableSpace (R p i)] [∀ p i, BorelSpace (R p i)]
    [∀ p i, SecondCountableTopology (R p i)]
    [∀ p, MeasurableSpace (∀ i, R p i)ˣ] [∀ p, BorelSpace (∀ i, R p i)ˣ]
    (μ : ∀ p i, Measure (R p i)) [∀ p i, IsProbabilityMeasure (μ p i)]
    [∀ p i, (μ p i).IsAddHaarMeasure]
    (ν : ∀ p, Measure (∀ i, R p i)ˣ) [∀ p, IsProbabilityMeasure (ν p)]
    [∀ p, (ν p).IsMulRightInvariant]
    (L : ∀ p : S, Submodule (PadicInt p.val) (∀ i, R p i))
    [∀ p, Finite ((∀ i, R p i) ⧸ L p)]

include μ in
 

theorem global_local_weight_moment_of_support_prod_le
    (hn : 0 < n) (ε : ℝ) (hε : 0 < ε)
    (hL : ∀ p, MeasurableSet (L p : Set (∀ i, R p i)))
    (hprod : (∏ p ∈ S, (p : ℝ)) ≤ (localIndexProduct S ι R L : ℝ))
    (hsat : ∀ p, Ideal.span (L p : Set (∀ i, R p i)) = ⊤)
    (e f : ∀ p, ι p → ℕ) (he0 : ∀ p i, 0 < e p i) (hf0 : ∀ p i, 0 < f p i)
    (he : ∀ p i, addVal (R p i) (algebraMap (PadicInt p.val) (R p i) p.val) = e p i)
    (hcard : ∀ p i, Nat.card (IsLocalRing.ResidueField (R p i)) = p.val ^ f p i)
    (hdegree : ∀ p, ∑ i, f p i * e p i = n) :
    (∑' k : ∀ p, ι p → ℕ, packetLocalWeight S ι R ν L k *
      packetLocalNorm S ι R k ^ (1 / (2 * (n : ℝ)) - 1)) ≤
      (localIndexProduct S ι R L : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (localProductConstant n ε hε * (localIndexProduct S ι R L : ℝ) ^ ε) := by
  have hnum (p : S) : Fintype.card (ι p) ≤ n := by
    rw [← hdegree p, ← Finset.card_univ]
    calc
      _ = ∑ _i : ι p, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => Nat.mul_pos (hf0 p i) (he0 p i))
  have hmajor := localProductConstant_bound n ε hε S (localIndexProduct S ι R L : ℝ)
    (fun p hp => (show Fact p.Prime from inferInstanceAs (Fact (⟨p, hp⟩ : S).val.Prime)).out.one_le)
    hprod
  have hfactor := local_weight_product_factorization (fun p : S => ι p → ℕ)
    (fun p k => localShellProbability (R p) (ν p) (L p) k)
    (fun p k => shellNorm (R p) k) (1 / (2 * (n : ℝ)) - 1)
  unfold packetLocalWeight packetLocalNorm
  have hid : (∑' k : ∀ p, ι p → ℕ,
      (∏ p, localShellProbability (R p) (ν p) (L p) (k p)) *
        (∏ p, shellNorm (R p) (k p)) ^ (1 / (2 * (n : ℝ)) - 1)) =
      ∏ p, ∑' k : ι p → ℕ, localShellProbability (R p) (ν p) (L p) k *
        shellNorm (R p) k ^ (1 / (2 * (n : ℝ)) - 1) := by
    simpa only [ENNReal.prod_rpow_of_ne_top (fun p _ => shellNorm_ne_top (R p) _) _] using hfactor
  rw [hid]
  calc
    _ ≤ ∏ p : S, ((L p).cardQuot : ℝ≥0∞)⁻¹ * ENNReal.ofReal (localMajorant n p.val) := by
      apply Finset.prod_le_prod
      intro p _
      apply (local_weight_moment (R p) (μ p) (ν p) p.val (L p) (hL p) (hsat p)
        (e p) (f p) (he0 p) (hf0 p) (he p) (hcard p) n hn (hdegree p)).trans
      apply mul_le_mul_right
      exact localEulerFactor_le_majorant (R p) p.val n (Fact.out : p.val.Prime).one_lt
        (f p) (hf0 p) (hcard p) (hnum p)
    _ = (localIndexProduct S ι R L : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (∏ p ∈ S, localMajorant n p) := by
      rw [Finset.prod_mul_distrib]
      congr 1
      · rw [localIndexProduct, Nat.cast_prod]
        exact (ENNReal.prod_inv_distrib (fun _ _ _ _ _ => Or.inr (by simp))).symm
      · rw [← Finset.prod_coe_sort S]
        exact (ENNReal.ofReal_prod_of_nonneg (fun p _ =>
          localMajorant_nonneg n p.val (Fact.out : p.val.Prime).one_le)).symm
    _ ≤ _ := mul_le_mul_right (ENNReal.ofReal_le_ofReal hmajor) _

end

 

theorem actual_tuple_weight_moment {n : ℕ} {K : Type u} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (hn0 : 0 < n)
    (ε : ℝ) (hε : 0 < ε) :
    (∑' k, actualTupleWeight M k * actualTupleNorm M k ^ (1 / (2 * (n : ℝ)) - 1)) ≤
      (saturationIndex M : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (localProductConstant n ε hε * (saturationIndex M : ℝ) ^ ε) := by
  let T (p : labelPrimes M) := actualLocalModel p.val K
  let L (p : labelPrimes M) := modelLocalModule M p.val (T p).equiv
  let (p : labelPrimes M) : Finite ((∀ i, (T p).Ring i) ⧸ L p) :=
    modelLocalModule_finiteQuotient M hn p.val (T p).equiv
  have hq : localIndexProduct (saturationIndex M).primeFactors (fun p => (T p).Index)
      (fun p => (T p).Ring) L = saturationIndex M := by
    unfold localIndexProduct
    dsimp only [L]
    simp_rw [modelLocalModule_cardQuot]
    exact (saturationIndex_eq_prod_integralNormalizedModule M hn).symm
  have hprod : (∏ p ∈ (saturationIndex M).primeFactors, (p : ℝ)) ≤
      (localIndexProduct (saturationIndex M).primeFactors (fun p => (T p).Index)
        (fun p => (T p).Ring) L : ℝ) := by
    rw [hq, ← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (saturationIndex_ne_zero M))
      (Nat.prod_primeFactors_dvd (saturationIndex M))
  have H := global_local_weight_moment_of_support_prod_le n (saturationIndex M).primeFactors
    (fun p => (T p).Index) (fun p => (T p).Ring)
    (fun p => modelAddHaarProbability (T p)) (fun p => modelUnitProbability p.val (T p).equiv)
    L hn0 ε hε
    (fun p => (modelLocalModule_open M hn p.val (T p).equiv (T p).continuous_symm).measurableSet)
    hprod (fun p => modelLocalModule_saturated M p.val (T p).equiv)
    (fun p => (T p).e) (fun p => (T p).f) (fun p => (T p).e_pos)
    (fun p => (T p).f_pos) (fun p => (T p).valuation_p)
    (fun p => (T p).card_residue) (fun p => (T p).degree.trans hn)
  rw [hq] at H
  exact H

end PrimeDegreePackets


namespace PrimeDegreePackets
open IsDiscreteValuationRing
open scoped BigOperators Pointwise NumberField nonZeroDivisors

lemma dvr_principal_eq_maximal_pow {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (x : R) (hx : x ≠ 0) :
    Ideal.span ({x} : Set R) = IsLocalRing.maximalIdeal R ^ (addVal R x).toNat := by
  ext y
  rw [Ideal.mem_span_singleton, ← addVal_le_iff_dvd, mem_maximalIdeal_pow_iff_addVal,
    ENat.natCast_toNat (addVal_eq_top_iff.not.mpr hx)]

 

lemma product_dvr_principal_eq {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)]
    [∀ i, IsDiscreteValuationRing (R i)] (x : ∀ i, R i) (hx : ∀ i, x i ≠ 0) :
    Ideal.span ({x} : Set (∀ i, R i)) =
      Ideal.pi (fun i => IsLocalRing.maximalIdeal (R i) ^ (addVal (R i) (x i)).toNat) := by
  rw [← Ideal.pi_span]
  congr 1
  funext i
  exact dvr_principal_eq_maximal_pow _ (hx i)

lemma cardQuot_pi_restrictScalars {S : Type*} [CommRing S] {ι : Type*} [Fintype ι]
    (R : ι → Type*) [∀ i, CommRing (R i)] [∀ i, Algebra S (R i)]
    (J : ∀ i, Ideal (R i)) :
    ((Ideal.pi J).restrictScalars S).cardQuot = ∏ i, (J i).cardQuot := by
  classical
  have h : (Ideal.pi J).restrictScalars S =
      Submodule.pi Set.univ (fun i => (J i).restrictScalars S) := by
    ext x
    simp only [Submodule.restrictScalars_mem, Ideal.mem_pi, Submodule.mem_pi,
      Set.mem_univ, forall_const]
  rw [h]
  rw [Submodule.cardQuot_apply]
  rw [Nat.card_congr (Submodule.quotientPi (fun i => (J i).restrictScalars S)).toEquiv,
    Nat.card_pi]
  rfl

lemma cardQuot_product_dvr_powers {S : Type*} [CommRing S] {ι : Type*} [Fintype ι]
    (R : ι → Type*) [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)]
    [∀ i, IsDiscreteValuationRing (R i)] [∀ i, Algebra S (R i)] (k : ι → ℕ) :
    ((Ideal.pi (fun i => IsLocalRing.maximalIdeal (R i) ^ k i)).restrictScalars S).cardQuot =
      ∏ i, Nat.card (IsLocalRing.ResidueField (R i)) ^ k i := by
  rw [cardQuot_pi_restrictScalars]
  apply Finset.prod_congr rfl
  intro i _
  rw [cardQuot_pow_of_prime]
  · rfl
  · exact fun h => IsDiscreteValuationRing.not_isField (R i)
      (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)

 
def integralCompletedIdeal {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule (PadicInt p) (completedMaximalOrder (K := K) p) :=
  (completedFractionalIdeal p J).comap (completedMaximalOrder (K := K) p).val.toLinearMap

lemma integralCompletedIdeal_eq_span {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) ≤ 1) :
    integralCompletedIdeal p J =
      (Ideal.span ({⟨idealLocalGenerator p J, integral_idealLocalGenerator p J hJ⟩} :
        Set (completedMaximalOrder (K := K) p))).restrictScalars (PadicInt p) := by
  ext x
  change (x : LocalAlgebra p K) ∈ completedFractionalIdeal p (J : FractionalIdeal (𝓞 K)⁰ K) ↔ _
  rw [idealLocalGenerator_spec]
  change _ ↔ x ∈ Ideal.span ({⟨idealLocalGenerator p J, integral_idealLocalGenerator p J hJ⟩} :
    Set (completedMaximalOrder (K := K) p))
  rw [Ideal.mem_span_singleton]
  constructor
  · intro hx
    obtain ⟨y,hy,hxy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    refine ⟨⟨y,hy⟩, ?_⟩
    apply Subtype.ext
    exact hxy.symm
  · rintro ⟨y,hy⟩
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨y,y.property,?_⟩
    exact (congrArg Subtype.val hy).symm

lemma map_principal_restrictScalars {S R T : Type*} [CommRing S] [CommRing R] [CommRing T]
    [Algebra S R] [Algebra S T] (E : R ≃ₐ[S] T) (x : R) :
    ((Ideal.span ({x} : Set R)).restrictScalars S).map E.toLinearMap =
      (Ideal.span ({E x} : Set T)).restrictScalars S := by
  ext y
  rw [Submodule.mem_map_equiv]
  change E.symm y ∈ Ideal.span ({x} : Set R) ↔ y ∈ Ideal.span ({E x} : Set T)
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton, map_dvd_iff_dvd_symm]
  rfl

 
def integralIdealValuations {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (T : ActualLocalModel p K)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) ≤ 1) : T.Index → ℕ :=
  fun i => (addVal (T.Ring i)
    (T.equiv ⟨idealLocalGenerator p J, integral_idealLocalGenerator p J hJ⟩ i)).toNat

lemma integralCompletedIdeal_model {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (T : ActualLocalModel p K)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) ≤ 1) :
    (integralCompletedIdeal p J).map T.equiv.toLinearMap =
      (Ideal.pi (fun i => IsLocalRing.maximalIdeal (T.Ring i) ^
        integralIdealValuations p T J hJ i)).restrictScalars (PadicInt p) := by
  rw [integralCompletedIdeal_eq_span p J hJ, map_principal_restrictScalars,
    product_dvr_principal_eq]
  · rfl
  · exact model_generator_components_ne_zero p T.equiv _ _

lemma integralCompletedIdeal_cardQuot {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (T : ActualLocalModel p K)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) ≤ 1) :
    (integralCompletedIdeal p J).cardQuot =
      ∏ i, p ^ (T.f i * integralIdealValuations p T J hJ i) := by
  rw [← cardQuot_map_equiv T.equiv.toLinearEquiv, integralCompletedIdeal_model p T J hJ,
    cardQuot_product_dvr_powers]
  apply Finset.prod_congr rfl
  intro i _
  rw [T.card_residue, pow_mul]

end PrimeDegreePackets


namespace PrimeDegreePackets
open NumberField
open scoped BigOperators Pointwise NumberField nonZeroDivisors ENNReal

 
def nonzeroIntegralIdealUnit {K : Type*} [Field K] [NumberField K]
    (J : {I : Ideal (𝓞 K) // I ≠ ⊥}) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (J.1 : FractionalIdeal (𝓞 K)⁰ K) (by simpa using J.2)

lemma nonzeroIntegralIdealUnit_le_one {K : Type*} [Field K] [NumberField K]
    (J : {I : Ideal (𝓞 K) // I ≠ ⊥}) :
    (nonzeroIntegralIdealUnit J : FractionalIdeal (𝓞 K)⁰ K) ≤ 1 :=
  FractionalIdeal.coeIdeal_le_one

lemma integralIdeal_subgroup_map {K : Type*} [Field K] [NumberField K]
    (J : Ideal (𝓞 K)) :
    ((J : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).toAddSubgroup =
      J.toAddSubgroup.map (algebraMap (𝓞 K) K).toAddMonoidHom := by
  ext x
  exact FractionalIdeal.mem_coeIdeal (𝓞 K)⁰

lemma fullLattice_ideal_relIndex {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : Module.finrank ℚ K = n) (J : {I : Ideal (𝓞 K) // I ≠ ⊥}) :
    (fractionalIdealFullLattice hn (nonzeroIntegralIdealUnit J)).carrier.toAddSubgroup.relIndex
      (fractionalIdealFullLattice hn 1).carrier.toAddSubgroup = Ideal.absNorm J.1 := by
  change ((J.1 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).toAddSubgroup.relIndex
    ((1 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).toAddSubgroup = _
  rw [← show ((⊤ : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 1 from by simp,
    integralIdeal_subgroup_map J.1, integralIdeal_subgroup_map ⊤,
    AddSubgroup.relIndex_map_map_of_injective _ _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]
  change J.1.toAddSubgroup.relIndex ⊤ = _
  rw [AddSubgroup.relIndex_top_right]
  rfl

lemma absNorm_smul_integral {K : Type*} [Field K] [NumberField K]
    (J : Ideal (𝓞 K)) {x : K} (hx : x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K)) :
    (Ideal.absNorm J : ℤ) • x ∈ (J : FractionalIdeal (𝓞 K)⁰ K) := by
  obtain ⟨a,rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 K)⁰).mp hx
  have h : (Ideal.absNorm J : 𝓞 K) * a ∈ J := J.mul_mem_right a (Ideal.absNorm_mem J)
  have H := FractionalIdeal.mem_coeIdeal_of_mem (P := K) (𝓞 K)⁰ h
  simpa only [map_mul, map_natCast, zsmul_eq_mul, Int.cast_natCast] using H

lemma completed_ideal_primePower_mem {K : Type*} [Field K] [NumberField K]
    (J : {I : Ideal (𝓞 K) // I ≠ ⊥}) (p : ℕ) [Fact p.Prime]
    {x : LocalAlgebra p K} (hx : x ∈ completedFractionalIdeal p (1 : FractionalIdeal (𝓞 K)⁰ K)) :
    (p : PadicInt p)^((Ideal.absNorm J.1).factorization p) • x ∈
      completedFractionalIdeal p (nonzeroIntegralIdealUnit J : FractionalIdeal (𝓞 K)⁰ K) := by
  apply completedLattice_primePower_mem
    (M := fractionalIdealFullLattice (n := Module.finrank ℚ K) rfl 1)
    (N := fractionalIdealFullLattice rfl (nonzeroIntegralIdealUnit J))
    (Ideal.absNorm J.1) (fun _ hx => absNorm_smul_integral J.1 hx) p _
    (ordCompl[p] (Ideal.absNorm J.1))
    (Nat.ordProj_mul_ordCompl_eq_self (Ideal.absNorm J.1) p).symm
    (Nat.coprime_ordCompl Fact.out (Ideal.absNorm_eq_zero_iff.not.mpr J.2)) hx

lemma completed_ideal_eq_off {K : Type*} [Field K] [NumberField K]
    (J : {I : Ideal (𝓞 K) // I ≠ ⊥}) (p : ℕ) [Fact p.Prime]
    (hp : ¬ p ∣ Ideal.absNorm J.1) :
    completedFractionalIdeal p (nonzeroIntegralIdealUnit J : FractionalIdeal (𝓞 K)⁰ K) =
      completedFractionalIdeal p (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  apply le_antisymm (completedFractionalIdeal_mono p (nonzeroIntegralIdealUnit_le_one J))
  intro x hx
  simpa [Nat.factorization_eq_zero_of_not_dvd hp] using completed_ideal_primePower_mem J p hx

lemma integralCompletedIdeal_relIndex {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (integralCompletedIdeal p J).cardQuot =
      (completedFractionalIdeal p (J : FractionalIdeal (𝓞 K)⁰ K)).toAddSubgroup.relIndex
        (completedFractionalIdeal p (1 : FractionalIdeal (𝓞 K)⁰ K)).toAddSubgroup := rfl

 
theorem integralIdeal_norm_eq_valuation_product {K : Type*} [Field K] [NumberField K]
    (J : {I : Ideal (𝓞 K) // I ≠ ⊥}) (S : Finset ℕ) [∀ p : S, Fact p.val.Prime]
    (hsupp : ∀ p, p.Prime → p ∣ Ideal.absNorm J.1 → p ∈ S)
    (T : ∀ p : S, ActualLocalModel p.val K) :
    Ideal.absNorm J.1 =
      ∏ p : S, ∏ i, p.val ^ ((T p).f i *
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
      exact completed_ideal_eq_off J p (fun hdiv => hnot ⟨⟨p,hsupp p hp hdiv⟩,rfl⟩))
  rw [fullLattice_ideal_relIndex] at H
  apply H.trans
  apply Finset.prod_congr rfl
  intro p _
  change (completedFractionalIdeal p.val (U : FractionalIdeal (𝓞 K)⁰ K)).toAddSubgroup.relIndex
    (completedFractionalIdeal p.val (1 : FractionalIdeal (𝓞 K)⁰ K)).toAddSubgroup = _
  rw [← integralCompletedIdeal_relIndex]
  exact integralCompletedIdeal_cardQuot p.val (T p) U (nonzeroIntegralIdealUnit_le_one J)

lemma completedFractionalIdeal_eq_of_integralCompletedIdeal_eq
    {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hI : (I : FractionalIdeal (𝓞 K)⁰ K) ≤ 1)
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) ≤ 1)
    (h : integralCompletedIdeal p I = integralCompletedIdeal p J) :
    completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) =
      completedFractionalIdeal p (J : FractionalIdeal (𝓞 K)⁰ K) := by
  ext x
  constructor
  · intro hx
    have hx' : x ∈ completedMaximalOrder (K := K) p := completedFractionalIdeal_mono p hI hx
    have H : (⟨x,hx'⟩ : completedMaximalOrder (K := K) p) ∈ integralCompletedIdeal p I := hx
    rw [h] at H
    exact H
  · intro hx
    have hx' : x ∈ completedMaximalOrder (K := K) p := completedFractionalIdeal_mono p hJ hx
    have H : (⟨x,hx'⟩ : completedMaximalOrder (K := K) p) ∈ integralCompletedIdeal p J := hx
    rw [← h] at H
    exact H

lemma integralIdeal_completions_eq_of_valuations_eq {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (T : ActualLocalModel p K)
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hI : (I : FractionalIdeal (𝓞 K)⁰ K) ≤ 1)
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) ≤ 1)
    (h : integralIdealValuations p T I hI = integralIdealValuations p T J hJ) :
    completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) =
      completedFractionalIdeal p (J : FractionalIdeal (𝓞 K)⁰ K) := by
  apply completedFractionalIdeal_eq_of_integralCompletedIdeal_eq p I J hI hJ
  apply Submodule.map_injective_of_injective (f := T.equiv.toLinearMap) T.equiv.injective
  rw [integralCompletedIdeal_model p T I hI, integralCompletedIdeal_model p T J hJ, h]

 
def primaryIntegralIdeals (K : Type*) [Field K] [NumberField K] (S : Finset ℕ) :=
  {J : {I : Ideal (𝓞 K) // I ≠ ⊥} // ∀ p, p.Prime → p ∣ Ideal.absNorm J.1 → p ∈ S}

def primaryIdealValuations {K : Type*} [Field K] [NumberField K]
    (S : Finset ℕ) [∀ p : S, Fact p.val.Prime] (T : ∀ p : S, ActualLocalModel p.val K)
    (J : primaryIntegralIdeals K S) : ∀ p : S, (T p).Index → ℕ :=
  fun p => integralIdealValuations p.val (T p) (nonzeroIntegralIdealUnit J.1)
    (nonzeroIntegralIdealUnit_le_one J.1)

 

theorem primaryIdealValuations_injective {K : Type*} [Field K] [NumberField K]
    (S : Finset ℕ) [∀ p : S, Fact p.val.Prime] (T : ∀ p : S, ActualLocalModel p.val K) :
    Function.Injective (primaryIdealValuations S T) := by
  intro I J h
  have H : (nonzeroIntegralIdealUnit I.1 : FractionalIdeal (𝓞 K)⁰ K) =
      (nonzeroIntegralIdealUnit J.1 : FractionalIdeal (𝓞 K)⁰ K) := by
    apply fractionalIdeal_eq_of_completions_eq
    intro p hp
    let : Fact p.Prime := ⟨hp⟩
    by_cases hs : p ∈ S
    · exact integralIdeal_completions_eq_of_valuations_eq p (T ⟨p,hs⟩) _ _ _ _ (congrFun h ⟨p,hs⟩)
    · rw [completed_ideal_eq_off I.1 p (fun hd => hs (I.2 p hp hd)),
        completed_ideal_eq_off J.1 p (fun hd => hs (J.2 p hp hd))]
  apply Subtype.ext
  apply Subtype.ext
  exact FractionalIdeal.coeIdeal_injective H

lemma localIdealWeight_eq_of_completion_eq {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime]
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (h : completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) =
      completedFractionalIdeal p (J : FractionalIdeal (𝓞 K)⁰ K)) :
    localIdealWeight M p I = localIdealWeight M p J := by
  exact localIdealWeight_eq_of_generator M p I (idealLocalGenerator p J)
    (h.trans (idealLocalGenerator_spec p J))

 
lemma primaryIdeal_actual_weight {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (J : primaryIntegralIdeals K (saturationIndex M).primeFactors) :
    globalIdealWeight M (nonzeroIntegralIdealUnit J.1) =
      actualTupleWeight M (primaryIdealValuations (saturationIndex M).primeFactors
        (fun p => actualLocalModel p.val K) J) := by
  apply Finset.prod_congr rfl
  intro p _
  exact localIdealWeight_eq_model_shell M hn p.val (actualLocalModel p.val K).Ring
    (actualLocalModel p.val K).equiv (actualLocalModel p.val K).continuous_equiv
    (actualLocalModel p.val K).continuous_symm _ (nonzeroIntegralIdealUnit_le_one J.1)

lemma primaryIdeal_actual_norm {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (J : primaryIntegralIdeals K (saturationIndex M).primeFactors) :
    (Ideal.absNorm J.1.1 : ℝ≥0∞) =
      actualTupleNorm M (primaryIdealValuations (saturationIndex M).primeFactors
        (fun p => actualLocalModel p.val K) J) := by
  rw [integralIdeal_norm_eq_valuation_product J.1 _ J.2 (fun p => actualLocalModel p.val K)]
  simp only [Nat.cast_prod, Nat.cast_pow, actualTupleNorm, shellNorm]
  apply Finset.prod_congr rfl
  intro p _
  apply Finset.prod_congr rfl
  intro i _
  rw [(actualLocalModel p.val K).card_residue, Nat.cast_pow, pow_mul]
  rfl

 

theorem primaryIdeal_reciprocal_sum_le {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) :
    (∑' J : primaryIntegralIdeals K (saturationIndex M).primeFactors,
      globalIdealWeight M (nonzeroIntegralIdealUnit J.1) / (Ideal.absNorm J.1.1 : ℝ≥0∞)) ≤
      (saturationIndex M : ℝ≥0∞)⁻¹ * actualLocalZ M := by
  simp_rw [primaryIdeal_actual_weight M hn, primaryIdeal_actual_norm M]
  apply (ENNReal.tsum_comp_le_tsum_of_injective
    (primaryIdealValuations_injective (saturationIndex M).primeFactors
      (fun p => actualLocalModel p.val K))
    (fun k => actualTupleWeight M k / actualTupleNorm M k)).trans
  exact (actual_tuple_weight_sum M hn).le

 

theorem primaryIdeal_moment_le {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (hn0 : 0 < n)
    (ε : ℝ) (hε : 0 < ε) :
    (∑' J : primaryIntegralIdeals K (saturationIndex M).primeFactors,
      globalIdealWeight M (nonzeroIntegralIdealUnit J.1) *
        (Ideal.absNorm J.1.1 : ℝ≥0∞) ^ (1 / (2 * (n : ℝ)) - 1)) ≤
      (saturationIndex M : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (localProductConstant n ε hε * (saturationIndex M : ℝ) ^ ε) := by
  simp_rw [primaryIdeal_actual_weight M hn, primaryIdeal_actual_norm M]
  apply (ENNReal.tsum_comp_le_tsum_of_injective
    (primaryIdealValuations_injective (saturationIndex M).primeFactors
      (fun p => actualLocalModel p.val K))
    (fun k => actualTupleWeight M k * actualTupleNorm M k ^ (1 / (2 * (n : ℝ)) - 1))).trans
  exact actual_tuple_weight_moment M hn hn0 ε hε

end PrimeDegreePackets
end
end

end OAI
