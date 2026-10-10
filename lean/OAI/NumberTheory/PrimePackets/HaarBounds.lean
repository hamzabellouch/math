import Mathlib

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
namespace PrimeDegreePackets

 

theorem haar_kernel_eq_inv_card {A B : Type*} [AddGroup A] [AddGroup B]
    [MeasurableSpace A] [MeasurableAdd A]
    (μ : Measure A) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (f : A →+ B) [Finite f.range] (hf : MeasurableSet (f.ker : Set A)) :
    μ (f.ker : Set A) = (Nat.card f.range : ℝ≥0∞)⁻¹ := by
  have hc : (Nat.card f.range : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  rw [← one_div (Nat.card f.range : ℝ≥0∞)]
  apply (ENNReal.eq_div_iff hc (by simp)).mpr
  simpa only [AddSubgroup.index_ker, measure_univ] using
    f.ker.index_mul_measure hf μ

 
theorem haar_kernel_le_inv_addOrderOf {A B : Type*} [AddGroup A] [AddGroup B]
    [MeasurableSpace A] [MeasurableAdd A]
    (μ : Measure A) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (f : A →+ B) [Finite f.range] (hf : MeasurableSet (f.ker : Set A)) (a : A) :
    μ (f.ker : Set A) ≤ (addOrderOf (f a) : ℝ≥0∞)⁻¹ := by
  rw [haar_kernel_eq_inv_card μ f hf, ENNReal.inv_le_inv]
  have h : addOrderOf (f a) ≤ Nat.card f.range := by
    have hx := @addOrderOf_le_card f.range _ (f.rangeRestrict a) _
    rwa [← addOrderOf_injective f.range.subtype Subtype.val_injective] at hx
  exact_mod_cast h

 

theorem haar_zero_fiber_le_of_order {A B : Type*} [AddGroup A] [AddGroup B]
    [MeasurableSpace A] [MeasurableAdd A]
    (μ : Measure A) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (f : A →+ B) [Finite f.range] (hf : MeasurableSet (f.ker : Set A))
    (m : ℕ) (a : A) (ha : m ≤ addOrderOf (f a)) :
    μ {x | f x = 0} ≤ (m : ℝ≥0∞)⁻¹ := by
  change μ (f.ker : Set A) ≤ _
  apply (haar_kernel_le_inv_addOrderOf μ f hf a).trans
  rw [ENNReal.inv_le_inv]
  exact_mod_cast ha

end PrimeDegreePackets

open IsDiscreteValuationRing IsLocalRing
namespace PrimeDegreePackets

lemma mem_maximalIdeal_pow_iff_addVal {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (x : R) (k : ℕ) :
    x ∈ IsLocalRing.maximalIdeal R ^ k ↔ (k : ℕ∞) ≤ addVal R x := by
  obtain ⟨π, hπ⟩ := exists_irreducible R
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← addVal_le_iff_dvd, hπ.addVal_pow]

 

lemma addVal_scalar_unit_mul_pow (p : ℕ) [Fact p.Prime]
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra (PadicInt p) R] (e : ℕ)
    (he : addVal R (algebraMap (PadicInt p) R p) = e)
    (u : (PadicInt p)ˣ) (a : ℕ) :
    addVal R (algebraMap (PadicInt p) R ((u : PadicInt p) * (p : PadicInt p) ^ a)) =
      (a * e : ℕ) := by
  rw [map_mul, map_pow, addVal_mul, addVal_pow, he,
    addVal_eq_zero_iff.mpr (u.isUnit.map (algebraMap (PadicInt p) R)), zero_add]
  simp [nsmul_eq_mul]

 

theorem scalar_preimage_maximalIdeal_pow (p : ℕ) [Fact p.Prime]
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra (PadicInt p) R] (e : ℕ) (he0 : 0 < e)
    (he : addVal R (algebraMap (PadicInt p) R p) = e) (k : ℕ) :
    Ideal.comap (algebraMap (PadicInt p) R) (IsLocalRing.maximalIdeal R ^ k) =
      Ideal.span {(p : PadicInt p) ^ (k ⌈/⌉ e)} := by
  ext x
  change algebraMap (PadicInt p) R x ∈ IsLocalRing.maximalIdeal R ^ k ↔ _
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨a, u, rfl⟩ := eq_unit_mul_pow_irreducible hx (PadicInt.irreducible_p (p := p))
  rw [mem_maximalIdeal_pow_iff_addVal, addVal_scalar_unit_mul_pow p e he,
    Ideal.mem_span_singleton, ← addVal_le_iff_dvd,
    (PadicInt.irreducible_p (p := p)).addVal_pow,
    addVal_def' u (PadicInt.irreducible_p (p := p)) a,
    ENat.natCast_le_natCast, ENat.natCast_le_natCast]
  simpa only [Nat.mul_comm] using (ceilDiv_le_iff_le_mul he0).symm

 

lemma natCast_mem_maximalIdeal_pow_iff (p : ℕ) [Fact p.Prime]
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra (PadicInt p) R] (e : ℕ) (he0 : 0 < e)
    (he : addVal R (algebraMap (PadicInt p) R p) = e) (k m : ℕ) :
    (m : R) ∈ IsLocalRing.maximalIdeal R ^ k ↔ p ^ (k ⌈/⌉ e) ∣ m := by
  rw [← map_natCast (algebraMap (PadicInt p) R) m]
  change (m : PadicInt p) ∈ Ideal.comap (algebraMap (PadicInt p) R)
    (IsLocalRing.maximalIdeal R ^ k) ↔ _
  rw [scalar_preimage_maximalIdeal_pow p e he0 he k,
    ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_natCast]
  exact ZMod.natCast_eq_zero_iff _ _

 

theorem addOrderOf_quotient_unit (p : ℕ) [Fact p.Prime]
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra (PadicInt p) R] (e : ℕ) (he0 : 0 < e)
    (he : addVal R (algebraMap (PadicInt p) R p) = e) (k : ℕ)
    (u : R) (hu : IsUnit u) :
    addOrderOf (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ k) u) =
      p ^ (k ⌈/⌉ e) := by
  let q := Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ k)
  have hq : IsUnit (q u) := hu.map q
  have hdiv : ∀ m : ℕ, addOrderOf (q u) ∣ m ↔ p ^ (k ⌈/⌉ e) ∣ m := by
    intro m
    rw [addOrderOf_dvd_iff_nsmul_eq_zero, nsmul_eq_mul, hq.mul_left_eq_zero]
    rw [← map_natCast q, Ideal.Quotient.eq_zero_iff_mem]
    exact natCast_mem_maximalIdeal_pow_iff p e he0 he k m
  exact Nat.dvd_antisymm ((hdiv _).mpr dvd_rfl) ((hdiv _).mp dvd_rfl)

 

lemma exists_unit_of_span_eq_top {R : Type*} [CommRing R]
    [IsLocalRing R] (S : Set R) (hS : Ideal.span S = ⊤) :
    ∃ x ∈ S, IsUnit x := by
  by_contra h
  push Not at h
  have hs : S ⊆ IsLocalRing.maximalIdeal R := by
    intro x hx
    exact h x hx
  have heq : IsLocalRing.maximalIdeal R = ⊤ := top_le_iff.mp (hS ▸ Ideal.span_le.mpr hs)
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top heq

end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing IsLocalRing
open scoped ENNReal

 

theorem haar_dvr_projection_tail (p : ℕ) [Fact p.Prime]
    {R A : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra (PadicInt p) R] [Finite (IsLocalRing.ResidueField R)]
    [AddGroup A] [MeasurableSpace A] [MeasurableAdd A]
    (μ : Measure A) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (φ : A →+ R) (hsat : Ideal.span (Set.range φ) = ⊤)
    (e : ℕ) (he0 : 0 < e)
    (he : addVal R (algebraMap (PadicInt p) R p) = e)
    (k : ℕ) (hM : MeasurableSet {x | φ x ∈ IsLocalRing.maximalIdeal R ^ k}) :
    μ {x | (k : ℕ∞) ≤ addVal R (φ x)} ≤ ((p : ℝ≥0∞) ^ (k ⌈/⌉ e))⁻¹ := by
  have : Finite (R ⧸ IsLocalRing.maximalIdeal R ^ k) :=
    IsLocalRing.finite_quotient_iff.mpr ⟨k, le_rfl⟩
  let f : A →+ R ⧸ IsLocalRing.maximalIdeal R ^ k :=
    (Ideal.Quotient.mk _).toAddMonoidHom.comp φ
  have hset : (f.ker : Set A) = {x | (k : ℕ∞) ≤ addVal R (φ x)} := by
    ext x
    change Ideal.Quotient.mk _ (φ x) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_maximalIdeal_pow_iff_addVal]
    rfl
  have hf : MeasurableSet (f.ker : Set A) := by
    convert hM using 1
    ext x
    exact Ideal.Quotient.eq_zero_iff_mem
  obtain ⟨u, ⟨a, rfl⟩, hu⟩ := exists_unit_of_span_eq_top (Set.range φ) hsat
  have horder : addOrderOf (f a) = p ^ (k ⌈/⌉ e) :=
    addOrderOf_quotient_unit p e he0 he k (φ a) hu
  have ht := haar_kernel_le_inv_addOrderOf μ f hf a
  rwa [horder, Nat.cast_pow, hset] at ht

 

theorem haar_natVal_projection_tail (p : ℕ) [Fact p.Prime]
    {R A : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra (PadicInt p) R] [Finite (IsLocalRing.ResidueField R)]
    [AddGroup A] [MeasurableSpace A] [MeasurableAdd A]
    (μ : Measure A) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (φ : A →+ R) (hsat : Ideal.span (Set.range φ) = ⊤)
    (e : ℕ) (he0 : 0 < e)
    (he : addVal R (algebraMap (PadicInt p) R p) = e)
    (k : ℕ) (hM : MeasurableSet {x | φ x ∈ IsLocalRing.maximalIdeal R ^ k}) :
    μ {x | k ≤ (addVal R (φ x)).toNat} ≤ ((p : ℝ≥0∞) ^ (k ⌈/⌉ e))⁻¹ := by
  apply (measure_mono ?_).trans (haar_dvr_projection_tail p μ φ hsat e he0 he k hM)
  intro x hx
  exact (ENat.natCast_le_natCast.mpr hx).trans (ENat.natCast_toNat_le_self _)

end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing IsLocalRing
open scoped ENNReal

section CompactDVR
variable {R A : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]
    [TopologicalSpace A] [MeasurableSpace A] [OpensMeasurableSpace A]

lemma measurableSet_dvr_tail {φ : A → R} (hφ : Continuous φ) (k : ℕ) :
    MeasurableSet {x | (k : ℕ∞) ≤ addVal R (φ x)} := by
  have heq : {x | (k : ℕ∞) ≤ addVal R (φ x)} = φ ⁻¹' ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R) := by
    ext x
    exact (mem_maximalIdeal_pow_iff_addVal _ _).symm
  rw [heq]
  exact ((isOpen_maximalIdeal_pow R k).preimage hφ).measurableSet

lemma measurable_dvr_val {φ : A → R} (hφ : Continuous φ) :
    Measurable (fun x => addVal R (φ x)) := by
  apply ENat.measurable_iff.mpr
  intro k
  have heq : (fun x => addVal R (φ x)) ⁻¹' {(k : ℕ∞)} =
      {x | (k : ℕ∞) ≤ addVal R (φ x)} \ {x | ((k + 1 : ℕ) : ℕ∞) ≤ addVal R (φ x)} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, Set.mem_sdiff, mem_ofPred_eq]
    induction addVal R (φ x) using ENat.recTopCoe with
    | top => simp
    | coe v => simp only [ENat.natCast_inj, ENat.natCast_le_natCast]; omega
  rw [heq]
  exact (measurableSet_dvr_tail hφ k).diff (measurableSet_dvr_tail hφ (k + 1))

lemma measurable_dvr_natVal {φ : A → R} (hφ : Continuous φ) :
    Measurable (fun x => (addVal R (φ x)).toNat) :=
  (Measurable.of_discrete : Measurable ENat.toNat).comp (measurable_dvr_val hφ)

end CompactDVR

 

theorem haar_dvr_zero_fiber (p : ℕ) [Fact p.Prime]
    {R A : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra (PadicInt p) R] [Finite (IsLocalRing.ResidueField R)]
    [AddGroup A] [MeasurableSpace A] [MeasurableAdd A]
    (μ : Measure A) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (φ : A →+ R) (hsat : Ideal.span (Set.range φ) = ⊤)
    (e : ℕ) (he0 : 0 < e)
    (he : addVal R (algebraMap (PadicInt p) R p) = e)
    (hM : ∀ k : ℕ, MeasurableSet {x | φ x ∈ IsLocalRing.maximalIdeal R ^ k}) :
    μ {x | φ x = 0} = 0 := by
  have hp : (1 : ℝ≥0∞) < p := by
    exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlim := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.inv_lt_one.mpr hp)
  apply le_antisymm _ zero_le
  apply ge_of_tendsto' hlim
  intro a
  calc
    μ {x | φ x = 0} ≤ μ {x | ((e * a : ℕ) : ℕ∞) ≤ addVal R (φ x)} := by
      apply measure_mono
      intro x hx
      simp only [mem_ofPred_eq] at hx ⊢
      rw [hx, addVal_zero]
      exact le_top
    _ ≤ ((p : ℝ≥0∞) ^ ((e * a) ⌈/⌉ e))⁻¹ :=
      haar_dvr_projection_tail p μ φ hsat e he0 he (e * a) (hM _)
    _ = (p : ℝ≥0∞)⁻¹ ^ a := by
      rw [← smul_eq_mul, smul_ceilDiv he0, ENNReal.inv_pow]

end PrimeDegreePackets

open scoped ENNReal BigOperators
namespace PrimeDegreePackets

 
theorem lintegral_pow_le_of_nat_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (J : Ω → ℕ) (hJ : Measurable J)
    (r p c : ℝ≥0∞) (htail : ∀ a : ℕ, 1 ≤ a → μ {ω | a ≤ J ω} ≤ c / p ^ a) :
    (∫⁻ ω, r ^ J ω ∂μ) ≤ 1 + c * (r / p) * (1 - r / p)⁻¹ := by
  rw [← lintegral_map (Measurable.of_discrete : Measurable (fun a : ℕ => r ^ a)) hJ,
    lintegral_countable', tsum_eq_zero_add' ENNReal.summable]
  simp only [pow_zero, one_mul]
  apply add_le_add
  · exact prob_le_one
  · calc
      (∑' a : ℕ, r ^ (a + 1) * (Measure.map J μ) {a + 1}) ≤
          ∑' a : ℕ, c * (r / p) ^ (a + 1) := by
        apply ENNReal.tsum_le_tsum
        intro a
        rw [Measure.map_apply hJ (measurableSet_singleton _)]
        have hsubset : J ⁻¹' {a + 1} ⊆ {ω | a + 1 ≤ J ω} := by
          intro ω hω
          exact le_of_eq (Set.mem_singleton_iff.mp hω).symm
        calc
          r ^ (a + 1) * μ (J ⁻¹' {a + 1}) ≤ r ^ (a + 1) * (c / p ^ (a + 1)) :=
            mul_le_mul_right ((measure_mono hsubset).trans (htail (a + 1) (by omega))) _
          _ = c * (r / p) ^ (a + 1) := by simp only [div_eq_mul_inv, mul_pow, ENNReal.inv_pow]; ac_rfl
      _ = c * (r / p) * (1 - r / p)⁻¹ := by
        simp_rw [pow_succ, ← mul_assoc, mul_right_comm c]
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

 
theorem sqrt_geometric_factor_le {p : ℝ} (hp : 2 ≤ p) :
    (Real.sqrt p / p) * (1 - Real.sqrt p / p)⁻¹ ≤ 4 / Real.sqrt p := by
  have hp0 : 0 < p := by linarith
  have hs0 : 0 < Real.sqrt p := Real.sqrt_pos_of_pos hp0
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
  have hs1 : 1 < Real.sqrt p := by
    by_contra h
    have hh : Real.sqrt p ≤ 1 := le_of_not_gt h
    nlinarith [sq_nonneg (Real.sqrt p - 1)]
  have hs43 : (4 / 3 : ℝ) ≤ Real.sqrt p := by
    by_contra h
    have hh : Real.sqrt p < 4 / 3 := lt_of_not_ge h
    nlinarith [mul_nonneg hs0.le (by linarith : 0 ≤ 4 / 3 - Real.sqrt p)]
  have hsp : Real.sqrt p < p := by nlinarith
  have hden : 0 < 1 - Real.sqrt p / p := sub_pos.mpr ((div_lt_one hp0).mpr hsp)
  apply (le_div_iff₀ hs0).mpr
  rw [mul_assoc, inv_mul_eq_div, ← mul_div_assoc]
  apply (div_le_iff₀ hden).mpr
  field_simp
  nlinarith

 

theorem local_sqrt_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (J : Ω → ℕ) (hJ : Measurable J)
    (n : ℕ) (p : ℝ) (hp : 2 ≤ p)
    (htail : ∀ a : ℕ, 1 ≤ a → μ {ω | a ≤ J ω} ≤ (n : ℝ≥0∞) / (ENNReal.ofReal p) ^ a) :
    (∫⁻ ω, (ENNReal.ofReal (Real.sqrt p)) ^ J ω ∂μ) ≤
      1 + (n : ℝ≥0∞) * ENNReal.ofReal (4 / Real.sqrt p) := by
  have hp0 : 0 < p := by linarith
  have hs0 : 0 < Real.sqrt p := Real.sqrt_pos_of_pos hp0
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
  have hs1 : 1 < Real.sqrt p := by
    by_contra h
    have hh : Real.sqrt p ≤ 1 := le_of_not_gt h
    nlinarith [sq_nonneg (Real.sqrt p - 1)]
  have hsp : Real.sqrt p < p := by nlinarith
  have hden : 0 < 1 - Real.sqrt p / p := sub_pos.mpr ((div_lt_one hp0).mpr hsp)
  have hratio : 0 ≤ Real.sqrt p / p := div_nonneg hs0.le hp0.le
  apply (lintegral_pow_le_of_nat_tail μ J hJ (ENNReal.ofReal (Real.sqrt p))
    (ENNReal.ofReal p) n htail).trans
  apply add_le_add_right
  rw [mul_assoc]
  apply mul_le_mul_right
  rw [← ENNReal.ofReal_div_of_pos hp0,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hratio,
    ← ENNReal.ofReal_inv_of_pos hden, ← ENNReal.ofReal_mul hratio]
  exact ENNReal.ofReal_le_ofReal (sqrt_geometric_factor_le hp)

 
def ramifiedMaximum {ι : Type*} [Fintype ι] (e v : ι → ℕ) : ℕ :=
  Finset.univ.sup fun i => v i ⌈/⌉ e i

lemma ramifiedMaximum_measurable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (e : ι → ℕ) (v : ι → Ω → ℕ) (hv : ∀ i, Measurable (v i)) :
    Measurable (fun ω => ramifiedMaximum e (fun i => v i ω)) := by
  exact (Measurable.of_discrete : Measurable (ramifiedMaximum e)).comp
    (Measurable.of_eval hv)

lemma ceilDiv_ramification_succ (e a : ℕ) (he : 0 < e) :
    (e * a + 1) ⌈/⌉ e = a + 1 := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  have heq : e * a + 1 + e - 1 = (a + 1) * e := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm a e]
    omega
  rw [heq, Nat.mul_div_left _ he]

 
theorem ramifiedMaximum_tail {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (e : ι → ℕ) (he : ∀ i, 0 < e i) (v : ι → Ω → ℕ)
    (p : ℝ≥0∞)
    (htail : ∀ i k, 1 ≤ k → μ {ω | k ≤ v i ω} ≤ p⁻¹ ^ (k ⌈/⌉ e i))
    (a : ℕ) (ha : 1 ≤ a) :
    μ {ω | a ≤ ramifiedMaximum e (fun i => v i ω)} ≤
      (Fintype.card ι : ℝ≥0∞) / p ^ a := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  have hsubset : {ω | a + 1 ≤ ramifiedMaximum e (fun i => v i ω)} ⊆
      ⋃ i, {ω | e i * a + 1 ≤ v i ω} := by
    intro ω hω
    obtain ⟨i, -, hi⟩ := (Finset.le_sup_iff (by omega : 0 < a + 1)).mp hω
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    change e i * a + 1 ≤ v i ω
    by_contra hn
    have hvle : v i ω ≤ e i * a := by omega
    have hh := (ceilDiv_le_iff_le_mul (he i)).mpr hvle
    change a + 1 ≤ v i ω ⌈/⌉ e i at hi
    omega
  calc
    _ ≤ μ (⋃ i, {ω | e i * a + 1 ≤ v i ω}) := measure_mono hsubset
    _ ≤ ∑ i, μ {ω | e i * a + 1 ≤ v i ω} := measure_iUnion_fintype_le μ _
    _ ≤ ∑ _i : ι, p⁻¹ ^ (a + 1) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [ceilDiv_ramification_succ _ _ (he i)] using
        htail i (e i * a + 1) (by omega)
    _ = (Fintype.card ι : ℝ≥0∞) / p ^ (a + 1) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        div_eq_mul_inv, ENNReal.inv_pow]

 
theorem normExponent_le_degree_mul_maximum {ι : Type*} [Fintype ι]
    (e f v : ι → ℕ) (he : ∀ i, 0 < e i) :
    ∑ i, f i * v i ≤ (∑ i, f i * e i) * ramifiedMaximum e v := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [mul_assoc]
  apply Nat.mul_le_mul_left
  calc
    v i ≤ e i * (v i ⌈/⌉ e i) := le_smul_ceilDiv (he i)
    _ ≤ e i * ramifiedMaximum e v :=
      Nat.mul_le_mul_left _ (Finset.le_sup (f := fun j => v j ⌈/⌉ e j) (Finset.mem_univ i))

lemma card_le_localDegree {ι : Type*} [Fintype ι]
    (e f : ι → ℕ) (he : ∀ i, 0 < e i) (hf : ∀ i, 0 < f i) :
    Fintype.card ι ≤ ∑ i, f i * e i := by
  calc
    Fintype.card ι = ∑ _i : ι, 1 := by simp
    _ ≤ ∑ i, f i * e i := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.ne_of_gt (hf i)) (Nat.ne_of_gt (he i)))

 

theorem local_norm_moment_of_valuation_tails {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (e f : ι → ℕ) (he : ∀ i, 0 < e i) (hf : ∀ i, 0 < f i)
    (n : ℕ) (hn : 0 < n) (hdegree : ∑ i, f i * e i = n)
    (v : ι → Ω → ℕ) (hv : ∀ i, Measurable (v i)) (p : ℝ) (hp : 2 ≤ p)
    (htail : ∀ i k, 1 ≤ k → μ {ω | k ≤ v i ω} ≤
      (ENNReal.ofReal p)⁻¹ ^ (k ⌈/⌉ e i)) :
    (∫⁻ ω, ((ENNReal.ofReal p) ^ (∑ i, f i * v i ω)) ^ (1 / (2 * (n : ℝ))) ∂μ) ≤
      1 + (n : ℝ≥0∞) * ENNReal.ofReal (4 / Real.sqrt p) := by
  have hp0 : 0 < p := by linarith
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hs : 0 ≤ (1 / (2 * (n : ℝ))) := by positivity
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)
  let J : Ω → ℕ := fun ω => ramifiedMaximum e (fun i => v i ω)
  have hJ : Measurable J := ramifiedMaximum_measurable e v hv
  have hc : Fintype.card ι ≤ n := hdegree ▸ card_le_localDegree e f he hf
  have hJtail : ∀ a : ℕ, 1 ≤ a → μ {ω | a ≤ J ω} ≤
      (n : ℝ≥0∞) / (ENNReal.ofReal p) ^ a := by
    intro a ha
    apply (ramifiedMaximum_tail μ e he v (ENNReal.ofReal p) htail a ha).trans
    exact ENNReal.div_le_div (by exact_mod_cast hc) le_rfl
  calc
    _ ≤ ∫⁻ ω, (ENNReal.ofReal (Real.sqrt p)) ^ J ω ∂μ := by
      apply lintegral_mono
      intro ω
      have hnorm : ∑ i, f i * v i ω ≤ n * J ω := by
        simpa only [hdegree] using normExponent_le_degree_mul_maximum e f (fun i => v i ω) he
      calc
        _ ≤ ((ENNReal.ofReal p) ^ (n * J ω)) ^ (1 / (2 * (n : ℝ))) :=
          ENNReal.rpow_le_rpow (pow_le_pow_right₀ hp1 hnorm) hs
        _ = (ENNReal.ofReal (Real.sqrt p)) ^ J ω := by
          rw [← ENNReal.rpow_natCast_mul]
          have hexp : ((n * J ω : ℕ) : ℝ) * (1 / (2 * (n : ℝ))) = (1 / 2 : ℝ) * J ω := by
            push_cast
            field_simp
          rw [hexp, ENNReal.rpow_mul_natCast, ENNReal.ofReal_rpow_of_pos hp0,
            ← Real.sqrt_eq_rpow]
    _ ≤ _ := local_sqrt_moment μ J hJ n p hp hJtail

end PrimeDegreePackets
end
end

end OAI
