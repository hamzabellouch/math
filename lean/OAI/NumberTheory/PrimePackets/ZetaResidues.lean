import Mathlib
import OAI.NumberTheory.PrimePackets.IntervalGeometry

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
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
namespace PrimeDegreePackets

 

def realDedekindZeta (K : Type*) [Field K] [NumberField K] (s : ℝ) : ℝ :=
  (NumberField.dedekindZeta K (s : ℂ)).re

 

lemma tendsto_residue_from_right (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun h : ℝ => h * realDedekindZeta K (1 + h)) (𝓝[>] 0)
      (𝓝 (NumberField.dedekindZeta_residue K)) := by
  have hshift : Tendsto (fun h : ℝ => 1 + h) (𝓝[>] 0) (𝓝[>] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (tendsto_const_nhds.add (tendsto_id.mono_left inf_le_left) :
        Tendsto (fun h : ℝ => 1 + h) (𝓝[>] 0) (𝓝 (1 + 0)))
    · filter_upwards [self_mem_nhdsWithin] with h hh
      simpa using hh
  have H := (Complex.continuous_re.tendsto _).comp
    ((NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K).comp hshift)
  simpa [Function.comp_def, realDedekindZeta, Complex.mul_re] using H

lemma fixed_field_residue_comparison (K : Type*) [Field K] [NumberField K] :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      NumberField.dedekindZeta_residue K / 2 ≤ h * realDedekindZeta K (1 + h) ∧
      h * realDedekindZeta K (1 + h) ≤ 2 * NumberField.dedekindZeta_residue K := by
  have hk := NumberField.dedekindZeta_residue_pos K
  have ht := tendsto_residue_from_right K
  filter_upwards [ht.eventually_const_lt (by linarith : NumberField.dedekindZeta_residue K / 2 <
      NumberField.dedekindZeta_residue K),
    ht.eventually_lt_const (by linarith : NumberField.dedekindZeta_residue K <
      2 * NumberField.dedekindZeta_residue K)] with h hlo hhi
  exact ⟨hlo.le, hhi.le⟩

 

theorem finite_family_residue_comparison {α : Type*} [Finite α]
    (K : α → Type*) [∀ i, Field (K i)] [∀ i, NumberField (K i)] :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ i,
      NumberField.dedekindZeta_residue (K i) / 2 ≤ h * realDedekindZeta (K i) (1 + h) ∧
      h * realDedekindZeta (K i) (1 + h) ≤ 2 * NumberField.dedekindZeta_residue (K i) := by
  exact Filter.eventually_all.mpr (fun i => fixed_field_residue_comparison (K i))

 
theorem finite_family_residue_reciprocal_bound {α : Type*} [Finite α]
    (K : α → Type*) [∀ i, Field (K i)] [∀ i, NumberField (K i)] :
    ∃ C : ℝ, 0 < C ∧ ∀ i, (NumberField.dedekindZeta_residue (K i))⁻¹ ≤ C := by
  classical
  let := Fintype.ofFinite α
  refine ⟨1 + ∑ i, (NumberField.dedekindZeta_residue (K i))⁻¹, ?_, ?_⟩
  · have : 0 ≤ ∑ i, (NumberField.dedekindZeta_residue (K i))⁻¹ := by
      exact Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (NumberField.dedekindZeta_residue_pos (K i)).le)
    linarith
  · intro i
    have H := Finset.single_le_sum (fun j _ =>
      inv_nonneg.mpr (NumberField.dedekindZeta_residue_pos (K j)).le) (Finset.mem_univ i)
    linarith

 
lemma dedekindZeta_algEquiv {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] (e : K ≃ₐ[ℚ] L) (s : ℂ) :
    NumberField.dedekindZeta K s = NumberField.dedekindZeta L s := by
  let f : 𝓞 K ≃+* 𝓞 L := (e.restrictScalars ℤ).mapIntegralClosure.toRingEquiv
  have hn (I : Ideal (𝓞 K)) : Ideal.absNorm I = Ideal.absNorm (I.map f) := by
    exact Nat.card_congr (Ideal.quotientEquiv I (I.map f) f rfl).toEquiv
  have hc (n : ℕ) : Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} =
      Nat.card {I : Ideal (𝓞 L) // Ideal.absNorm I = n} := by
    apply Nat.card_congr
    exact f.idealComapOrderIso.symm.toEquiv.subtypeEquiv (fun I => by
      change Ideal.absNorm I = n ↔ Ideal.absNorm (I.map f) = n
      rw [hn])
  simp only [NumberField.dedekindZeta, hc]

lemma dedekindZeta_residue_algEquiv {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] (e : K ≃ₐ[ℚ] L) :
    NumberField.dedekindZeta_residue K = NumberField.dedekindZeta_residue L := by
  apply tendsto_nhds_unique (tendsto_residue_from_right K)
  simpa only [realDedekindZeta, dedekindZeta_algEquiv e] using tendsto_residue_from_right L

 
abbrev BoundedRealFields (N : ℕ) :=
  {K : {F : IntermediateField ℚ ℝ // FiniteDimensional ℚ F} //
    letI : NumberField K := @NumberField.mk _ _ inferInstance K.prop
    |NumberField.discr K| ≤ N}

instance boundedRealFields_numberField (N : ℕ) (K : BoundedRealFields N) :
    NumberField K.val := @NumberField.mk _ _ inferInstance K.val.prop

instance boundedRealFields_finite (N : ℕ) : Finite (BoundedRealFields N) :=
  (NumberField.finite_of_discr_bdd ℝ N).to_subtype

 

theorem bounded_discr_residue_data (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (K : BoundedRealFields N),
        (NumberField.dedekindZeta_residue K.val)⁻¹ ≤ C ∧
        ∀ h : ℝ, 0 < h → h < δ →
          NumberField.dedekindZeta_residue K.val / 2 ≤
            h * realDedekindZeta K.val (1+h) ∧
          h * realDedekindZeta K.val (1+h) ≤
            2 * NumberField.dedekindZeta_residue K.val := by
  obtain ⟨C,hC,HC⟩ := finite_family_residue_reciprocal_bound
    (fun K : BoundedRealFields N => K.val)
  have H := finite_family_residue_comparison (fun K : BoundedRealFields N => K.val)
  obtain ⟨δ,hδ,Hδ⟩ := Metric.mem_nhdsWithin_iff.mp H
  refine ⟨C,hC,δ,hδ,fun K => ⟨HC K,fun h hh hhδ => ?_⟩⟩
  apply Hδ
  exact ⟨by simpa [Real.dist_eq,abs_of_pos hh] using hhδ,hh⟩

 

theorem bounded_discr_residue_comparison (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (K : Type*) [Field K] [NumberField K],
        (K →+* ℝ) → |NumberField.discr K| ≤ N →
        (NumberField.dedekindZeta_residue K)⁻¹ ≤ C ∧
        ∀ h : ℝ, 0 < h → h < δ →
          NumberField.dedekindZeta_residue K / 2 ≤
            h * realDedekindZeta K (1+h) ∧
          h * realDedekindZeta K (1+h) ≤
            2 * NumberField.dedekindZeta_residue K := by
  obtain ⟨C,hC,δ,hδ,H⟩ := bounded_discr_residue_data N
  refine ⟨C,hC,δ,hδ,?_⟩
  intro K _ _ σ hD
  let f := σ.toRatAlgHom
  let F := f.fieldRange
  let e : K ≃ₐ[ℚ] F := f.equivFieldRange
  let : FiniteDimensional ℚ F := e.toLinearEquiv.finiteDimensional
  let : NumberField F := @NumberField.mk F _ inferInstance inferInstance
  have hd : |NumberField.discr F| ≤ N := by
    rw [← NumberField.discr_eq_discr_of_algEquiv K e]
    exact hD
  let J : BoundedRealFields N := ⟨⟨F,inferInstance⟩,hd⟩
  have HE := H J
  change (NumberField.dedekindZeta_residue F)⁻¹ ≤ C ∧
    ∀ h : ℝ, 0 < h → h < δ →
      NumberField.dedekindZeta_residue F / 2 ≤ h * realDedekindZeta F (1+h) ∧
      h * realDedekindZeta F (1+h) ≤ 2 * NumberField.dedekindZeta_residue F at HE
  simpa only [dedekindZeta_residue_algEquiv e,realDedekindZeta,
    dedekindZeta_algEquiv e] using HE

 

theorem no_quadratic_subfield {K : Type*} [Field K] [NumberField K]
    {n : ℕ} (hn : n.Prime) (hn3 : 3 ≤ n) (hdeg : Module.finrank ℚ K = n)
    (F : IntermediateField ℚ K) : Module.finrank ℚ F ≠ 2 := by
  intro hF
  have hmul := Module.finrank_mul_finrank ℚ F K
  rw [hF,hdeg] at hmul
  have hd : 2 ∣ n := ⟨Module.finrank F K,hmul.symm⟩
  rcases hn.eq_one_or_self_of_dvd 2 hd with h|h <;> omega

end PrimeDegreePackets


namespace PrimeDegreePackets
open Filter Topology
open scoped ENNReal

 

theorem weightedIdeal_interval_bounded_discr (n : ℕ) (hn0 : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (A₀ : ℝ), 1 ≤ A₀ → ∀ η : ℝ, 0 < η →
      ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type*) [Field K] [NumberField K] (M : FullLattice n K),
        (K →+* ℝ) → |NumberField.discr K| ≤ N →
        Module.finrank ℚ K = n → (saturationIndex M : ℝ) ≤ Q →
        ∀ a b : ℕ, Q^(3/4:ℝ) ≤ (b:ℝ) → (b:ℝ) ≤ A₀*Q →
          a ≤ b → η*b ≤ (b:ℝ)-a →
          weightedIdealInterval M a b ≤ (saturationIndex M : ℝ≥0∞)⁻¹ *
            ENNReal.ofReal (C * ((b:ℝ)-a) * NumberField.dedekindZeta_residue K) := by
  obtain ⟨C,hC,H⟩ := weightedIdeal_interval_zeta_bound n hn0
  refine ⟨2*C,by positivity,?_⟩
  intro N A₀ hA η hη
  obtain ⟨D,hD,δ,hδ,Hδ⟩ := bounded_discr_residue_comparison N
  have hlog : Tendsto (fun Q : ℝ => Real.log (Q^(3/4:ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_rpow_atTop (by norm_num))
  filter_upwards [H A₀ hA η hη,hlog.eventually_gt_atTop (1/δ),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/4)).eventually_ge_atTop 2]
    with Q hQ hQL hQ2
  intro K _ _ M σ hdisc hn hq a b hb hbQ hab hrel
  have hb2 : (2:ℝ) ≤ b := hQ2.trans hb
  have hlogb : 0 < Real.log (b:ℝ) := Real.log_pos (by linarith)
  have hsmall : 1/Real.log (b:ℝ) < δ := by
    have Hlog : 1/δ < Real.log (b:ℝ) :=
      hQL.trans_le (Real.log_le_log (by linarith) hb)
    exact (one_div_lt hlogb hδ).mpr Hlog
  have HR := ((Hδ K σ hdisc).2 (1/Real.log b) (one_div_pos.mpr hlogb) hsmall).2
  have Hratio : (NumberField.dedekindZeta K (1+1/Real.log b)).re / Real.log b ≤
      2*NumberField.dedekindZeta_residue K := by
    simpa only [realDedekindZeta,Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_one,
      one_div,Complex.ofReal_inv,mul_comm (Real.log (b:ℝ))⁻¹,← div_eq_mul_inv] using HR
  apply (hQ K M hn hq a b hb hbQ hab hrel).trans
  apply mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
  calc
    C*((b:ℝ)-a)*_ ≤ C*((b:ℝ)-a)*(2*NumberField.dedekindZeta_residue K) :=
      mul_le_mul_of_nonneg_left Hratio (mul_nonneg hC.le (sub_nonneg.mpr (by exact_mod_cast hab)))
    _ = _ := by ring

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma rounded_relative_interval {x y η : ℝ} (_hx : 1 ≤ x) (hy : 2 ≤ y)
    (hη : 0 < η) (hrel : η*x ≤ y) (hyx : y ≤ x) :
    ⌊x-y⌋₊ ≤ ⌈x⌉₊ ∧ x ≤ (⌈x⌉₊:ℝ) ∧ (⌈x⌉₊:ℝ) ≤ x+1 ∧
    η/2*(⌈x⌉₊:ℝ) ≤ (⌈x⌉₊:ℝ)-(⌊x-y⌋₊:ℝ) ∧
    (⌈x⌉₊:ℝ)-(⌊x-y⌋₊:ℝ) ≤ 2*y := by
  have hceil := Nat.le_ceil x
  have hceil' := (Nat.ceil_lt_add_one (by linarith : 0 ≤ x)).le
  have hfloor := Nat.floor_le (show 0 ≤ x-y by linarith)
  have hfloor' := Nat.lt_floor_add_one (x-y)
  have hab : ⌊x-y⌋₊ ≤ ⌈x⌉₊ := by exact_mod_cast (by linarith : (⌊x-y⌋₊:ℝ) ≤ (⌈x⌉₊:ℝ))
  refine ⟨hab,hceil,hceil',?_,by linarith⟩
  have H : η/2*(⌈x⌉₊:ℝ) ≤ η*x := by nlinarith
  exact H.trans (by linarith)

lemma eventual_rounding_parameters (A₀ η : ℝ) (_hA : 1 ≤ A₀) (hη : 0 < η) :
    ∀ᶠ Q : ℝ in atTop, ∀ x y : ℝ, Q^(3/4:ℝ) ≤ x → x ≤ A₀*Q →
      η*x ≤ y → y ≤ x →
      1 ≤ Q ∧ ⌊x-y⌋₊ ≤ ⌈x⌉₊ ∧ Q^(3/4:ℝ) ≤ (⌈x⌉₊:ℝ) ∧
      (⌈x⌉₊:ℝ) ≤ (A₀+1)*Q ∧
      η/2*(⌈x⌉₊:ℝ) ≤ (⌈x⌉₊:ℝ)-(⌊x-y⌋₊:ℝ) ∧
      (⌈x⌉₊:ℝ)-(⌊x-y⌋₊:ℝ) ≤ 2*y := by
  have ht := tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/4)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually_ge_atTop 1,
    ht.eventually_ge_atTop (2/η)] with Q hQ hQ1 hQη
  intro x y hxl hxu hy hyx
  have hx : 1 ≤ x := hQ1.trans hxl
  have htwo : 2 ≤ y := by
    have : 2/η ≤ x := hQη.trans hxl
    have := (div_le_iff₀ hη).mp this
    nlinarith
  obtain ⟨hab,hceil,hceil',hrel,hw⟩ := rounded_relative_interval hx htwo hη hy hyx
  refine ⟨hQ,hab,hxl.trans hceil,?_,hrel,hw⟩
  nlinarith

end PrimeDegreePackets


namespace PrimeDegreePackets
open Filter Topology
open scoped ENNReal NumberField

 

noncomputable def weightedIdealRealInterval {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (x y : ℝ) : ℝ≥0∞ :=
  ∑' I : {J : Ideal (𝓞 K) // J ≠ ⊥},
    if x-y < (Ideal.absNorm I.1:ℝ) ∧ (Ideal.absNorm I.1:ℝ) ≤ x
    then globalIdealWeight M (nonzeroIntegralIdealUnit I) else 0

lemma weightedIdealRealInterval_le_rounded {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (x y : ℝ) (hyx : y ≤ x) :
    weightedIdealRealInterval M x y ≤ weightedIdealInterval M ⌊x-y⌋₊ ⌈x⌉₊ := by
  classical
  apply ENNReal.tsum_le_tsum
  intro I
  split_ifs with h h' h'
  · rfl
  · exfalso
    apply h'
    refine ⟨(Nat.floor_lt (sub_nonneg.mpr hyx)).mpr h.1,?_⟩
    exact_mod_cast (h.2.trans (Nat.le_ceil x))
  · exact bot_le
  · rfl

 

theorem weightedIdeal_realInterval_zeta_bound (n : ℕ) (hn0 : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ A₀ : ℝ, 1 ≤ A₀ → ∀ η : ℝ, 0 < η →
      ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type*) [Field K] [NumberField K] (M : FullLattice n K),
        Module.finrank ℚ K = n → (saturationIndex M : ℝ) ≤ Q →
        ∀ x y : ℝ, Q^(3/4:ℝ) ≤ x → x ≤ A₀*Q →
          η*x ≤ y → y ≤ x →
          weightedIdealRealInterval M x y ≤ (saturationIndex M : ℝ≥0∞)⁻¹ *
            ENNReal.ofReal (C*y*((NumberField.dedekindZeta K
              (1+1/Real.log (⌈x⌉₊:ℝ))).re / Real.log (⌈x⌉₊:ℝ))) := by
  obtain ⟨C,hC,H⟩ := weightedIdeal_interval_zeta_bound n hn0
  refine ⟨2*C,by positivity,?_⟩
  intro A₀ hA η hη
  filter_upwards [H (A₀+1) (by linarith) (η/2) (by positivity),
    eventual_rounding_parameters A₀ η hA hη,
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/4)).eventually_ge_atTop 2]
    with Q hQ hround hQ2
  intro K _ _ M hn hq x y hxl hxu hrel hyx
  obtain ⟨_,hab,hbl,hbu,hbrel,hwidth⟩ := hround x y hxl hxu hrel hyx
  have hb2 : (2:ℝ) ≤ (⌈x⌉₊:ℝ) := hQ2.trans hbl
  have hlog : 0 < Real.log (⌈x⌉₊:ℝ) := Real.log_pos (by linarith)
  have hz : 0 ≤ (NumberField.dedekindZeta K (1+1/Real.log (⌈x⌉₊:ℝ))).re := by
    have HZ := dedekindZeta_real_one_le K
      (show 1 < 1+1/Real.log (⌈x⌉₊:ℝ) by linarith [one_div_pos.mpr hlog])
    exact le_trans zero_le_one (by
      simpa only [Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_one] using HZ)
  apply (weightedIdealRealInterval_le_rounded M x y hyx).trans
  apply (hQ K M hn hq _ _ hbl hbu hab hbrel).trans
  apply mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
  calc
    C*((⌈x⌉₊:ℝ)-(⌊x-y⌋₊:ℝ))*_ ≤ C*(2*y)*_ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwidth hC.le) (div_nonneg hz hlog.le)
    _ = _ := by ring

 

theorem weightedIdeal_realInterval_bounded_discr (n : ℕ) (hn0 : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (A₀ : ℝ), 1 ≤ A₀ → ∀ η : ℝ, 0 < η →
      ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type*) [Field K] [NumberField K] (M : FullLattice n K),
        (K →+* ℝ) → |NumberField.discr K| ≤ N →
        Module.finrank ℚ K = n → (saturationIndex M : ℝ) ≤ Q →
        ∀ x y : ℝ, Q^(3/4:ℝ) ≤ x → x ≤ A₀*Q →
          η*x ≤ y → y ≤ x →
          weightedIdealRealInterval M x y ≤ (saturationIndex M : ℝ≥0∞)⁻¹ *
            ENNReal.ofReal (C*y*NumberField.dedekindZeta_residue K) := by
  obtain ⟨C,hC,H⟩ := weightedIdeal_interval_bounded_discr n hn0
  refine ⟨2*C,by positivity,?_⟩
  intro N A₀ hA η hη
  filter_upwards [H N (A₀+1) (by linarith) (η/2) (by positivity),
    eventual_rounding_parameters A₀ η hA hη] with Q hQ hround
  intro K _ _ M σ hdisc hn hq x y hxl hxu hrel hyx
  obtain ⟨_,hab,hbl,hbu,hbrel,hwidth⟩ := hround x y hxl hxu hrel hyx
  apply (weightedIdealRealInterval_le_rounded M x y hyx).trans
  apply (hQ K M σ hdisc hn hq _ _ hbl hbu hab hbrel).trans
  apply mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
  calc
    C*((⌈x⌉₊:ℝ)-(⌊x-y⌋₊:ℝ))*_ ≤ C*(2*y)*_ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwidth hC.le)
        (NumberField.dedekindZeta_residue_pos K).le
    _ = _ := by ring

end PrimeDegreePackets

open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
namespace PrimeDegreePackets

theorem embeddingMatrix_det_ne_zero {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n) :
    Matrix.det (embeddingMatrix M σ) ≠ 0 := by
  let b := fullLatticeRatBasis M hn
  let e : Fin n → (K →ₐ[ℚ] ℝ) := fun i => RingHom.equivRatAlgHom K ℝ (σ i)
  have he : Function.Injective e := (RingHom.equivRatAlgHom K ℝ).injective.comp σ.injective
  have H := (linearIndependent_algHom_toLinearMap ℚ K ℝ).comp e he
  have H' := H.map' (b.constr ℝ).symm.toLinearMap (b.constr ℝ).symm.ker
  apply Matrix.nonsingular_iff_det_ne_zero.mp
  apply Matrix.Nonsingular.of_linearIndependent_col
  have heq : (b.constr ℝ).symm.toLinearMap ∘ AlgHom.toLinearMap ∘ e =
      (embeddingMatrix M σ).col := by
    ext i j
    simp [b, e, embeddingMatrix, Matrix.col, Function.comp_def]
  rw [heq] at H'
  exact H'

 

lemma rowLattice_neg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    rowLattice (-A) = rowLattice A := by
  unfold rowLattice
  rw [show (Set.range fun i => (-A) i) = -(Set.range fun i => A i) by
    ext v
    simp [Set.mem_neg, funext_iff, neg_eq_iff_eq_neg]]
  exact Submodule.span_neg _

 

lemma normalizedMatrix_abs_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hn : 0 < n) (hA : A.det ≠ 0) :
    |Matrix.det (|A.det| ^ (-(1 : ℝ) / n) • A)| = 1 := by
  have hpos : 0 < |A.det| := abs_pos.mpr hA
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Matrix.det_smul, Fintype.card_fin, abs_mul, abs_pow,
    abs_of_pos (Real.rpow_pos_of_pos hpos _), ← Real.rpow_natCast,
    ← Real.rpow_mul hpos.le]
  have he : (-(1 : ℝ) / n) * n = -1 := div_mul_cancel₀ _ hn0
  rw [he, Real.rpow_neg_one, inv_mul_cancel₀ hpos.ne']

 

theorem exists_SL_normalizedLattice {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n)
    (hodd : Odd n) : ∃ g : G n, rowLattice g.1 = normalizedLattice M σ := by
  let B := embeddingMatrix M σ
  let A := |B.det| ^ (-(1 : ℝ) / n) • B
  have hd : |A.det| = 1 := normalizedMatrix_abs_det B hodd.pos
    (embeddingMatrix_det_ne_zero M σ hn)
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hd with h | h
  · exact ⟨⟨A, h⟩, rfl⟩
  · have hneg : (-A).det = 1 := by
      rw [Matrix.det_neg, Fintype.card_fin, hodd.neg_one_pow, h]
      norm_num
    exact ⟨⟨-A, hneg⟩, rowLattice_neg A⟩

open scoped NumberField nonZeroDivisors

 

theorem multiplierOrder_le_integralElements {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : multiplierOrder M ≤ integralElements K := by
  intro a ha
  have hne : M.carrier ≠ ⊥ := by
    intro h
    have H : (⊥ : Submodule ℚ K) = ⊤ := by simpa [h] using M.spans
    exact bot_ne_top H
  have hfg : M.carrier.FG := by
    rw [← fullLattice_span_basis M]
    exact Submodule.fg_span (Set.finite_range _)
  exact isIntegral_of_smul_mem_submodule M.carrier hne hfg a ha

 

lemma scaled_integralElements_le_multiplierOrder {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) :
    (integralElements K).map (nsmulAddMonoidHom (saturationIndex M)) ≤ multiplierOrder M := by
  rintro _ ⟨a, ha, rfl⟩ x hx
  change (saturationIndex M • a) * x ∈ M.carrier
  rw [smul_mul_assoc]
  apply saturationIndex_smul_mem
  change a * x ∈ Submodule.span (𝓞 K) (M.carrier : Set K)
  exact Submodule.smul_mem _ (⟨a, ha⟩ : 𝓞 K) (Submodule.subset_span hx)

 

lemma integralElements_scaled_index {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : Module.finrank ℚ K = n) (q : ℕ) :
    ((integralElements K).map (nsmulAddMonoidHom q)).relIndex (integralElements K) = q ^ n := by
  let e : 𝓞 K ≃+ (integralElements K).toIntSubmodule := AddEquiv.refl _
  let : Module.Free ℤ (integralElements K).toIntSubmodule :=
    Module.Free.of_equiv e.toIntLinearEquiv
  let : Module.Finite ℤ (integralElements K).toIntSubmodule :=
    Module.Finite.equiv e.toIntLinearEquiv
  rw [AddSubgroup.relIndex_map_nsmul]
  congr 1
  exact e.toIntLinearEquiv.finrank_eq.symm.trans ((NumberField.RingOfIntegers.rank K).trans hn)

 

theorem multiplierOrder_index_le {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) :
    (multiplierOrder M).relIndex (integralElements K) ≤ saturationIndex M ^ n := by
  have h := AddSubgroup.relIndex_le_of_le_left
    (scaled_integralElements_le_multiplierOrder M)
    (show ((integralElements K).map (nsmulAddMonoidHom (saturationIndex M))).relIndex
      (integralElements K) ≠ 0 by
        rw [integralElements_scaled_index hn]
        exact pow_ne_zero _ (saturationIndex_ne_zero M))
  rwa [integralElements_scaled_index hn] at h

 

def packetScale {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : ℝ := saturationIndex M * Real.sqrt |(NumberField.discr K : ℝ)|

lemma fieldDiscriminant_one_le (K : Type*) [Field K] [NumberField K] :
    1 ≤ |(NumberField.discr K : ℝ)| := by
  exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero K)

lemma packetScale_pos {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : 0 < packetScale M := by
  unfold packetScale
  exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero (saturationIndex_ne_zero M))
    (Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num) (fieldDiscriminant_one_le K)))

 

theorem multiplierDiscriminant_le_packetScale_pow {n : ℕ} {K : Type*}
    [Field K] [NumberField K] (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (hnpos : 0 < n) : multiplierDiscriminant M ≤ packetScale M ^ (2 * n) := by
  have hi : ((multiplierOrder M).relIndex (integralElements K) : ℝ) ≤
      (saturationIndex M : ℝ) ^ n := by exact_mod_cast multiplierOrder_index_le M hn
  have hD := fieldDiscriminant_one_le K
  have hDp : |(NumberField.discr K : ℝ)| ≤ |(NumberField.discr K : ℝ)| ^ n :=
    le_self_pow₀ hD hnpos.ne'
  calc
    multiplierDiscriminant M ≤ |(NumberField.discr K : ℝ)| *
        ((saturationIndex M : ℝ) ^ n) ^ 2 := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hi 2) (abs_nonneg _)
    _ ≤ |(NumberField.discr K : ℝ)| ^ n * ((saturationIndex M : ℝ) ^ n) ^ 2 :=
      mul_le_mul_of_nonneg_right hDp (sq_nonneg _)
    _ = packetScale M ^ (2 * n) := by
      unfold packetScale
      rw [mul_pow, pow_mul (Real.sqrt _) 2 n, Real.sq_sqrt (abs_nonneg _),
        ← pow_mul, Nat.mul_comm n 2, mul_comm]

 

theorem packetScale_tendsto_of_multiplierDiscriminant_tendsto
    {n : ℕ} (hnpos : 0 < n) (K : ℕ → Type*)
    [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    (M : ∀ i, FullLattice n (K i)) (hn : ∀ i, Module.finrank ℚ (K i) = n)
    (hD : Tendsto (fun i => multiplierDiscriminant (M i)) atTop atTop) :
    Tendsto (fun i => packetScale (M i)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [hD.eventually (eventually_gt_atTop (|b| ^ (2 * n)))] with i hi
  have hlt : |b| ^ (2 * n) < packetScale (M i) ^ (2 * n) :=
    hi.trans_le (multiplierDiscriminant_le_packetScale_pow (M i) (hn i) hnpos)
  by_contra hb
  have hle : packetScale (M i) ≤ |b| := (le_of_not_ge hb).trans (le_abs_self b)
  exact (not_lt_of_ge (pow_le_pow_left₀ (packetScale_pos (M i)).le hle _)) hlt

 

def integralUnit {K : Type*} [Field K] [NumberField K] : (𝓞 K)ˣ →* Kˣ :=
  Units.map (algebraMap (𝓞 K) K).toMonoidHom

 

def unitStabilizer {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : Subgroup (𝓞 K)ˣ where
  carrier := {u | ∀ x : K, x ∈ M.carrier ↔ (integralUnit u : K) * x ∈ M.carrier}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv x
    rw [map_mul, Units.val_mul, mul_assoc]
    exact (hv x).trans (hu ((integralUnit v : K) * x))
  inv_mem' := by
    intro u hu x
    have h := hu ((integralUnit u⁻¹ : K) * x)
    simpa [← mul_assoc] using h.symm

 

def unitsReduction {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) :
    (𝓞 K)ˣ →* (𝓞 K ⧸ Ideal.span {(saturationIndex M : 𝓞 K)})ˣ :=
  Units.map (Ideal.Quotient.mk (Ideal.span {(saturationIndex M : 𝓞 K)})).toMonoidHom

lemma unitsReduction_one_preserves {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (u : (𝓞 K)ˣ) (hu : unitsReduction M u = 1)
    {x : K} (hx : x ∈ M.carrier) : (integralUnit u : K) * x ∈ M.carrier := by
  have hu' : Ideal.Quotient.mk (Ideal.span {(saturationIndex M : 𝓞 K)}) (u : 𝓞 K) = 1 :=
    congrArg Units.val hu
  have hz : (u : 𝓞 K) - 1 ∈ Ideal.span {(saturationIndex M : 𝓞 K)} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, hu', map_one, sub_self]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hz
  have hax : (a : K) * x ∈ saturation M := by
    exact Submodule.smul_mem (Submodule.span (𝓞 K) (M.carrier : Set K)) a
      (Submodule.subset_span hx)
  have hqx := saturationIndex_smul_mem M hax
  have heq : (integralUnit u : K) * x = x + saturationIndex M • ((a : K) * x) := by
    have H := congrArg (algebraMap (𝓞 K) K) ha
    change ((u : 𝓞 K) : K) * x = _
    simp only [map_sub, map_one, map_mul, map_natCast] at H
    rw [nsmul_eq_mul]
    linear_combination H * x
  rw [heq]
  exact M.carrier.add_mem hx hqx

lemma unitsReduction_ker_le_stabilizer {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : (unitsReduction M).ker ≤ unitStabilizer M := by
  intro u hu
  change unitsReduction M u = 1 at hu
  intro x
  constructor
  · exact unitsReduction_one_preserves M u hu
  · intro hx
    have h := unitsReduction_one_preserves M u⁻¹ (by simp [hu]) hx
    simpa [← mul_assoc] using h

 

theorem unitStabilizer_finiteIndex {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : (unitStabilizer M).FiniteIndex := by
  have hq : (saturationIndex M : 𝓞 K) ≠ 0 := by
    exact_mod_cast saturationIndex_ne_zero M
  let : Finite (𝓞 K ⧸ Ideal.span {(saturationIndex M : 𝓞 K)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hq)
  exact Subgroup.finiteIndex_of_le (unitsReduction_ker_le_stabilizer M)

 

def unitSigns {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) : (𝓞 K)ˣ →* (Fin n → SignTypeˣ) where
  toFun u i := Units.map ((signHom : ℝ →*₀ SignType).toMonoidHom.comp
    (σ i).toMonoidHom) (integralUnit u)
  map_one' := by ext i; simp
  map_mul' u v := by ext i; simp

lemma unitSigns_eq_one_iff {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (u : (𝓞 K)ˣ) :
    unitSigns σ u = 1 ↔ ∀ i, 0 < σ i (integralUnit u : K) := by
  simp only [funext_iff, Pi.one_apply, Units.ext_iff]
  change (∀ i, SignType.sign (σ i (integralUnit u : K)) = 1) ↔ _
  simp only [sign_eq_one_iff]

 

def positiveUnitStabilizer {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) : Subgroup (𝓞 K)ˣ :=
  unitStabilizer M ⊓ (unitSigns σ).ker

lemma mem_positiveUnitStabilizer {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) (u : (𝓞 K)ˣ) :
    u ∈ positiveUnitStabilizer M σ ↔ u ∈ unitStabilizer M ∧
      ∀ i, 0 < σ i (integralUnit u : K) := by
  simp only [positiveUnitStabilizer, Subgroup.mem_inf, MonoidHom.mem_ker,
    unitSigns_eq_one_iff]

 

theorem positiveUnitStabilizer_finiteIndex {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) :
    (positiveUnitStabilizer M σ).FiniteIndex := by
  have hq : (saturationIndex M : 𝓞 K) ≠ 0 := by
    exact_mod_cast saturationIndex_ne_zero M
  let : Finite (𝓞 K ⧸ Ideal.span {(saturationIndex M : 𝓞 K)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hq)
  apply Subgroup.finiteIndex_of_le (H := ((unitsReduction M).prod (unitSigns σ)).ker)
  intro u hu
  have h : unitsReduction M u = 1 ∧ unitSigns σ u = 1 := by
    change (unitsReduction M u, unitSigns σ u) = (1, 1) at hu
    exact Prod.mk.inj hu
  exact ⟨unitsReduction_ker_le_stabilizer M h.1, h.2⟩

 

def logSubgroup {K : Type*} [Field K] [NumberField K] (S : Subgroup (𝓞 K)ˣ) :
    Submodule ℤ (NumberField.Units.dirichletUnitTheorem.logSpace K) :=
  Submodule.map (NumberField.Units.logEmbedding K).toIntLinearMap
    S.toAddSubgroup.toIntSubmodule

lemma logSubgroup_le_unitLattice {K : Type*} [Field K] [NumberField K]
    (S : Subgroup (𝓞 K)ˣ) : logSubgroup S ≤ NumberField.Units.unitLattice K :=
  Submodule.map_mono le_top

instance logSubgroup_discrete {K : Type*} [Field K] [NumberField K]
    (S : Subgroup (𝓞 K)ˣ) : DiscreteTopology (logSubgroup S) := by
  apply DiscreteTopology.of_continuous_injective
    (f := Submodule.inclusion (logSubgroup_le_unitLattice S))
  · exact continuous_subtype_val.subtype_mk _
  · exact Submodule.inclusion_injective _

 

theorem logSubgroup_span_eq_top {K : Type*} [Field K] [NumberField K]
    (S : Subgroup (𝓞 K)ˣ) [S.FiniteIndex] :
    Submodule.span ℝ (logSubgroup S : Set (NumberField.Units.dirichletUnitTheorem.logSpace K)) = ⊤ := by
  rw [eq_top_iff, ← NumberField.Units.dirichletUnitTheorem.unitLattice_span_eq_top K]
  apply Submodule.span_le.mpr
  intro x hx
  obtain ⟨u, _, rfl⟩ := Submodule.mem_map.mp hx
  have hu : (NumberField.Units.logEmbedding K) (Additive.ofMul (u.toMul ^ S.index)) ∈
      logSubgroup S := Submodule.mem_map.mpr
    ⟨Additive.ofMul (u.toMul ^ S.index), S.pow_index_mem u.toMul, rfl⟩
  have hmul : (S.index : ℝ) • (NumberField.Units.logEmbedding K) u =
      (NumberField.Units.logEmbedding K) (Additive.ofMul (u.toMul ^ S.index)) := by
    rw [Nat.cast_smul_eq_nsmul ℝ, ← map_nsmul]
    rfl
  have hmem := Submodule.smul_mem
    (Submodule.span ℝ (logSubgroup S : Set (NumberField.Units.dirichletUnitTheorem.logSpace K))) (S.index : ℝ)⁻¹
    (Submodule.subset_span hu)
  rw [← hmul, smul_smul, inv_mul_cancel₀ (by exact_mod_cast (Subgroup.FiniteIndex.index_ne_zero (H := S))), one_smul] at hmem
  exact hmem

instance logSubgroup_isZLattice {K : Type*} [Field K] [NumberField K]
    (S : Subgroup (𝓞 K)ˣ) [S.FiniteIndex] : IsZLattice ℝ (logSubgroup S) :=
  ⟨logSubgroup_span_eq_top S⟩

 

def realPlace {K : Type*} [Field K] (σ : K →+* ℝ) : NumberField.InfinitePlace K :=
  NumberField.InfinitePlace.mk (Complex.ofRealHom.comp σ)

@[simp] theorem realPlace_apply {K : Type*} [Field K] (σ : K →+* ℝ) (x : K) :
    realPlace σ x = |σ x| := by
  simp [realPlace, NumberField.InfinitePlace.apply, Real.norm_eq_abs]

lemma realPlace_injective {K : Type*} [Field K] : Function.Injective (realPlace (K := K)) := by
  intro σ τ h
  apply RingHom.ext
  intro x
  rcases NumberField.InfinitePlace.mk_eq_iff.mp h with h | h
  · exact Complex.ofReal_injective (RingHom.congr_fun h x)
  · have H := RingHom.congr_fun h x
    simpa [NumberField.ComplexEmbedding.conjugate] using H

lemma realPlace_surjective {K : Type*} [Field K] [NumberField.IsTotallyReal K] :
    Function.Surjective (realPlace (K := K)) := by
  intro w
  refine ⟨NumberField.InfinitePlace.embedding_of_isReal (NumberField.IsTotallyReal.isReal w), ?_⟩
  unfold realPlace
  rw [show Complex.ofRealHom.comp
      (NumberField.InfinitePlace.embedding_of_isReal (NumberField.IsTotallyReal.isReal w)) =
      w.embedding by ext x; simp]
  exact NumberField.InfinitePlace.mk_embedding w

 

def orderedRealPlaces {n : ℕ} {K : Type*} [Field K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings n K) : Fin n ≃ NumberField.InfinitePlace K :=
  σ.trans (Equiv.ofBijective realPlace ⟨realPlace_injective, realPlace_surjective⟩)

@[simp] lemma orderedRealPlaces_apply {n : ℕ} {K : Type*} [Field K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings n K) (i : Fin n) (x : K) :
    orderedRealPlaces σ i x = |σ i x| := realPlace_apply _ _

 

def zeroSumSubmodule (ι : Type*) [Fintype ι] : Submodule ℝ (ι → ℝ) :=
  { carrier := {u | ∑ i, u i = 0}
    zero_mem' := by simp
    add_mem' := by intro u v hu hv; simp_all [Finset.sum_add_distrib]
    smul_mem' := by
      intro c u hu
      change ∑ i, c * u i = 0
      rw [← Finset.mul_sum, hu, mul_zero]}

@[simp] lemma mem_zeroSumSubmodule {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    u ∈ zeroSumSubmodule ι ↔ ∑ i, u i = 0 := Iff.rfl

 

def insertDeleted {ι : Type*} [Fintype ι] (i₀ : ι) :
    ({i : ι // i ≠ i₀} → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun u i := if h : i = i₀ then -∑ j, u j else u ⟨i, h⟩
  map_add' u v := by ext i; dsimp; split_ifs <;> simp [Finset.sum_add_distrib, add_comm]
  map_smul' c u := by ext i; dsimp; split_ifs <;> simp [Finset.mul_sum]

@[simp] lemma insertDeleted_self {ι : Type*} [Fintype ι] (i₀ : ι)
    (u : {i : ι // i ≠ i₀} → ℝ) : insertDeleted i₀ u i₀ = -∑ j, u j := by
  simp [insertDeleted]

@[simp] lemma insertDeleted_ne {ι : Type*} [Fintype ι] (i₀ : ι)
    (u : {i : ι // i ≠ i₀} → ℝ) (i : {i : ι // i ≠ i₀}) :
    insertDeleted i₀ u i = u i := by simp [insertDeleted, i.property]

lemma insertDeleted_sum {ι : Type*} [Fintype ι] (i₀ : ι)
    (u : {i : ι // i ≠ i₀} → ℝ) : ∑ i, insertDeleted i₀ u i = 0 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀]
  simp

 

def deletedCoordinatesEquiv {ι : Type*} [Fintype ι] (i₀ : ι) :
    ({i : ι // i ≠ i₀} → ℝ) ≃ₗ[ℝ] zeroSumSubmodule ι where
  toFun u := ⟨insertDeleted i₀ u, insertDeleted_sum i₀ u⟩
  invFun u i := u.1 i
  left_inv u := by ext i; simp
  right_inv u := by
    apply Subtype.ext
    funext i
    by_cases hi : i = i₀
    · subst i
      have h := u.property
      change ∑ i, u.1 i = 0 at h
      rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀] at h
      simp only [insertDeleted_self]
      linarith
    · exact insertDeleted_ne i₀ _ ⟨i, hi⟩
  map_add' u v := by apply Subtype.ext; exact map_add (insertDeleted i₀) u v
  map_smul' c u := by apply Subtype.ext; exact map_smul (insertDeleted i₀) c u

 

def zeroSumReindex {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    zeroSumSubmodule κ ≃ₗ[ℝ] zeroSumSubmodule ι where
  toFun u := ⟨fun i => u.1 (e i), by
    change ∑ i, u.1 (e i) = 0
    rw [Equiv.sum_comp e]
    exact u.property⟩
  invFun u := ⟨fun i => u.1 (e.symm i), by
    change ∑ i, u.1 (e.symm i) = 0
    rw [Equiv.sum_comp e.symm]
    exact u.property⟩
  left_inv u := by ext i; simp
  right_inv u := by ext i; simp
  map_add' u v := rfl
  map_smul' c u := rfl

 

def changeDeletedCoordinates {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (i₀ : ι) (j₀ : κ) :
    ({j : κ // j ≠ j₀} → ℝ) ≃ₗ[ℝ] ({i : ι // i ≠ i₀} → ℝ) :=
  ((deletedCoordinatesEquiv j₀).trans (zeroSumReindex e)).trans (deletedCoordinatesEquiv i₀).symm

@[simp] theorem changeDeletedCoordinates_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (i₀ : ι) (j₀ : κ) (u : {j : κ // j ≠ j₀} → ℝ)
    (i : {i : ι // i ≠ i₀}) :
    changeDeletedCoordinates e i₀ j₀ u i = insertDeleted j₀ u (e i) := rfl

 

def orderedLogCoordinatesEquiv {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d + 1) K) :
    NumberField.Units.dirichletUnitTheorem.logSpace K ≃ₗ[ℝ] (Fin d → ℝ) :=
  (changeDeletedCoordinates (orderedRealPlaces σ) (Fin.last d)
    NumberField.Units.dirichletUnitTheorem.w₀).trans
    (LinearEquiv.funCongrLeft ℝ ℝ (finSuccAboveEquiv (Fin.last d)))

lemma insertDeleted_logEmbedding {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (u : (𝓞 K)ˣ) (w : NumberField.InfinitePlace K) :
    insertDeleted NumberField.Units.dirichletUnitTheorem.w₀
      (NumberField.Units.logEmbedding K (Additive.ofMul u)) w = Real.log (w (u : K)) := by
  by_cases hw : w = NumberField.Units.dirichletUnitTheorem.w₀
  · subst w
    rw [insertDeleted_self, NumberField.Units.dirichletUnitTheorem.sum_logEmbedding_component]
    rw [(NumberField.IsTotallyReal.isReal _).mult_eq_one]
    simp
  · rw [show w = (⟨w, hw⟩ : {w : NumberField.InfinitePlace K //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}).val from rfl,
      insertDeleted_ne]
    rw [NumberField.Units.dirichletUnitTheorem.logEmbedding_component,
      (NumberField.IsTotallyReal.isReal _).mult_eq_one]
    simp

 

def orderedUnitLog {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d + 1) K) :
    Additive ((𝓞 K)ˣ) →+ (Fin d → ℝ) :=
  (orderedLogCoordinatesEquiv σ).toAddMonoidHom.comp (NumberField.Units.logEmbedding K)

@[simp] lemma orderedUnitLog_apply {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d + 1) K) (u : (𝓞 K)ˣ) (i : Fin d) :
    orderedUnitLog σ (Additive.ofMul u) i = Real.log |σ i.castSucc (u : K)| := by
  change insertDeleted NumberField.Units.dirichletUnitTheorem.w₀
    (NumberField.Units.logEmbedding K (Additive.ofMul u))
    (orderedRealPlaces σ ((finSuccAboveEquiv (Fin.last d) i).val)) = _
  simp only [insertDeleted_logEmbedding, finSuccAboveEquiv_apply, Fin.succAbove_last,
    orderedRealPlaces_apply]

 

def orderedLogSubgroup {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d + 1) K)
    (S : Subgroup (𝓞 K)ˣ) : Submodule ℤ (Fin d → ℝ) :=
  ZLattice.comap ℝ (logSubgroup S) (orderedLogCoordinatesEquiv σ).symm.toLinearMap

lemma mem_orderedLogSubgroup {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d + 1) K)
    (S : Subgroup (𝓞 K)ˣ) (v : Fin d → ℝ) :
    v ∈ orderedLogSubgroup σ S ↔ ∃ u ∈ S, orderedUnitLog σ (Additive.ofMul u) = v := by
  change (orderedLogCoordinatesEquiv σ).symm v ∈ logSubgroup S ↔ _
  constructor
  · intro hv
    obtain ⟨u, hu, heq⟩ := Submodule.mem_map.mp hv
    refine ⟨u.toMul, hu, ?_⟩
    change orderedLogCoordinatesEquiv σ (NumberField.Units.logEmbedding K u) = v
    change NumberField.Units.logEmbedding K u = (orderedLogCoordinatesEquiv σ).symm v at heq
    rw [heq, LinearEquiv.apply_symm_apply]
  · rintro ⟨u, hu, rfl⟩
    change (orderedLogCoordinatesEquiv σ).symm
      (orderedLogCoordinatesEquiv σ (NumberField.Units.logEmbedding K (Additive.ofMul u))) ∈ _
    rw [LinearEquiv.symm_apply_apply]
    exact Submodule.mem_map.mpr ⟨Additive.ofMul u, hu, rfl⟩

instance orderedLogSubgroup_discrete {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d + 1) K)
    (S : Subgroup (𝓞 K)ˣ) : DiscreteTopology (orderedLogSubgroup σ S) :=
  ZLattice.comap_discreteTopology ℝ (logSubgroup S)
    (orderedLogCoordinatesEquiv σ).symm.toContinuousLinearEquiv.continuous
    (orderedLogCoordinatesEquiv σ).symm.injective

instance orderedLogSubgroup_isZLattice {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d + 1) K)
    (S : Subgroup (𝓞 K)ˣ) [S.FiniteIndex] : IsZLattice ℝ (orderedLogSubgroup σ S) := by
  change IsZLattice ℝ (ZLattice.comap ℝ (logSubgroup S)
    (orderedLogCoordinatesEquiv σ).symm.toContinuousLinearEquiv.toLinearMap)
  infer_instance

 

theorem positiveStabilizer_fullLogLattice {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d + 1) K)
    (σ : OrderedEmbeddings (d + 1) K) :
    DiscreteTopology (orderedLogSubgroup σ (positiveUnitStabilizer M σ)) ∧
      IsZLattice ℝ (orderedLogSubgroup σ (positiveUnitStabilizer M σ)) := by
  let := positiveUnitStabilizer_finiteIndex M σ
  exact ⟨inferInstance, inferInstance⟩

 

lemma rowLattice_int_mul_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (g : Matrix (Fin n) (Fin n) ℝ) : rowLattice ((A.map (Int.castRingHom ℝ)) * g) ≤ rowLattice g := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have h : (fun j => ((A.map (Int.castRingHom ℝ)) * g) i j) = ∑ k, (A i k) • g k := by
    funext j
    simp [Matrix.mul_apply, Matrix.map_apply, Finset.sum_apply, zsmul_eq_mul]
  change (fun j => ((A.map (Int.castRingHom ℝ)) * g) i j) ∈ rowLattice g
  rw [h]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

 

lemma rowLattice_integral_mul {n : ℕ} (A : Matrix.SpecialLinearGroup (Fin n) ℤ)
    (g : G n) : rowLattice ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A * g).1) =
      rowLattice g.1 := by
  apply le_antisymm
  · exact rowLattice_int_mul_le A.1 g.1
  · have h := rowLattice_int_mul_le A⁻¹.1
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A * g).1
    change rowLattice ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A⁻¹ *
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A * g)).1) ≤ _ at h
    simpa using h

 

lemma exists_int_matrix_of_rowLattice_le {n : ℕ}
    (g h : Matrix (Fin n) (Fin n) ℝ) (hgh : rowLattice g ≤ rowLattice h) :
    ∃ A : Matrix (Fin n) (Fin n) ℤ, g = A.map (Int.castRingHom ℝ) * h := by
  have H (i : Fin n) : ∃ c : Fin n → ℤ, ∑ j, c j • h j = g i :=
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hgh (Submodule.subset_span ⟨i, rfl⟩))
  choose A hA using H
  refine ⟨A, ?_⟩
  ext i j
  have h := congrFun (hA i) j
  change g i j = ∑ k, (A i k : ℝ) * _
  simpa [Finset.sum_apply, zsmul_eq_mul] using h.symm

 

lemma exists_integral_mul_of_rowLattice_eq {n : ℕ} (g h : G n)
    (hgh : rowLattice g.1 = rowLattice h.1) :
    ∃ A : Matrix.SpecialLinearGroup (Fin n) ℤ,
      g = Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A * h := by
  obtain ⟨A, hA⟩ := exists_int_matrix_of_rowLattice_le g.1 h.1 hgh.le
  have hdet : A.det = 1 := by
    have hd := congrArg Matrix.det hA
    rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, Matrix.SpecialLinearGroup.det_coe,
      mul_one] at hd
    have hmap : (A.map (Int.castRingHom ℝ)).det = (A.det : ℝ) :=
      (Int.castRingHom ℝ).map_det A |>.symm
    rw [hmap] at hd
    exact_mod_cast hd.symm
  refine ⟨⟨A, hdet⟩, ?_⟩
  exact Subtype.ext hA

 

theorem quotient_eq_iff_rowLattice_eq {n : ℕ} (g h : G n) :
    (Quotient.mk (QuotientGroup.rightRel (integralGroup n)) g : X n) = Quotient.mk _ h ↔
      rowLattice g.1 = rowLattice h.1 := by
  constructor
  · intro heq
    have H := Quotient.exact heq
    change (QuotientGroup.rightRel (integralGroup n)) g h at H
    rw [QuotientGroup.rightRel_apply] at H
    obtain ⟨A, hA⟩ := H
    have hh : h = Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A * g := by
      rw [hA, inv_mul_cancel_right]
    rw [hh]
    exact (rowLattice_integral_mul A g).symm
  · intro H
    obtain ⟨A, rfl⟩ := exists_integral_mul_of_rowLattice_eq g h H
    apply Quotient.sound
    change (QuotientGroup.rightRel (integralGroup n))
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A * h) h
    rw [QuotientGroup.rightRel_apply]
    exact ⟨A⁻¹, by simp [mul_inv_rev]⟩

 

def realEmbeddingMap {n : ℕ} {K : Type*} [Field K] (σ : OrderedEmbeddings n K) :
    K →ₗ[ℤ] (Fin n → ℝ) where
  toFun x i := σ i x
  map_add' x y := by ext i; exact map_add (σ i) x y
  map_smul' z x := by ext i; simp

 

def diagonalLinear (n : ℕ) (t : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℤ] (Fin n → ℝ) where
  toFun x i := t i * x i
  map_add' x y := by ext i; exact mul_add _ _ _
  map_smul' z x := by ext i; simp [mul_assoc, mul_comm]

lemma fullLattice_exists_ne_zero {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : ∃ x ∈ M.carrier, x ≠ 0 := by
  by_contra! h
  have hbot : M.carrier = ⊥ := le_antisymm (fun x hx => by simp [h x hx]) bot_le
  have H : (⊥ : Submodule ℚ K) = ⊤ := by simpa [hbot] using M.spans
  exact bot_ne_top H

lemma realEmbeddingMap_injective {n : ℕ} {K : Type*} [Field K]
    (σ : OrderedEmbeddings n K) (hn : 0 < n) : Function.Injective (realEmbeddingMap σ) := by
  intro x y h
  exact (σ ⟨0, hn⟩).injective (congrFun h ⟨0, hn⟩)

 

theorem diagonal_into_lattice_is_field_multiplication
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (σ : OrderedEmbeddings n K) (t : Fin n → ℝ)
    (h : M.carrier.map ((diagonalLinear n t).comp (realEmbeddingMap σ)) ≤
      N.carrier.map (realEmbeddingMap σ)) :
    ∃ b : K, ∀ i, t i = σ i b := by
  obtain ⟨α, hα, hα0⟩ := fullLattice_exists_ne_zero M
  have hv := h (Submodule.mem_map.mpr ⟨α, hα, rfl⟩)
  obtain ⟨β, _, hβ⟩ := Submodule.mem_map.mp hv
  refine ⟨β / α, fun i => ?_⟩
  have hi : σ i β = t i * σ i α := congrFun hβ i
  rw [map_div₀]
  exact (eq_div_iff ((map_ne_zero (σ i)).mpr hα0)).mpr hi.symm

 

theorem diagonal_lattice_equality_iff_homothety
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (σ : OrderedEmbeddings n K) (hn : 0 < n)
    (t : Fin n → ℝ) (ht : ∀ i, t i ≠ 0)
    (h : M.carrier.map ((diagonalLinear n t).comp (realEmbeddingMap σ)) =
      N.carrier.map (realEmbeddingMap σ)) :
    ∃ b : K, b ≠ 0 ∧ (∀ i, t i = σ i b) ∧
      (N.carrier : Set K) = (fun x => b * x) '' (M.carrier : Set K) := by
  obtain ⟨b, hb⟩ := diagonal_into_lattice_is_field_multiplication M N σ t h.le
  refine ⟨b, ?_, hb, ?_⟩
  · intro hb0
    exact ht ⟨0, hn⟩ (by simp [hb, hb0])
  · ext x
    constructor
    · intro hx
      have he : realEmbeddingMap σ x ∈ N.carrier.map (realEmbeddingMap σ) :=
        Submodule.mem_map.mpr ⟨x, hx, rfl⟩
      rw [← h] at he
      obtain ⟨y, hy, he⟩ := Submodule.mem_map.mp he
      refine ⟨y, hy, ?_⟩
      apply realEmbeddingMap_injective σ hn
      ext i
      change σ i (b * y) = σ i x
      rw [map_mul, ← hb i]
      exact congrFun he i
    · rintro ⟨y, hy, rfl⟩
      have he : (diagonalLinear n t).comp (realEmbeddingMap σ) y ∈
          M.carrier.map ((diagonalLinear n t).comp (realEmbeddingMap σ)) :=
        Submodule.mem_map.mpr ⟨y, hy, rfl⟩
      rw [h] at he
      obtain ⟨x, hx, he⟩ := Submodule.mem_map.mp he
      have hxy : x = b * y := by
        apply realEmbeddingMap_injective σ hn
        ext i
        change σ i x = σ i (b * y)
        rw [map_mul, ← hb i]
        exact congrFun he i
      change b * y ∈ N.carrier
      rwa [← hxy]

lemma rowLattice_embeddingMatrix {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) :
    rowLattice (embeddingMatrix M σ) = M.carrier.map (realEmbeddingMap σ) := by
  rw [← fullLattice_span_basis M, Submodule.map_span, ← Set.range_comp]
  rfl

lemma rowLattice_mul_diagonal {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (t : Fin n → ℝ) :
    rowLattice (B * Matrix.diagonal t) = (rowLattice B).map (diagonalLinear n t) := by
  unfold rowLattice
  rw [Submodule.map_span, ← Set.range_comp]
  apply congrArg (Submodule.span ℤ)
  apply congrArg Set.range
  ext i j
  simp [diagonalLinear, Matrix.mul_diagonal, mul_comm]

lemma rowLattice_smul {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    rowLattice (c • B) = (rowLattice B).map (diagonalLinear n (fun _ => c)) := by
  unfold rowLattice
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

lemma diagonalLinear_commute {n : ℕ} (s t : Fin n → ℝ) :
    (diagonalLinear n s).comp (diagonalLinear n t) =
      (diagonalLinear n t).comp (diagonalLinear n s) := by
  ext x i
  simp [diagonalLinear, mul_left_comm]

 

lemma embeddedLattice_unit_invariant {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) (u : (𝓞 K)ˣ)
    (hu : u ∈ unitStabilizer M) :
    (M.carrier.map (realEmbeddingMap σ)).map
      (diagonalLinear n (fun i => σ i (u : K))) = M.carrier.map (realEmbeddingMap σ) := by
  apply le_antisymm
  · rintro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
    refine Submodule.mem_map.mpr ⟨(u : K) * z, (hu z).mp hz, ?_⟩
    ext i
    exact map_mul (σ i) _ _
  · rintro x hx
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hx
    refine Submodule.mem_map.mpr ⟨realEmbeddingMap σ ((↑u⁻¹ : K) * z),
      Submodule.mem_map.mpr ⟨_, ((unitStabilizer M).inv_mem hu z).mp hz, rfl⟩, ?_⟩
    ext i
    change σ i (u : K) * σ i ((↑u⁻¹ : K) * z) = σ i z
    rw [map_mul, ← mul_assoc, ← map_mul]
    simp

 

lemma normalizedLattice_unit_invariant {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) (u : (𝓞 K)ˣ)
    (hu : u ∈ unitStabilizer M) :
    (normalizedLattice M σ).map (diagonalLinear n (fun i => σ i (u : K))) =
      normalizedLattice M σ := by
  unfold normalizedLattice
  rw [rowLattice_smul, rowLattice_embeddingMatrix, ← Submodule.map_comp,
    diagonalLinear_commute, Submodule.map_comp, embeddedLattice_unit_invariant M σ u hu]

lemma sum_orderedUnitLog_full {n : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings n K) (u : (𝓞 K)ˣ) :
    ∑ i, Real.log |σ i (u : K)| = 0 := by
  have h := NumberField.Units.sum_mult_mul_log u
  simp only [(show ∀ w : NumberField.InfinitePlace K, w.mult = 1 from
    fun w => (NumberField.IsTotallyReal.isReal w).mult_eq_one), Nat.cast_one, one_mul] at h
  rw [← Equiv.sum_comp (orderedRealPlaces σ)] at h
  simpa only [orderedRealPlaces_apply] using h

lemma diagonalFlow_orderedUnitLog {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d + 1) K) (u : (𝓞 K)ˣ)
    (hu : ∀ i, 0 < σ i (u : K)) :
    (diagonalFlow (orderedUnitLog σ (Additive.ofMul u))).1 =
      Matrix.diagonal (fun i => σ i (u : K)) := by
  apply congrArg Matrix.diagonal
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    have h := sum_orderedUnitLog_full σ u
    rw [Fin.sum_univ_castSucc] at h
    simp only [orderedUnitLog_apply]
    rw [show -(∑ j : Fin d, Real.log |σ j.castSucc (u : K)|) =
      Real.log |σ (Fin.last d) (u : K)| by linarith]
    rw [abs_of_pos (hu _), Real.exp_log (hu _)]
  · simp only [Fin.snoc_castSucc, orderedUnitLog_apply, abs_of_pos (hu _), Real.exp_log (hu _)]

lemma latticePoint_eq_of_rowLattice_eq {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) (g : G n)
    (hg : rowLattice g.1 = normalizedLattice M σ) :
    latticePoint M σ = Quotient.mk _ g := by
  have H : ∃ g : G n, rowLattice g.1 = normalizedLattice M σ := ⟨g, hg⟩
  unfold latticePoint
  rw [dite_eq_left H]
  exact (quotient_eq_iff_rowLattice_eq _ _).mpr (H.choose_spec.trans hg.symm)

 

theorem orderedLogSubgroup_le_periodGroup {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d + 1) K)
    (σ : OrderedEmbeddings (d + 1) K) (hn : Module.finrank ℚ K = d + 1)
    (hodd : Odd (d + 1)) :
    (orderedLogSubgroup σ (positiveUnitStabilizer M σ)).toAddSubgroup ≤
      periodGroup (latticePoint M σ) := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := (mem_orderedLogSubgroup σ _ v).mp hv
  have H := (mem_positiveUnitStabilizer M σ u).mp hu
  obtain ⟨g, hg⟩ := exists_SL_normalizedLattice M σ hn hodd
  change orbitMap (latticePoint M σ) (orderedUnitLog σ (Additive.ofMul u)) = _
  rw [latticePoint_eq_of_rowLattice_eq M σ g hg]
  apply (quotient_eq_iff_rowLattice_eq _ _).mpr
  change rowLattice (g.1 * (diagonalFlow (orderedUnitLog σ (Additive.ofMul u))).1) = _
  rw [diagonalFlow_orderedUnitLog σ u H.2, rowLattice_mul_diagonal, hg]
  exact normalizedLattice_unit_invariant M σ u H.1

lemma diagonalFlow_injective (d : ℕ) : Function.Injective (@diagonalFlow d) := by
  intro u v huv
  ext i
  apply Real.exp_injective
  have h := congrArg (fun g : G (d + 1) => g.1 i.castSucc i.castSucc) huv
  simpa [diagonalFlow] using h

lemma continuous_diagonalFlow (d : ℕ) : Continuous (@diagonalFlow d) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun u : LogCoordinates d =>
    Matrix.diagonal (Fin.snoc (fun i => Real.exp (u i)) (Real.exp (-∑ i, u i))) i j)
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp only [Fin.snoc_last]
      exact Real.continuous_exp.comp (continuous_finsetSum _ (fun i _ => continuous_apply i)).neg
    · simp only [Fin.snoc_castSucc]
      exact Real.continuous_exp.comp (continuous_apply k)
  · simp only [Matrix.diagonal_apply_ne _ hij]
    exact continuous_const

lemma continuous_orbitMap {d : ℕ} (x : X (d + 1)) : Continuous (orbitMap x) := by
  induction x using Quotient.inductionOn with
  | h g =>
    change Continuous (fun u => (Quotient.mk _ (g * diagonalFlow u) : X (d + 1)))
    exact continuous_quotient_mk'.comp (continuous_const.mul (continuous_diagonalFlow d))

 

instance periodGroup_discrete {d : ℕ} (x : X (d + 1)) : DiscreteTopology (periodGroup x) := by
  induction x using Quotient.inductionOn with
  | h g =>
    let f : periodGroup (Quotient.mk _ g : X (d + 1)) → integralGroup (d + 1) := fun u =>
      ⟨g * (g * diagonalFlow u.1)⁻¹, by
        have hu := u.property
        change (Quotient.mk _ (g * diagonalFlow u.1) : X (d + 1)) = Quotient.mk _ g at hu
        have H := Quotient.exact hu
        change (QuotientGroup.rightRel (integralGroup (d + 1))) (g * diagonalFlow u.1) g at H
        exact QuotientGroup.rightRel_apply.mp H⟩
    let : DiscreteTopology (integralGroup (d + 1)) := by unfold integralGroup; infer_instance
    apply DiscreteTopology.of_continuous_injective (f := f)
    · apply Continuous.subtype_mk
      exact continuous_const.mul (continuous_const.mul
        ((continuous_diagonalFlow d).comp continuous_subtype_val)).inv
    · intro u v huv
      apply Subtype.ext
      apply diagonalFlow_injective d
      apply mul_left_cancel (a := g)
      apply inv_injective
      exact mul_left_cancel (congrArg Subtype.val huv)

instance periodSubmodule_discrete {d : ℕ} (x : X (d + 1)) :
    DiscreteTopology (periodGroup x).toIntSubmodule :=
  inferInstanceAs (DiscreteTopology (periodGroup x))

 

theorem periodGroup_hasFundamentalDomain {d : ℕ} (x : X (d + 1))
    [IsZLattice ℝ (periodGroup x).toIntSubmodule] :
    HasAddFundamentalDomain (periodGroup x) (LogCoordinates d) volume := by
  let L := (periodGroup x).toIntSubmodule
  have : DiscreteTopology L := inferInstanceAs (DiscreteTopology (periodGroup x))
  let b := Module.Free.chooseBasis ℤ L
  exact (ZLattice.isAddFundamentalDomain b volume).hasAddFundamentalDomain volume

 

theorem orbitVolume_ne_zero_ne_top {d : ℕ} (x : X (d + 1))
    [IsZLattice ℝ (periodGroup x).toIntSubmodule] : orbitVolume x ≠ 0 ∧ orbitVolume x ≠ ⊤ := by
  let L := (periodGroup x).toIntSubmodule
  have : DiscreteTopology L := inferInstanceAs (DiscreteTopology (periodGroup x))
  have h := ZLattice.covolume_ne_zero L volume
  change (orbitVolume x).toReal ≠ 0 at h
  exact ENNReal.toReal_ne_zero.mp h

lemma orbitalHaar_univ {d : ℕ} (x : X (d + 1))
    (h : HasAddFundamentalDomain (periodGroup x) (LogCoordinates d) volume) :
    orbitalHaar x Set.univ = orbitVolume x := by
  simp only [orbitalHaar, dite_eq_left h]
  rw [Measure.map_apply (continuous_orbitMap x).measurable MeasurableSet.univ]
  simp only [Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  change _ = addCovolume (periodGroup x) (LogCoordinates d) volume
  simp only [addCovolume, dite_eq_left h]

 

theorem orbitProbability_isProbabilityMeasure {d : ℕ} (x : X (d + 1))
    [IsZLattice ℝ (periodGroup x).toIntSubmodule] : IsProbabilityMeasure (orbitProbability x) := by
  constructor
  rw [orbitProbability, Measure.smul_apply, smul_eq_mul,
    orbitalHaar_univ x (periodGroup_hasFundamentalDomain x)]
  exact ENNReal.inv_mul_cancel (orbitVolume_ne_zero_ne_top x).1 (orbitVolume_ne_zero_ne_top x).2

 

theorem latticePoint_period_isZLattice {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d + 1) K)
    (σ : OrderedEmbeddings (d + 1) K) (hn : Module.finrank ℚ K = d + 1)
    (hodd : Odd (d + 1)) : IsZLattice ℝ (periodGroup (latticePoint M σ)).toIntSubmodule := by
  let L := orderedLogSubgroup σ (positiveUnitStabilizer M σ)
  let : IsZLattice ℝ L := (positiveStabilizer_fullLogLattice M σ).2
  constructor
  apply top_unique
  rw [← IsZLattice.span_top (K := ℝ) (L := L)]
  apply Submodule.span_mono
  exact orderedLogSubgroup_le_periodGroup M σ hn hodd

 

theorem latticePoint_diagonalOrbit_isCompact {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d + 1) K)
    (σ : OrderedEmbeddings (d + 1) K) (hn : Module.finrank ℚ K = d + 1)
    (hodd : Odd (d + 1)) : IsCompact (diagonalOrbit (latticePoint M σ)) := by
  let := latticePoint_period_isZLattice M σ hn hodd
  apply IsZLattice.isCompact_range_of_periodic (periodGroup (latticePoint M σ)).toIntSubmodule
    (orbitMap (latticePoint M σ)) (continuous_orbitMap _)
  intro z w hw
  change orbitMap (latticePoint M σ) w = latticePoint M σ at hw
  rw [add_comm z w, orbitMap_add, hw]

 

theorem latticePoint_orbitProbability {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d + 1) K)
    (σ : OrderedEmbeddings (d + 1) K) (hn : Module.finrank ℚ K = d + 1)
    (hodd : Odd (d + 1)) : IsProbabilityMeasure (orbitProbability (latticePoint M σ)) := by
  let := latticePoint_period_isZLattice M σ hn hodd
  exact orbitProbability_isProbabilityMeasure _

lemma continuous_rightAction {n : ℕ} (g : G n) :
    Continuous (fun x : X n => rightAction x g) := by
  apply continuous_quot_lift
  exact continuous_quotient_mk'.comp (continuous_id.mul continuous_const)

lemma rightAction_injective {n : ℕ} (g : G n) :
    Function.Injective (fun x : X n => rightAction x g) := by
  intro x y h
  have := congrArg (fun z => rightAction z g⁻¹) h
  simpa using this

lemma diagonalFlow_commute_of_diagonal {d : ℕ} (g : G (d + 1))
    (hg : ∀ i j, i ≠ j → g.1 i j = 0) (u : LogCoordinates d) :
    g * diagonalFlow u = diagonalFlow u * g := by
  apply Subtype.ext
  change g.1 * Matrix.diagonal _ = Matrix.diagonal _ * g.1
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : i = j
  · subst j; exact mul_comm _ _
  · simp [hg i j h]

lemma orbitMap_rightAction_of_diagonal {d : ℕ} (x : X (d + 1)) (g : G (d + 1))
    (hg : ∀ i j, i ≠ j → g.1 i j = 0) (u : LogCoordinates d) :
    orbitMap (rightAction x g) u = rightAction (orbitMap x u) g := by
  simp only [orbitMap, rightAction_mul, diagonalFlow_commute_of_diagonal g hg u]

lemma periodGroup_rightAction_of_diagonal {d : ℕ} (x : X (d + 1)) (g : G (d + 1))
    (hg : ∀ i j, i ≠ j → g.1 i j = 0) :
    periodGroup (rightAction x g) = periodGroup x := by
  ext u
  change orbitMap (rightAction x g) u = rightAction x g ↔ orbitMap x u = x
  rw [orbitMap_rightAction_of_diagonal x g hg u]
  exact (rightAction_injective g).eq_iff

lemma periodGroup_orbitMap {d : ℕ} (x : X (d + 1)) (u : LogCoordinates d) :
    periodGroup (orbitMap x u) = periodGroup x := by
  apply periodGroup_rightAction_of_diagonal
  intro i j hij
  exact Matrix.diagonal_apply_ne _ hij

lemma mem_diagonalOrbit_self {d : ℕ} (x : X (d + 1)) : x ∈ diagonalOrbit x :=
  ⟨0, orbitMap_zero x⟩

lemma periodGroup_eq_of_diagonalOrbit_eq {d : ℕ} {x y : X (d + 1)}
    (h : diagonalOrbit x = diagonalOrbit y) : periodGroup x = periodGroup y := by
  have hx := mem_diagonalOrbit_self x
  rw [h] at hx
  obtain ⟨u, rfl⟩ := hx
  exact periodGroup_orbitMap y u

lemma diagonalOrbit_orbitMap {d : ℕ} (x : X (d + 1)) (u : LogCoordinates d) :
    diagonalOrbit (orbitMap x u) = diagonalOrbit x := by
  apply Set.Subset.antisymm
  · rintro _ ⟨v, rfl⟩
    exact ⟨u + v, orbitMap_add x u v⟩
  · rintro _ ⟨v, rfl⟩
    refine ⟨-u + v, ?_⟩
    rw [← orbitMap_add, ← add_assoc, add_neg_cancel, zero_add]

lemma diagonalOrbit_rightAction_of_diagonal {d : ℕ} (x : X (d + 1)) (g : G (d + 1))
    (hg : ∀ i j, i ≠ j → g.1 i j = 0) :
    diagonalOrbit (rightAction x g) = (fun y => rightAction y g) '' diagonalOrbit x := by
  ext y
  simp only [diagonalOrbit, Set.mem_range, Set.mem_image]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨orbitMap x u, ⟨u, rfl⟩, (orbitMap_rightAction_of_diagonal x g hg u).symm⟩
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, orbitMap_rightAction_of_diagonal x g hg u⟩

lemma orbitVolume_eq_of_diagonalOrbit_eq {d : ℕ} {x y : X (d + 1)}
    (h : diagonalOrbit x = diagonalOrbit y) : orbitVolume x = orbitVolume y := by
  unfold orbitVolume
  rw [periodGroup_eq_of_diagonalOrbit_eq h]

 

lemma map_orbitMap_restrict_eq {d : ℕ} (x : X (d + 1))
    {s t : Set (LogCoordinates d)}
    (hs : IsAddFundamentalDomain (periodGroup x) s volume)
    (ht : IsAddFundamentalDomain (periodGroup x) t volume) :
    Measure.map (orbitMap x) (volume.restrict s) =
      Measure.map (orbitMap x) (volume.restrict t) := by
  have : Countable (periodGroup x) := countable_of_Lindelof_of_discrete
  ext A hA
  rw [Measure.map_apply (continuous_orbitMap x).measurable hA,
    Measure.map_apply (continuous_orbitMap x).measurable hA,
    Measure.restrict_apply (hA.preimage (continuous_orbitMap x).measurable),
    Measure.restrict_apply (hA.preimage (continuous_orbitMap x).measurable)]
  apply hs.measure_set_eq ht (hA.preimage (continuous_orbitMap x).measurable)
  intro u
  ext v
  change orbitMap x (u.1 + v) ∈ A ↔ orbitMap x v ∈ A
  rw [orbitMap_add, (show orbitMap x u.1 = x from u.property)]

lemma map_orbitMap_add_restrict_eq {d : ℕ} (x : X (d + 1))
    {s : Set (LogCoordinates d)}
    (hs : IsAddFundamentalDomain (periodGroup x) s volume) (u : LogCoordinates d) :
    Measure.map (fun v => orbitMap x (u + v)) (volume.restrict s) =
      Measure.map (orbitMap x) (volume.restrict s) := by
  have htrans := (measurePreserving_add_left (volume : Measure (LogCoordinates d)) u).restrict_image_emb (MeasurableEquiv.addLeft u).measurableEmbedding s
  have ht : IsAddFundamentalDomain (periodGroup x) ((fun v => u + v) '' s) volume :=
    hs.vadd_of_comm u
  calc
    _ = Measure.map (orbitMap x)
        (Measure.map (fun v => u + v) (volume.restrict s)) := by
      have ha : Measurable (fun v : LogCoordinates d => u + v) :=
        measurable_const.add measurable_id
      exact (Measure.map_map (continuous_orbitMap x).measurable ha).symm
    _ = Measure.map (orbitMap x) (volume.restrict ((fun v => u + v) '' s)) := by
      rw [htrans.map_eq]
    _ = _ := map_orbitMap_restrict_eq x ht hs

 

theorem orbitalHaar_invariant {d : ℕ} (x : X (d + 1)) (u : LogCoordinates d) :
    Measure.map (fun y => orbitMap y u) (orbitalHaar x) = orbitalHaar x := by
  have hmu : Measurable (fun y => orbitMap y u) :=
    (continuous_rightAction (diagonalFlow u)).measurable
  unfold orbitalHaar
  split_ifs with h
  · rw [Measure.map_map hmu
      (continuous_orbitMap x).measurable]
    have H : (fun y => orbitMap y u) ∘ orbitMap x = fun v => orbitMap x (u + v) := by
      funext v
      rw [Function.comp_apply, ← orbitMap_add, add_comm v u]
    rw [H]
    exact map_orbitMap_add_restrict_eq x h.ExistsIsAddFundamentalDomain.choose_spec u
  · simp

 

theorem orbitProbability_invariant {d : ℕ} (x : X (d + 1)) (u : LogCoordinates d) :
    Measure.map (fun y => orbitMap y u) (orbitProbability x) = orbitProbability x := by
  have hmeas : Measurable (fun y => orbitMap y u) :=
    (continuous_rightAction (diagonalFlow u)).measurable
  simp only [orbitProbability, Measure.map_smul _ hmeas.aemeasurable, orbitalHaar_invariant]

theorem orbitalHaar_orbitMap {d : ℕ} (x : X (d + 1)) (u : LogCoordinates d) :
    orbitalHaar (orbitMap x u) = orbitalHaar x := by
  have H : orbitMap (orbitMap x u) = fun v => orbitMap x (u + v) := by
    funext v
    exact (orbitMap_add x u v).symm
  by_cases hx : HasAddFundamentalDomain (periodGroup x) (LogCoordinates d) volume
  · have hy : HasAddFundamentalDomain (periodGroup (orbitMap x u)) (LogCoordinates d) volume := by
      rw [periodGroup_orbitMap]
      exact hx
    rw [orbitalHaar, dite_eq_left hy, orbitalHaar, dite_eq_left hx, H]
    have hs : IsAddFundamentalDomain (periodGroup x) hy.ExistsIsAddFundamentalDomain.choose volume := by
      have transport (P Q : AddSubgroup (LogCoordinates d)) (h : P = Q)
          (s : Set (LogCoordinates d)) : IsAddFundamentalDomain P s volume →
            IsAddFundamentalDomain Q s volume := by
        subst Q
        exact id
      exact transport _ _ (periodGroup_orbitMap x u) _ hy.ExistsIsAddFundamentalDomain.choose_spec
    exact (map_orbitMap_add_restrict_eq x hs u).trans
      (map_orbitMap_restrict_eq x hs hx.ExistsIsAddFundamentalDomain.choose_spec)
  · have hy : ¬ HasAddFundamentalDomain (periodGroup (orbitMap x u)) (LogCoordinates d) volume := by
      rwa [periodGroup_orbitMap]
    rw [orbitalHaar, dite_eq_right hy, orbitalHaar, dite_eq_right hx]

 

theorem orbitalHaar_eq_of_diagonalOrbit_eq {d : ℕ} {x y : X (d + 1)}
    (h : diagonalOrbit x = diagonalOrbit y) : orbitalHaar x = orbitalHaar y := by
  have hx := mem_diagonalOrbit_self x
  rw [h] at hx
  obtain ⟨u, rfl⟩ := hx
  exact orbitalHaar_orbitMap y u

theorem orbitProbability_eq_of_diagonalOrbit_eq {d : ℕ} {x y : X (d + 1)}
    (h : diagonalOrbit x = diagonalOrbit y) : orbitProbability x = orbitProbability y := by
  simp only [orbitProbability, orbitalHaar_eq_of_diagonalOrbit_eq h,
    orbitVolume_eq_of_diagonalOrbit_eq h]

 

lemma locallyHomothetic_refl {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : LocallyHomothetic M M := by
  intro p hp
  exact ⟨1, by simp⟩

lemma one_mem_signMatrices (n : ℕ) : (1 : G n) ∈ signMatrices n := by
  constructor
  · intro i j hij
    exact Matrix.one_apply_ne hij
  · intro i
    exact Or.inl (Matrix.one_apply_eq i)

lemma packetOrbits_nonempty {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d + 1) K) (σ : OrderedEmbeddings (d + 1) K) :
    (packetOrbits M σ).Nonempty := by
  refine ⟨diagonalOrbit (latticePoint M σ), M, locallyHomothetic_refl M,
    1, one_mem_signMatrices _, ?_⟩
  rw [rightAction_one]

lemma orbitBasepoint_spec {d : ℕ} {K : Type*} [Field K] [NumberField K]
    {M : FullLattice (d + 1) K} {σ : OrderedEmbeddings (d + 1) K}
    (O : packetOrbits M σ) : diagonalOrbit (orbitBasepoint O) = O.1 := by
  unfold orbitBasepoint
  refine Classical.epsilon_spec (p := fun x : X (d + 1) => diagonalOrbit x = O.1) ?_
  obtain ⟨M', _, w, _, hO⟩ := O.property
  exact ⟨rightAction (latticePoint M' σ) w, hO.symm⟩

 

theorem packetOrbit_isCompact {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {M : FullLattice (d + 1) K}
    {σ : OrderedEmbeddings (d + 1) K} (hn : Module.finrank ℚ K = d + 1)
    (hodd : Odd (d + 1)) (O : packetOrbits M σ) : IsCompact O.1 := by
  obtain ⟨M', _, w, hw, hO⟩ := O.property
  rw [hO, diagonalOrbit_rightAction_of_diagonal _ _ hw.1]
  exact (latticePoint_diagonalOrbit_isCompact M' σ hn hodd).image (continuous_rightAction w)

 

theorem packetBasepoint_period_isZLattice {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {M : FullLattice (d + 1) K}
    {σ : OrderedEmbeddings (d + 1) K} (hn : Module.finrank ℚ K = d + 1)
    (hodd : Odd (d + 1)) (O : packetOrbits M σ) :
    IsZLattice ℝ (periodGroup (orbitBasepoint O)).toIntSubmodule := by
  obtain ⟨M', _, w, hw, hO⟩ := O.property
  have heq := periodGroup_eq_of_diagonalOrbit_eq ((orbitBasepoint_spec O).trans hO)
  rw [periodGroup_rightAction_of_diagonal _ _ hw.1] at heq
  constructor
  change Submodule.span ℝ (↑(periodGroup (orbitBasepoint O)) : Set (LogCoordinates d)) = ⊤
  rw [heq]
  exact (latticePoint_period_isZLattice M' σ hn hodd).span_top

theorem packetBasepoint_volume_pos_finite {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {M : FullLattice (d + 1) K}
    {σ : OrderedEmbeddings (d + 1) K} (hn : Module.finrank ℚ K = d + 1)
    (hodd : Odd (d + 1)) (O : packetOrbits M σ) :
    orbitVolume (orbitBasepoint O) ≠ 0 ∧ orbitVolume (orbitBasepoint O) ≠ ⊤ := by
  let := packetBasepoint_period_isZLattice hn hodd O
  exact orbitVolume_ne_zero_ne_top _

theorem packetBasepoint_probability {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {M : FullLattice (d + 1) K}
    {σ : OrderedEmbeddings (d + 1) K} (hn : Module.finrank ℚ K = d + 1)
    (hodd : Odd (d + 1)) (O : packetOrbits M σ) :
    IsProbabilityMeasure (orbitProbability (orbitBasepoint O)) := by
  let := packetBasepoint_period_isZLattice hn hodd O
  exact orbitProbability_isProbabilityMeasure _

 

theorem packetMeasure_invariant {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d + 1) K) (σ : OrderedEmbeddings (d + 1) K)
    (u : LogCoordinates d) :
    Measure.map (fun x => orbitMap x u) (packetMeasure M σ) = packetMeasure M σ := by
  have hm : Measurable (fun x => orbitMap x u) :=
    (continuous_rightAction (diagonalFlow u)).measurable
  simp only [packetMeasure, Measure.map_smul _ hm.aemeasurable, Measure.map_sum hm.aemeasurable, orbitProbability_invariant]

lemma completedLattice_mul_mem {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) {a : K} (ha : a ∈ multiplierOrder M)
    (p : ℕ) [Fact p.Prime] {z : LocalAlgebra p K} (hz : z ∈ completedLattice p M) :
    Algebra.TensorProduct.includeRight (R := ℚ) (A := Padic p) a * z ∈ completedLattice p M := by
  induction hz using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      rw [← map_mul]
      exact Submodule.subset_span ⟨a * b, ha b hb, rfl⟩
  | zero => simp
  | add x y hx hy ihx ihy => simpa [mul_add] using (completedLattice p M).add_mem ihx ihy
  | smul c x hx ih =>
      simpa only [mul_smul_comm] using (completedLattice p M).smul_mem c ih

 

theorem multiplierOrder_eq_of_locallyHomothetic {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (hn : Module.finrank ℚ K = n) (hMN : LocallyHomothetic M N) :
    multiplierOrder M = multiplierOrder N := by
  ext a
  constructor
  · intro ha x hx
    apply (mem_fullLattice_iff_forall_completed N hn (a * x)).mpr
    intro p hp
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨c, hc⟩ := hMN p hp
    have hx' : Algebra.TensorProduct.includeRight (R := ℚ) (A := Padic p) x ∈
        (completedLattice p N : Set (LocalAlgebra p K)) :=
      Submodule.subset_span ⟨x, hx, rfl⟩
    rw [hc] at hx'
    obtain ⟨z, hz, heq⟩ := hx'
    rw [map_mul]
    change _ ∈ (completedLattice p N : Set (LocalAlgebra p K))
    rw [hc]
    refine ⟨Algebra.TensorProduct.includeRight (R := ℚ) (A := Padic p) a * z,
      completedLattice_mul_mem M ha p hz, ?_⟩
    rw [← heq]
    ring
  · intro ha x hx
    apply (mem_fullLattice_iff_forall_completed M hn (a * x)).mpr
    intro p hp
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨c, hc⟩ := hMN p hp
    have hx' : (c : LocalAlgebra p K) * Algebra.TensorProduct.includeRight (R := ℚ) (A := Padic p) x ∈
        completedLattice p N := by
      change _ ∈ (completedLattice p N : Set (LocalAlgebra p K))
      rw [hc]
      exact ⟨_, Submodule.subset_span ⟨x, hx, rfl⟩, rfl⟩
    have H := completedLattice_mul_mem N ha p hx'
    change _ ∈ (completedLattice p N : Set (LocalAlgebra p K)) at H
    rw [hc] at H
    obtain ⟨z, hz, heq⟩ := H
    have hz' : z = Algebra.TensorProduct.includeRight (R := ℚ) (A := Padic p) (a * x) := by
      apply (Units.isUnit c).mul_left_cancel
      rw [map_mul]
      change (c : LocalAlgebra p K) * z = _ at heq
      rw [heq]
      ring
    rwa [← hz']

theorem uniform_saturation_denominator {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (hn : Module.finrank ℚ K = n) (hMN : LocallyHomothetic M N)
    {x : K} (hx : x ∈ saturation N) : saturationIndex M • x ∈ N.carrier := by
  have horder := multiplierOrder_eq_of_locallyHomothetic M N hn hMN
  have hmult (r : 𝓞 K) : saturationIndex M • (r : K) ∈ multiplierOrder N := by
    rw [← horder]
    apply scaled_integralElements_le_multiplierOrder M
    exact ⟨r, r.property, rfl⟩
  have H : ∀ r : 𝓞 K, (saturationIndex M • (r : K)) * x ∈ N.carrier := by
    change x ∈ Submodule.span (𝓞 K) (N.carrier : Set K) at hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact fun r => hmult r y hy
    | zero => simp
    | add y z hy hz ihy ihz =>
      intro r
      rw [mul_add]
      exact N.carrier.add_mem (ihy r) (ihz r)
    | smul a y hy ih =>
      intro r
      simpa [Algebra.smul_def, nsmul_eq_mul, mul_assoc] using ih (r * a)
  simpa using H 1

open scoped Pointwise

 

theorem finite_submodules_between {K : Type*} [Field K] [NumberField K]
    (J : Submodule ℤ K) (hJ : J.FG) (q : ℕ) (hq : q ≠ 0) :
    {N : Submodule ℤ K | (q : ℤ) • J ≤ N ∧ N ≤ J}.Finite := by
  let : Module.Finite ℤ J := Module.Finite.iff_fg.mpr hJ
  let A : Submodule ℤ J := (q : ℤ) • (⊤ : Submodule ℤ J)
  have ht : Module.IsTorsion ℤ (J ⧸ A) := by
    intro x
    refine ⟨⟨(q : ℤ), mem_nonZeroDivisors_iff_ne_zero.mpr (by exact_mod_cast hq)⟩, ?_⟩
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      change (q : ℤ) • x ∈ (q : ℤ) • (⊤ : Submodule ℤ J)
      exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨x, Submodule.mem_top, rfl⟩
  let : Finite (J ⧸ A) := Module.finite_of_fg_torsion _ ht
  let : Finite (Set.Ici A) := Finite.of_equiv (Submodule ℤ (J ⧸ A)) A.comapMkQRelIso.toEquiv
  let f : {N : Submodule ℤ K | (q : ℤ) • J ≤ N ∧ N ≤ J} → Set.Ici A := fun N =>
    ⟨N.1.comap J.subtype, by
      intro x hx
      change x ∈ (q : ℤ) • (⊤ : Submodule ℤ J) at hx
      obtain ⟨y, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
      exact N.property.1 ((Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
        ⟨(y : K), y.property, rfl⟩)⟩
  apply Set.finite_coe_iff.mp
  apply Finite.of_injective f
  intro N P h
  apply Subtype.ext
  have hc : N.1.comap J.subtype = P.1.comap J.subtype := congrArg Subtype.val h
  have hm := congrArg (Submodule.map J.subtype) hc
  simpa only [Submodule.map_comap_subtype, inf_eq_right.mpr N.property.2,
    inf_eq_right.mpr P.property.2] using hm

 

theorem finite_packet_labels {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (J : Submodule ℤ K)
    (hJ : J.FG) :
    {P : Submodule ℤ K | ∃ N : FullLattice n K,
      LocallyHomothetic M N ∧ saturation N = J ∧ N.carrier = P}.Finite := by
  apply (finite_submodules_between J hJ (saturationIndex M) (saturationIndex_ne_zero M)).subset
  rintro P ⟨N, hMN, rfl, rfl⟩
  refine ⟨?_, le_saturation N⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
  simpa using uniform_saturation_denominator M N hn hMN hy

open FractionalIdeal

 

theorem fractionalIdeal_same_class {R K : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (I J : (FractionalIdeal R⁰ K)ˣ) :
    ClassGroup.mk K I = ClassGroup.mk K J ↔
      ∃ x : K, x ≠ 0 ∧ FractionalIdeal.spanSingleton R⁰ x * (I : FractionalIdeal R⁰ K) = J := by
  refine (ClassGroup.equiv K).injective.eq_iff.symm.trans ?_
  simp only [ClassGroup.equiv_mk, FractionalIdeal.canonicalEquiv_self,
    Units.coe_mapEquiv, RingEquiv.coe_toMulEquiv, RingEquiv.refl_apply,
    QuotientGroup.mk'_eq_mk', mem_principal_ideals_iff, Units.ext_iff, Units.val_mul,
    Units.coe_mapEquiv, RingEquiv.coe_toMulEquiv, RingEquiv.refl_apply]
  constructor
  · rintro ⟨X, ⟨x, hX⟩, hx⟩
    refine ⟨x, ?_, ?_⟩
    · rintro rfl
      simp [X.ne_zero.symm] at hX
    · simpa only [hX, mul_comm] using hx
  · rintro ⟨x, hx, heq⟩
    refine ⟨toPrincipalIdeal R K (Units.mk0 x hx), ⟨x, by simp⟩, ?_⟩
    simpa only [coe_toPrincipalIdeal, Units.val_mk0, mul_comm] using heq

 

def classRepresentative (K : Type*) [Field K] [NumberField K]
    (c : ClassGroup (𝓞 K)) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Classical.choose (show ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ClassGroup.mk K I = c from
    ClassGroup.induction K (fun I => ⟨I, rfl⟩) c)

lemma classRepresentative_spec (K : Type*) [Field K] [NumberField K]
    (c : ClassGroup (𝓞 K)) : ClassGroup.mk K (classRepresentative K c) = c :=
  by
    exact Classical.choose_spec
      (show ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ClassGroup.mk K I = c from
        ClassGroup.induction K (fun I => ⟨I, rfl⟩) c)

 

theorem exists_scale_to_classRepresentative (K : Type*) [Field K] [NumberField K]
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    ∃ c : ClassGroup (𝓞 K), ∃ x : K, x ≠ 0 ∧
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x * I = classRepresentative K c := by
  let U := Units.mk0 I hI
  let c := ClassGroup.mk K U
  have heq : ClassGroup.mk K U = ClassGroup.mk K (classRepresentative K c) := by
    rw [classRepresentative_spec]
  exact ⟨c, (fractionalIdeal_same_class U (classRepresentative K c)).mp heq⟩

 

lemma locallyHomothetic_scale {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (a : Kˣ) : LocallyHomothetic M (scaleFullLattice M a) := by
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  refine ⟨Units.map (Algebra.TensorProduct.includeRight (R := ℚ) (A := Padic p)).toMonoidHom a, ?_⟩
  rw [completedLattice_scale]
  rfl

lemma locallyHomothetic_trans {n : ℕ} {K : Type*} [Field K] [NumberField K]
    {M N P : FullLattice n K} (hMN : LocallyHomothetic M N) (hNP : LocallyHomothetic N P) :
    LocallyHomothetic M P := by
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := hMN p hp
  obtain ⟨b, hb⟩ := hNP p hp
  refine ⟨b * a, ?_⟩
  rw [hb, ha, Set.image_image]
  congr 1
  ext x
  exact (mul_assoc _ _ _).symm

lemma saturationFractionalIdeal_scale {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (a : Kˣ) :
    saturationFractionalIdeal (scaleFullLattice M a) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K) * saturationFractionalIdeal M := by
  apply FractionalIdeal.coeToSubmodule_injective
  dsimp only
  rw [FractionalIdeal.coe_mul, FractionalIdeal.coe_spanSingleton, Submodule.span_singleton_mul]
  change Submodule.span (𝓞 K) (((scaleFullLattice M a).carrier : Set K)) =
    (a : K) • Submodule.span (𝓞 K) (M.carrier : Set K)
  rw [scaleFullLattice_carrier]
  change Submodule.span (𝓞 K) ((LinearMap.mulLeft (𝓞 K) (a : K)) '' (M.carrier : Set K)) = _
  rw [← Submodule.map_span]
  rfl

 

theorem exists_scale_to_representative {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : ∃ a : Kˣ, ∃ c : ClassGroup (𝓞 K),
      saturationFractionalIdeal (scaleFullLattice M a) = classRepresentative K c := by
  obtain ⟨c, x, hx, he⟩ := exists_scale_to_classRepresentative K
    (saturationFractionalIdeal M) (saturationFractionalIdeal_ne_zero M)
  refine ⟨Units.mk0 x hx, c, ?_⟩
  rw [saturationFractionalIdeal_scale]
  exact he

 

theorem finite_normalized_packet_carriers {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) :
    {P : Submodule ℤ K | ∃ N : FullLattice n K, LocallyHomothetic M N ∧
      (∃ c : ClassGroup (𝓞 K), saturationFractionalIdeal N = classRepresentative K c) ∧
      N.carrier = P}.Finite := by
  let J : ClassGroup (𝓞 K) → Submodule ℤ K := fun c =>
    (((classRepresentative K c : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K).restrictScalars ℤ
  have hJ (c : ClassGroup (𝓞 K)) : (J c).FG :=
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl
      ((classRepresentative K c : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)).restrictScalars
  apply (Set.finite_iUnion fun c => finite_packet_labels M hn (J c) (hJ c)).subset
  rintro P ⟨N, hMN, ⟨c, hc⟩, rfl⟩
  apply Set.mem_iUnion.mpr
  refine ⟨c, N, hMN, ?_, rfl⟩
  exact congrArg (fun I : FractionalIdeal (𝓞 K)⁰ K =>
    (I : Submodule (𝓞 K) K).restrictScalars ℤ) hc

 

lemma abs_det_le_of_rowLattice_le {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.det ≠ 0) (hBC : rowLattice B ≤ rowLattice C) : |C.det| ≤ |B.det| := by
  obtain ⟨A, hA⟩ := exists_int_matrix_of_rowLattice_le B C hBC
  have hd : B.det = (A.det : ℝ) * C.det := by
    rw [hA, Matrix.det_mul]
    congr 1
    exact (Int.castRingHom ℝ).map_det A |>.symm
  have hA0 : A.det ≠ 0 := by
    intro h
    rw [h, Int.cast_zero, zero_mul] at hd
    exact hB hd
  have hone : (1 : ℝ) ≤ |(A.det : ℝ)| := by exact_mod_cast Int.one_le_abs hA0
  rw [hd, abs_mul]
  nlinarith [abs_nonneg C.det]

lemma abs_det_eq_of_rowLattice_eq {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.det ≠ 0) (hC : C.det ≠ 0) (hBC : rowLattice B = rowLattice C) :
    |B.det| = |C.det| :=
  le_antisymm (abs_det_le_of_rowLattice_le C B hC hBC.ge)
    (abs_det_le_of_rowLattice_le B C hB hBC.le)

 

theorem normalizedLattice_eq_of_carrier_eq {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n)
    (hMN : M.carrier = N.carrier) : normalizedLattice M σ = normalizedLattice N σ := by
  have hrow : rowLattice (embeddingMatrix M σ) = rowLattice (embeddingMatrix N σ) := by
    rw [rowLattice_embeddingMatrix, rowLattice_embeddingMatrix, hMN]
  have hdet := abs_det_eq_of_rowLattice_eq _ _ (embeddingMatrix_det_ne_zero M σ hn)
    (embeddingMatrix_det_ne_zero N σ hn) hrow
  dsimp only [normalizedLattice]
  rw [rowLattice_smul, rowLattice_smul, hdet, hrow]

 

theorem latticePoint_eq_of_carrier_eq {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n)
    (hodd : Odd n) (hMN : M.carrier = N.carrier) : latticePoint M σ = latticePoint N σ := by
  obtain ⟨g, hg⟩ := exists_SL_normalizedLattice M σ hn hodd
  have hgN : rowLattice g.1 = normalizedLattice N σ :=
    hg.trans (normalizedLattice_eq_of_carrier_eq M N σ hn hMN)
  rw [latticePoint_eq_of_rowLattice_eq M σ g hg, latticePoint_eq_of_rowLattice_eq N σ g hgN]

 

theorem normalizedLattice_scale_diagonal {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n)
    (hpos : 0 < n) (a : Kˣ) :
    ∃ t : Fin n → ℝ, |(Matrix.diagonal t).det| = 1 ∧
      normalizedLattice (scaleFullLattice M a) σ =
        (normalizedLattice M σ).map (diagonalLinear n t) := by
  let B := embeddingMatrix M σ
  let C := embeddingMatrix (scaleFullLattice M a) σ
  let b : ℝ := |B.det| ^ (-(1 : ℝ) / n)
  let c : ℝ := |C.det| ^ (-(1 : ℝ) / n)
  have hb : b ≠ 0 := (Real.rpow_pos_of_pos
    (abs_pos.mpr (embeddingMatrix_det_ne_zero M σ hn)) _).ne'
  let t : Fin n → ℝ := fun i => c / b * σ i (a : K)
  have he : c • C = (b • B) * Matrix.diagonal t := by
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    change c * σ j ((scaleFullLattice M a).basis i : K) =
      b * σ j (M.basis i : K) * (c / b * σ j (a : K))
    rw [scaleFullLattice_basis, map_mul]
    field_simp [hb]
  have hdB : |(b • B).det| = 1 := normalizedMatrix_abs_det B hpos
    (embeddingMatrix_det_ne_zero M σ hn)
  have hdC : |(c • C).det| = 1 := normalizedMatrix_abs_det C hpos
    (embeddingMatrix_det_ne_zero (scaleFullLattice M a) σ hn)
  rw [he, Matrix.det_mul, abs_mul, hdB, one_mul] at hdC
  refine ⟨t, hdC, ?_⟩
  change rowLattice (c • C) = (rowLattice (b • B)).map (diagonalLinear n t)
  rw [he, rowLattice_mul_diagonal]

 

theorem latticePoint_scale_diagonal {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n)
    (hodd : Odd n) (a : Kˣ) :
    ∃ D : G n, (∀ i j, i ≠ j → D.1 i j = 0) ∧
      latticePoint (scaleFullLattice M a) σ = rightAction (latticePoint M σ) D := by
  obtain ⟨t, hdet, ht⟩ := normalizedLattice_scale_diagonal M σ hn hodd.pos a
  obtain ⟨g, hg⟩ := exists_SL_normalizedLattice M σ hn hodd
  have hrow : rowLattice (g.1 * Matrix.diagonal t) =
      normalizedLattice (scaleFullLattice M a) σ := by
    rw [rowLattice_mul_diagonal, hg, ← ht]
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hdet with hd | hd
  · let D : G n := ⟨Matrix.diagonal t, hd⟩
    refine ⟨D, fun i j hij => Matrix.diagonal_apply_ne _ hij, ?_⟩
    rw [latticePoint_eq_of_rowLattice_eq M σ g hg,
      latticePoint_eq_of_rowLattice_eq (scaleFullLattice M a) σ (g * D) hrow]
    rfl
  · have hneg : (-Matrix.diagonal t).det = 1 := by
      rw [Matrix.det_neg, Fintype.card_fin, hodd.neg_one_pow, hd]
      norm_num
    let D : G n := ⟨-Matrix.diagonal t, hneg⟩
    have hrow' : rowLattice (g * D).1 = normalizedLattice (scaleFullLattice M a) σ := by
      change rowLattice (g.1 * -Matrix.diagonal t) = _
      rw [Matrix.mul_neg, rowLattice_neg, hrow]
    refine ⟨D, ?_, ?_⟩
    · intro i j hij
      change -(Matrix.diagonal t i j) = 0
      rw [Matrix.diagonal_apply_ne _ hij, neg_zero]
    · rw [latticePoint_eq_of_rowLattice_eq M σ g hg,
        latticePoint_eq_of_rowLattice_eq (scaleFullLattice M a) σ (g * D) hrow']
      rfl

 

theorem exists_diagonalFlow_of_positive {d : ℕ} (t : Fin (d + 1) → ℝ)
    (ht : ∀ i, 0 < t i) (hp : ∏ i, t i = 1) :
    ∃ u : LogCoordinates d, (diagonalFlow u).1 = Matrix.diagonal t := by
  let u : LogCoordinates d := fun i => Real.log (t i.castSucc)
  have hsum : ∑ i, Real.log (t i) = 0 := by
    rw [← Real.log_prod (fun i _ => (ht i).ne'), hp, Real.log_one]
  have hlast : Real.log (t (Fin.last d)) = -∑ i, u i := by
    rw [Fin.sum_univ_castSucc] at hsum
    dsimp only [u]
    linarith
  refine ⟨u, ?_⟩
  change Matrix.diagonal _ = Matrix.diagonal t
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last, ← hlast, Real.exp_log (ht _)]
  · simp only [Fin.snoc_castSucc, u, Real.exp_log (ht _)]

 

theorem diagonal_eq_sign_mul_flow {d : ℕ} (g : G (d + 1))
    (hg : ∀ i j, i ≠ j → g.1 i j = 0) :
    ∃ w ∈ signMatrices (d + 1), ∃ u : LogCoordinates d, g = w * diagonalFlow u := by
  have hd : Matrix.diagonal (Matrix.diag g.1) = g.1 :=
    Matrix.IsDiag.diagonal_diag (fun i j hij => hg i j hij)
  let t := Matrix.diag g.1
  have hp : ∏ i, t i = 1 := by rw [← Matrix.det_diagonal, hd]; exact g.property
  have ht0 : ∀ i, t i ≠ 0 := fun i => by
    have H : ∏ i, t i ≠ 0 := by rw [hp]; exact one_ne_zero
    exact (Finset.prod_ne_zero_iff.mp H) i (Finset.mem_univ i)
  have ha : ∏ i, |t i| = 1 := by rw [← Finset.abs_prod, hp, abs_one]
  obtain ⟨u, hu⟩ := exists_diagonalFlow_of_positive (fun i => |t i|)
    (fun i => abs_pos.mpr (ht0 i)) ha
  let w : G (d + 1) := ⟨Matrix.diagonal (fun i => t i / |t i|), by
    rw [Matrix.det_diagonal, Finset.prod_div_distrib, hp, ha, _root_.div_one]⟩
  refine ⟨w, ⟨?_, ?_⟩, u, ?_⟩
  · intro i j hij
    exact Matrix.diagonal_apply_ne _ hij
  · intro i
    change Matrix.diagonal (fun i => t i / |t i|) i i = 1 ∨
      Matrix.diagonal (fun i => t i / |t i|) i i = -1
    simp only [Matrix.diagonal_apply_eq]
    rcases lt_or_gt_of_ne (ht0 i) with h | h
    · right
      rw [abs_of_neg h, div_neg, div_self (ht0 i)]
    · left
      rw [abs_of_pos h, div_self (ht0 i)]
  · apply Subtype.ext
    change g.1 = w.1 * (diagonalFlow u).1
    rw [hu, show w.1 = Matrix.diagonal (fun i => t i / |t i|) from rfl,
      Matrix.diagonal_mul_diagonal]
    rw [← hd]
    congr 1
    funext i
    exact (div_mul_cancel₀ (t i) (abs_ne_zero.mpr (ht0 i))).symm

 

theorem signMatrices_finite (n : ℕ) : (signMatrices n).Finite := by
  let f : signMatrices n → (Fin n → Bool) := fun g i => decide (g.1.1 i i = 1)
  apply Set.finite_coe_iff.mp
  apply Finite.of_injective f
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  by_cases hij : i = j
  · subst j
    have H : decide (g.1.1 i i = 1) = decide (h.1.1 i i = 1) := congrFun he i
    rcases g.property.2 i with hi | hi <;> rcases h.property.2 i with hj | hj
    · exact hi.trans hj.symm
    · norm_num [hi, hj] at H
    · norm_num [hi, hj] at H
    · exact hi.trans hj.symm
  · rw [g.property.1 i j hij, h.property.1 i j hij]

lemma diagonal_inv {n : ℕ} (g : G n) (hg : ∀ i j, i ≠ j → g.1 i j = 0) :
    ∀ i j, i ≠ j → (g⁻¹).1 i j = 0 := by
  have hd : Matrix.diagonal (Matrix.diag g.1) = g.1 :=
    Matrix.IsDiag.diagonal_diag (fun i j hij => hg i j hij)
  intro i j hij
  rw [Matrix.SpecialLinearGroup.coe_inv, ← hd, Matrix.adjugate_diagonal,
    Matrix.diagonal_apply_ne _ hij]

lemma diagonal_mul {n : ℕ} (g h : G n)
    (hg : ∀ i j, i ≠ j → g.1 i j = 0) (hh : ∀ i j, i ≠ j → h.1 i j = 0) :
    ∀ i j, i ≠ j → (g * h).1 i j = 0 := by
  have hdg : Matrix.diagonal (Matrix.diag g.1) = g.1 :=
    Matrix.IsDiag.diagonal_diag (fun i j hij => hg i j hij)
  have hdh : Matrix.diagonal (Matrix.diag h.1) = h.1 :=
    Matrix.IsDiag.diagonal_diag (fun i j hij => hh i j hij)
  intro i j hij
  change (g.1 * h.1) i j = 0
  rw [← hdg, ← hdh, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_ne _ hij]

 

theorem packetOrbits_finite {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d + 1) K) (σ : OrderedEmbeddings (d + 1) K)
    (hn : Module.finrank ℚ K = d + 1) (hodd : Odd (d + 1)) :
    (packetOrbits M σ).Finite := by
  let C := {P : Submodule ℤ K | ∃ N : FullLattice (d + 1) K, LocallyHomothetic M N ∧
    (∃ c : ClassGroup (𝓞 K), saturationFractionalIdeal N = classRepresentative K c) ∧
    N.carrier = P}
  have hC : C.Finite := finite_normalized_packet_carriers M hn
  let F : C → FullLattice (d + 1) K := fun P => Classical.choose P.property
  have hF (P : C) : (F P).carrier = P.1 := (Classical.choose_spec P.property).2.2
  let : Finite C := hC.to_subtype
  let : Finite (signMatrices (d + 1)) := (signMatrices_finite (d + 1)).to_subtype
  let f : C × signMatrices (d + 1) → Set (X (d + 1)) := fun Pw =>
    diagonalOrbit (rightAction (latticePoint (F Pw.1) σ) Pw.2.1)
  apply (Set.finite_range f).subset
  rintro O ⟨N, hMN, w, hw, rfl⟩
  obtain ⟨a, c, hc⟩ := exists_scale_to_representative N
  let P : C := ⟨(scaleFullLattice N a).carrier,
    scaleFullLattice N a, locallyHomothetic_trans hMN (locallyHomothetic_scale N a),
    ⟨c, hc⟩, rfl⟩
  have hFP : latticePoint (F P) σ = latticePoint (scaleFullLattice N a) σ :=
    latticePoint_eq_of_carrier_eq (F P) (scaleFullLattice N a) σ hn hodd (hF P)
  obtain ⟨D, hD, heD⟩ := latticePoint_scale_diagonal N σ hn hodd a
  have heN : latticePoint N σ = rightAction (latticePoint (F P) σ) D⁻¹ := by
    rw [hFP, heD, rightAction_mul, mul_inv_cancel, rightAction_one]
  have hDw := diagonal_mul D⁻¹ w (diagonal_inv D hD) hw.1
  obtain ⟨v, hv, u, he⟩ := diagonal_eq_sign_mul_flow (D⁻¹ * w) hDw
  refine ⟨(P, ⟨v, hv⟩), ?_⟩
  change diagonalOrbit (rightAction (latticePoint (F P) σ) v) =
    diagonalOrbit (rightAction (latticePoint N σ) w)
  rw [heN, rightAction_mul, he, ← rightAction_mul]
  exact (diagonalOrbit_orbitMap (rightAction (latticePoint (F P) σ) v) u).symm

 

theorem packetVolume_ne_zero_ne_top {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d + 1) K)
    (σ : OrderedEmbeddings (d + 1) K) (hn : Module.finrank ℚ K = d + 1)
    (hodd : Odd (d + 1)) :
    (∑' O : packetOrbits M σ, orbitVolume (orbitBasepoint O)) ≠ 0 ∧
    (∑' O : packetOrbits M σ, orbitVolume (orbitBasepoint O)) ≠ ⊤ := by
  let : Fintype (packetOrbits M σ) := (packetOrbits_finite M σ hn hodd).fintype
  rw [tsum_fintype]
  constructor
  · obtain ⟨O, hO⟩ := packetOrbits_nonempty M σ
    let o : packetOrbits M σ := ⟨O, hO⟩
    intro hzero
    have H := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (packetOrbits M σ))) =>
      show (0 : ℝ≥0∞) ≤ orbitVolume (orbitBasepoint i) from bot_le) (Finset.mem_univ o)
    rw [hzero] at H
    exact (packetBasepoint_volume_pos_finite hn hodd o).1 (le_antisymm H bot_le)
  · exact ENNReal.sum_ne_top.mpr (fun O _ => (packetBasepoint_volume_pos_finite hn hodd O).2)

 

theorem packetMeasure_isProbabilityMeasure {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d + 1) K)
    (σ : OrderedEmbeddings (d + 1) K) (hn : Module.finrank ℚ K = d + 1)
    (hodd : Odd (d + 1)) : IsProbabilityMeasure (packetMeasure M σ) := by
  have hv (O : packetOrbits M σ) : orbitProbability (orbitBasepoint O) Set.univ = 1 :=
    (packetBasepoint_probability hn hodd O).measure_univ
  constructor
  rw [packetMeasure, Measure.smul_apply,
    Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, hv, smul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (packetVolume_ne_zero_ne_top M σ hn hodd).1
    (packetVolume_ne_zero_ne_top M σ hn hodd).2

lemma normalizedLattice_diagonal_invariant_iff
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K)
    (hn : Module.finrank ℚ K = n) (t : Fin n → ℝ) :
    (normalizedLattice M σ).map (diagonalLinear n t) = normalizedLattice M σ ↔
      (M.carrier.map (realEmbeddingMap σ)).map (diagonalLinear n t) =
        M.carrier.map (realEmbeddingMap σ) := by
  let c : ℝ := |(embeddingMatrix M σ).det| ^ (-(1 : ℝ) / n)
  have hc : c ≠ 0 := (Real.rpow_pos_of_pos (abs_pos.mpr
    (embeddingMatrix_det_ne_zero M σ hn)) _).ne'
  have hinj : Function.Injective (diagonalLinear n (fun _ => c)) := by
    intro x y h
    ext i
    exact mul_left_cancel₀ hc (congrFun h i)
  unfold normalizedLattice
  rw [rowLattice_smul,rowLattice_embeddingMatrix,← Submodule.map_comp,
    diagonalLinear_commute,Submodule.map_comp]
  exact (Submodule.map_injective_of_injective hinj).eq_iff

 

lemma exists_integralUnit_of_carrier_preserving
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (b : K) (hb : b ≠ 0)
    (h : ∀ x : K, x ∈ M.carrier ↔ b * x ∈ M.carrier) :
    ∃ u : (𝓞 K)ˣ, (u : K) = b ∧ u ∈ unitStabilizer M := by
  have hbi : IsIntegral ℤ b := multiplierOrder_le_integralElements M
    (fun x hx => (h x).mp hx)
  have hbinv : IsIntegral ℤ b⁻¹ := multiplierOrder_le_integralElements M (x := b⁻¹)
    (fun x hx => (h (b⁻¹*x)).mpr (by simpa [← mul_assoc,hb] using hx))
  let u : (𝓞 K)ˣ :=
    ⟨⟨b,hbi⟩,⟨b⁻¹,hbinv⟩,by ext; exact mul_inv_cancel₀ hb,
      by ext; exact inv_mul_cancel₀ hb⟩
  exact ⟨u,rfl,h⟩

 

theorem periodGroup_le_orderedLogSubgroup
    {d : ℕ} {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) :
    periodGroup (latticePoint M σ) ≤
      (orderedLogSubgroup σ (positiveUnitStabilizer M σ)).toAddSubgroup := by
  intro v hv
  obtain ⟨g,hg⟩ := exists_SL_normalizedLattice M σ hn hodd
  have he : rowLattice (g.1 * (diagonalFlow v).1) = rowLattice g.1 := by
    apply (quotient_eq_iff_rowLattice_eq (g * diagonalFlow v) g).mp
    change orbitMap (Quotient.mk _ g) v = Quotient.mk _ g
    rw [← latticePoint_eq_of_rowLattice_eq M σ g hg]
    exact hv
  let t : Fin (d+1) → ℝ := Fin.snoc (fun i : Fin d => Real.exp (v i)) (Real.exp (-∑ i, v i))
  change rowLattice (g.1 * Matrix.diagonal t) = rowLattice g.1 at he
  rw [rowLattice_mul_diagonal,hg] at he
  have hraw := (normalizedLattice_diagonal_invariant_iff M σ hn t).mp he
  have ht (i : Fin (d+1)) : 0 < t i := by
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [t,Fin.snoc_last,Fin.snoc_castSucc] <;>
      exact Real.exp_pos _
  obtain ⟨b,hb,hbt,hset⟩ := diagonal_lattice_equality_iff_homothety M M σ
    (Nat.succ_pos d) t (fun i => (ht i).ne') (by rw [Submodule.map_comp]; exact hraw)
  have hpres (x : K) : x ∈ M.carrier ↔ b*x ∈ M.carrier := by
    constructor
    · intro hx
      change b*x ∈ (M.carrier : Set K)
      rw [hset]
      exact ⟨x,hx,rfl⟩
    · intro hx
      change b*x ∈ (M.carrier : Set K) at hx
      rw [hset] at hx
      obtain ⟨y,hy,he⟩ := hx
      exact (mul_left_cancel₀ hb he) ▸ hy
  obtain ⟨u,hu,hust⟩ := exists_integralUnit_of_carrier_preserving M b hb hpres
  apply (mem_orderedLogSubgroup σ _ v).mpr
  refine ⟨u,(mem_positiveUnitStabilizer M σ u).mpr ⟨hust,?_⟩,?_⟩
  · intro i
    change 0 < σ i (u : K)
    rw [hu,← hbt i]
    exact ht i
  · ext i
    rw [orderedUnitLog_apply,hu,← hbt i.castSucc]
    simp only [t,Fin.snoc_castSucc,abs_of_pos (Real.exp_pos _),Real.log_exp]

 

theorem periodGroup_eq_orderedLogSubgroup
    {d : ℕ} {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) :
    periodGroup (latticePoint M σ) =
      (orderedLogSubgroup σ (positiveUnitStabilizer M σ)).toAddSubgroup :=
  le_antisymm (periodGroup_le_orderedLogSubgroup M σ hn hodd)
    (orderedLogSubgroup_le_periodGroup M σ hn hodd)

lemma orderedLogSubgroup_toAddSubgroup
    {d : ℕ} {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (S : Subgroup (𝓞 K)ˣ) :
    (orderedLogSubgroup σ S).toAddSubgroup = S.toAddSubgroup.map (orderedUnitLog σ) := by
  ext v
  rw [Submodule.mem_toAddSubgroup,mem_orderedLogSubgroup]
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨Additive.ofMul u,hu,rfl⟩
  · rintro ⟨u,hu,rfl⟩
    exact ⟨u.toMul,hu,rfl⟩

lemma orderedUnitLog_ker
    {d : ℕ} {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) :
    (orderedUnitLog σ).ker = (NumberField.Units.torsion K).toAddSubgroup := by
  rw [← NumberField.Units.dirichletUnitTheorem.logEmbedding_ker]
  ext u
  change orderedLogCoordinatesEquiv σ (NumberField.Units.logEmbedding K u) = 0 ↔ _
  exact EmbeddingLike.map_eq_zero_iff

 

theorem orderedLogSubgroup_relIndex
    {d : ℕ} {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (S T : Subgroup (𝓞 K)ˣ) :
    (orderedLogSubgroup σ S).toAddSubgroup.relIndex (orderedLogSubgroup σ T).toAddSubgroup =
      (S ⊔ NumberField.Units.torsion K).relIndex (T ⊔ NumberField.Units.torsion K) := by
  rw [orderedLogSubgroup_toAddSubgroup,orderedLogSubgroup_toAddSubgroup,
    AddSubgroup.relIndex_map_map,orderedUnitLog_ker,← OrderIso.map_sup,
    ← OrderIso.map_sup,Subgroup.relIndex_toAddSubgroup]

theorem orderedLogSubgroup_covolume_ratio
    {d : ℕ} {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (S : Subgroup (𝓞 K)ˣ) [S.FiniteIndex] :
    ZLattice.covolume (orderedLogSubgroup σ S) /
      ZLattice.covolume (orderedLogSubgroup σ ⊤) =
      ((S ⊔ NumberField.Units.torsion K).index : ℝ) := by
  have hle : orderedLogSubgroup σ S ≤ orderedLogSubgroup σ ⊤ := by
    intro v hv
    obtain ⟨u,_,rfl⟩ := (mem_orderedLogSubgroup σ S v).mp hv
    exact (mem_orderedLogSubgroup σ ⊤ _).mpr ⟨u,Subgroup.mem_top u,rfl⟩
  rw [ZLattice.covolume_div_covolume_eq_relIndex _ _ hle,
    orderedLogSubgroup_relIndex,top_sup_eq,Subgroup.relIndex_top_right]

 

theorem orbitVolume_latticePoint_ratio
    {d : ℕ} {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) :
    (orbitVolume (latticePoint M σ)).toReal /
      ZLattice.covolume (orderedLogSubgroup σ ⊤) =
      (((positiveUnitStabilizer M σ ⊔ NumberField.Units.torsion K).index) : ℝ) := by
  let := positiveUnitStabilizer_finiteIndex M σ
  rw [orbitVolume,periodGroup_eq_orderedLogSubgroup M σ hn hodd]
  exact orderedLogSubgroup_covolume_ratio σ (positiveUnitStabilizer M σ)

lemma compact_quotient_of_isZLattice {d : ℕ} (P : Submodule ℤ (Fin d → ℝ))
    [DiscreteTopology P] [IsZLattice ℝ P] :
    CompactSpace ((Fin d → ℝ) ⧸ P.toAddSubgroup) := by
  constructor
  rw [← Set.range_eq_univ.mpr (@QuotientAddGroup.mk_surjective _ _ P.toAddSubgroup)]
  apply IsZLattice.isCompact_range_of_periodic P
    (QuotientAddGroup.mk : (Fin d → ℝ) → (Fin d → ℝ) ⧸ P.toAddSubgroup)
    QuotientAddGroup.continuous_mk
  intro x p hp
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  simpa using hp

def normalizedLatticeQuotientMeasure {d : ℕ} (P : Submodule ℤ (Fin d → ℝ))
    (s : Set (Fin d → ℝ)) : Measure ((Fin d → ℝ) ⧸ P.toAddSubgroup) :=
  (volume s)⁻¹ • Measure.map QuotientAddGroup.mk (volume.restrict s)

lemma map_quotient_restrict_eq {d : ℕ} (P L : Submodule ℤ (Fin d → ℝ))
    [DiscreteTopology P] [DiscreteTopology L] (hLP : L ≤ P)
    {s t : Set (Fin d → ℝ)} (hs : IsAddFundamentalDomain L s volume)
    (ht : IsAddFundamentalDomain L t volume) :
    Measure.map (QuotientAddGroup.mk : _ → (Fin d → ℝ) ⧸ P.toAddSubgroup) (volume.restrict s) =
      Measure.map QuotientAddGroup.mk (volume.restrict t) := by
  have : Countable L := countable_of_Lindelof_of_discrete
  have : VAddInvariantMeasure L (Fin d → ℝ) volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup (Fin d → ℝ) volume)
  have hm : Measurable (QuotientAddGroup.mk : _ → (Fin d → ℝ) ⧸ P.toAddSubgroup) :=
    QuotientAddGroup.continuous_mk.measurable
  ext A hA
  rw [Measure.map_apply hm hA,Measure.map_apply hm hA,
    Measure.restrict_apply (hA.preimage hm),Measure.restrict_apply (hA.preimage hm)]
  apply hs.measure_set_eq ht (hA.preimage hm)
  intro u
  ext v
  change (QuotientAddGroup.mk (u.val + v) : (Fin d → ℝ) ⧸ P.toAddSubgroup) ∈ A ↔ _
  have he : (QuotientAddGroup.mk (u.val + v) : (Fin d → ℝ) ⧸ P.toAddSubgroup) =
      QuotientAddGroup.mk v := by
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    simpa using hLP u.property
  rw [he]
  rfl

lemma normalizedLatticeQuotientMeasure_invariant {d : ℕ}
    (P L : Submodule ℤ (Fin d → ℝ)) [DiscreteTopology P] [DiscreteTopology L]
    (hLP : L ≤ P) {s : Set (Fin d → ℝ)} (hs : IsAddFundamentalDomain L s volume) :
    (normalizedLatticeQuotientMeasure P s).IsAddLeftInvariant := by
  constructor
  intro a
  obtain ⟨u,rfl⟩ := QuotientAddGroup.mk_surjective a
  have hm : Measurable (QuotientAddGroup.mk : _ → (Fin d → ℝ) ⧸ P.toAddSubgroup) :=
    QuotientAddGroup.continuous_mk.measurable
  have hmu : Measurable (fun v : Fin d → ℝ => u + v) := measurable_const.add measurable_id
  have htrans := (measurePreserving_add_left (volume : Measure (Fin d → ℝ)) u).restrict_image_emb
    (MeasurableEquiv.addLeft u).measurableEmbedding s
  have ht : IsAddFundamentalDomain L ((fun v => u + v) '' s) volume := hs.vadd_of_comm u
  unfold normalizedLatticeQuotientMeasure
  have hadd : Measurable (fun a : (Fin d → ℝ) ⧸ P.toAddSubgroup => QuotientAddGroup.mk u + a) :=
    (continuous_const_add _).measurable
  rw [Measure.map_smul _ hadd.aemeasurable, Measure.map_map hadd hm]
  have he : (fun a : (Fin d → ℝ) ⧸ P.toAddSubgroup => QuotientAddGroup.mk u + a) ∘
      QuotientAddGroup.mk = QuotientAddGroup.mk ∘ (fun v : Fin d → ℝ => u+v) := by
    funext v
    exact (map_add (QuotientAddGroup.mk' P.toAddSubgroup) u v).symm
  rw [he,← Measure.map_map hm hmu,htrans.map_eq,map_quotient_restrict_eq P L hLP ht hs]

lemma normalizedLatticeQuotientMeasure_probability {d : ℕ}
    (P L : Submodule ℤ (Fin d → ℝ)) [DiscreteTopology P] [DiscreteTopology L]
    [IsZLattice ℝ L] {s : Set (Fin d → ℝ)} (hs : IsAddFundamentalDomain L s volume) :
    IsProbabilityMeasure (normalizedLatticeQuotientMeasure P s) := by
  have hvol : volume s ≠ 0 ∧ volume s ≠ ⊤ := by
    have h := ZLattice.covolume_ne_zero L volume
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L volume hs] at h
    exact ENNReal.toReal_ne_zero.mp h
  constructor
  rw [normalizedLatticeQuotientMeasure,Measure.smul_apply,smul_eq_mul,
    Measure.map_apply QuotientAddGroup.continuous_mk.measurable MeasurableSet.univ]
  simp only [preimage_univ,Measure.restrict_apply MeasurableSet.univ,univ_inter]
  exact ENNReal.inv_mul_cancel hvol.1 hvol.2

 

theorem normalizedLatticeQuotientMeasure_eq {d : ℕ}
    (P L L' : Submodule ℤ (Fin d → ℝ))
    [DiscreteTopology P] [IsZLattice ℝ P]
    [DiscreteTopology L] [IsZLattice ℝ L]
    [DiscreteTopology L'] [IsZLattice ℝ L']
    (hLP : L ≤ P) (hL'P : L' ≤ P) {s t : Set (Fin d → ℝ)}
    (hs : IsAddFundamentalDomain L s volume) (ht : IsAddFundamentalDomain L' t volume) :
    normalizedLatticeQuotientMeasure P s = normalizedLatticeQuotientMeasure P t := by
  let := compact_quotient_of_isZLattice P
  let := normalizedLatticeQuotientMeasure_invariant P L hLP hs
  let := normalizedLatticeQuotientMeasure_invariant P L' hL'P ht
  let := normalizedLatticeQuotientMeasure_probability P L hs
  let := normalizedLatticeQuotientMeasure_probability P L' ht
  have haar (U : Measure ((Fin d → ℝ) ⧸ P.toAddSubgroup))
      [U.IsAddLeftInvariant] [IsProbabilityMeasure U] : U.IsAddHaarMeasure := by
    apply Measure.isAddHaarMeasure_of_isCompact_nonempty_interior U Set.univ
      isCompact_univ (by simp) <;> simp
  let := haar (normalizedLatticeQuotientMeasure P s)
  let := haar (normalizedLatticeQuotientMeasure P t)
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

 

theorem normalized_periodic_map_eq {d : ℕ} {Y : Type*}
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (P L L' : Submodule ℤ (Fin d → ℝ))
    [DiscreteTopology P] [IsZLattice ℝ P]
    [DiscreteTopology L] [IsZLattice ℝ L]
    [DiscreteTopology L'] [IsZLattice ℝ L']
    (hLP : L ≤ P) (hL'P : L' ≤ P) {s t : Set (Fin d → ℝ)}
    (hs : IsAddFundamentalDomain L s volume) (ht : IsAddFundamentalDomain L' t volume)
    (f : (Fin d → ℝ) → Y) (hf : Continuous f)
    (hper : ∀ x p, p ∈ P → f (p+x) = f x) :
    (volume s)⁻¹ • Measure.map f (volume.restrict s) =
      (volume t)⁻¹ • Measure.map f (volume.restrict t) := by
  let F : ((Fin d → ℝ) ⧸ P.toAddSubgroup) → Y := Quotient.lift f (by
    intro u v huv
    have hmem : v-u ∈ P := by
      have h0 := QuotientAddGroup.leftRel_apply.mp huv
      rw [Submodule.mem_toAddSubgroup] at h0
      simpa only [sub_eq_neg_add] using h0
    simpa using (hper u (v-u) hmem).symm)
  have hF : Continuous F := (QuotientAddGroup.isQuotientMap_mk P.toAddSubgroup).continuous_iff.mpr hf
  have h := congrArg (Measure.map F) (normalizedLatticeQuotientMeasure_eq P L L' hLP hL'P hs ht)
  have he : F ∘ (QuotientAddGroup.mk : _ → (Fin d → ℝ) ⧸ P.toAddSubgroup) = f := rfl
  simpa only [normalizedLatticeQuotientMeasure,Measure.map_smul _ hF.measurable.aemeasurable,
    Measure.map_map hF.measurable QuotientAddGroup.continuous_mk.measurable,he] using h

lemma spanSingleton_maximalOrder_unit {K : Type*} [Field K] [NumberField K]
    (u : (𝓞 K)ˣ) : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((u : 𝓞 K) : K) = 1 := by
  rw [← FractionalIdeal.spanSingleton_one, FractionalIdeal.spanSingleton_eq_spanSingleton]
  exact ⟨u⁻¹,by simp [Units.smul_def,Algebra.smul_def]⟩

lemma scaleFullLattice_unit_carrier {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (N : FullLattice n K) (u : (𝓞 K)ˣ) :
    (scaleFullLattice N (Units.map (algebraMap (𝓞 K) K).toMonoidHom u)).carrier =
      u • N.carrier := by
  rw [Units.smul_def, Submodule.pointwise_smul_def]
  rfl

lemma globalLabels_unit_smul_mem {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (N : globalLabels M I) (u : (𝓞 K)ˣ) : u • N.val ∈ globalLabels M I := by
  let A := globalLabelLattice M I N
  refine ⟨scaleFullLattice A (Units.map (algebraMap (𝓞 K) K).toMonoidHom u),?_,?_,?_⟩
  · rw [scaleFullLattice_unit_carrier,(globalLabelLattice_spec M I N).1]
  · exact locallyHomothetic_trans (globalLabelLattice_spec M I N).2.1
      (locallyHomothetic_scale A _)
  · rw [saturationFractionalIdeal_scale]
    change FractionalIdeal.spanSingleton (𝓞 K)⁰ ((u : 𝓞 K) : K) * saturationFractionalIdeal A = _
    rw [spanSingleton_maximalOrder_unit,one_mul]
    exact (globalLabelLattice_spec M I N).2.2

instance globalLabelsMulAction {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    MulAction (𝓞 K)ˣ (globalLabels M I) where
  smul u N := ⟨u • N.val,globalLabels_unit_smul_mem M I N u⟩
  one_smul N := by apply Subtype.ext; exact one_smul _ _
  mul_smul u v N := by apply Subtype.ext; exact mul_smul _ _ _

@[simp] lemma globalLabels_smul_val {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (u : (𝓞 K)ˣ) (N : globalLabels M I) : (u • N).val = u • N.val := rfl

def signValue : SignTypeˣ →* ℝ :=
  (SignType.castHom : SignType →*₀ ℝ).toMonoidHom.comp (Units.coeHom SignType)

@[simp] lemma signValue_apply (w : SignTypeˣ) : signValue w = ((w : SignType) : ℝ) := rfl

lemma signValue_eq_one_or_neg_one (w : SignTypeˣ) : signValue w = 1 ∨ signValue w = -1 := by
  have hw := w.ne_zero
  cases h : (w : SignType) <;> simp_all

lemma signValue_sq (w : SignTypeˣ) : signValue w ^ 2 = 1 := by
  rcases signValue_eq_one_or_neg_one w with h | h <;> rw [h] <;> norm_num

lemma signValue_pow_odd (w : SignTypeˣ) {n : ℕ} (hn : Odd n) : signValue w ^ n = signValue w := by
  rw [signValue_apply, ← SignType.coe_pow, SignType.pow_odd _ hn]

 

def positiveSignMatrix {n : ℕ} (hn : Odd n) (w : Fin n → SignTypeˣ) : G n :=
  ⟨Matrix.diagonal (fun i => signValue ((∏ j, w j)*w i)), by
    rw [Matrix.det_diagonal]
    simp only [map_mul, Finset.prod_mul_distrib, Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    rw [← map_prod,signValue_pow_odd _ hn,← sq,signValue_sq]⟩

lemma positiveSignMatrix_one {n : ℕ} (hn : Odd n) : positiveSignMatrix hn 1 = 1 := by
  apply Subtype.ext
  simp [positiveSignMatrix]

lemma positiveSignMatrix_mul {n : ℕ} (hn : Odd n) (w v : Fin n → SignTypeˣ) :
    positiveSignMatrix hn (w*v) = positiveSignMatrix hn w * positiveSignMatrix hn v := by
  apply Subtype.ext
  change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  simp only [Pi.mul_apply,Finset.prod_mul_distrib,map_mul]
  ring

lemma positiveSignMatrix_diagonal {n : ℕ} (hn : Odd n) (w : Fin n → SignTypeˣ)
    (i j : Fin n) (hij : i ≠ j) : (positiveSignMatrix hn w).1 i j = 0 :=
  Matrix.diagonal_apply_ne _ hij

lemma positiveSignMatrix_entries {n : ℕ} (hn : Odd n) (w : Fin n → SignTypeˣ)
    (i : Fin n) : (positiveSignMatrix hn w).1 i i = 1 ∨
      (positiveSignMatrix hn w).1 i i = -1 := by
  change Matrix.diagonal _ i i = 1 ∨ Matrix.diagonal _ i i = -1
  simp only [Matrix.diagonal_apply_eq]
  exact signValue_eq_one_or_neg_one _

 

theorem orbitProbability_eq_normalized_map_sublattice {d : ℕ}
    (x : X (d+1)) [IsZLattice ℝ (periodGroup x).toIntSubmodule]
    (L : Submodule ℤ (LogCoordinates d)) [DiscreteTopology L] [IsZLattice ℝ L]
    (hLP : L ≤ (periodGroup x).toIntSubmodule) {s : Set (LogCoordinates d)}
    (hs : IsAddFundamentalDomain L s volume) :
    orbitProbability x = (volume s)⁻¹ • Measure.map (orbitMap x) (volume.restrict s) := by
  have : Countable (periodGroup x) := countable_of_Lindelof_of_discrete
  let hF := periodGroup_hasFundamentalDomain x
  let t := hF.ExistsIsAddFundamentalDomain.choose
  have ht : IsAddFundamentalDomain (periodGroup x) t volume :=
    hF.ExistsIsAddFundamentalDomain.choose_spec
  have hv : orbitVolume x = volume t := ht.covolume_eq_volume volume
  rw [orbitProbability,hv,orbitalHaar,dite_eq_left hF]
  apply normalized_periodic_map_eq (periodGroup x).toIntSubmodule
    (periodGroup x).toIntSubmodule L le_rfl hLP ht hs (orbitMap x) (continuous_orbitMap x)
  intro u p hp
  rw [orbitMap_add,(show orbitMap x p = x from hp)]
 

structure SignedGlobalLabel {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) where
  lattice : globalLabels M I
  signs : Fin n → SignTypeˣ

@[ext] lemma SignedGlobalLabel.ext {n : ℕ} {K : Type*} [Field K] [NumberField K]
    {M : FullLattice n K} {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    {x y : SignedGlobalLabel M I} (hN : x.lattice = y.lattice) (hw : x.signs = y.signs) : x = y := by
  cases x; cases y; cases hN; cases hw; rfl

@[instance_reducible] def signedGlobalLabelMulAction {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : MulAction (𝓞 K)ˣ (SignedGlobalLabel M I) where
  smul u x := ⟨u • x.lattice, (unitSigns σ u)⁻¹ * x.signs⟩
  one_smul x := by
    apply SignedGlobalLabel.ext
    · change (1 : (𝓞 K)ˣ) • x.lattice = x.lattice
      exact one_smul _ _
    · change (unitSigns σ 1)⁻¹ * x.signs = x.signs
      simp
  mul_smul u v x := by
    apply SignedGlobalLabel.ext
    · change (u*v) • x.lattice = u • v • x.lattice
      exact mul_smul _ _ _
    · change (unitSigns σ (u*v))⁻¹ * x.signs =
        (unitSigns σ u)⁻¹ * ((unitSigns σ v)⁻¹ * x.signs)
      simp only [map_mul, mul_inv_rev, mul_assoc, mul_left_comm]

 

lemma unit_smul_globalLabel_eq_iff {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (N : globalLabels M I) (u : (𝓞 K)ˣ) :
    u • N = N ↔ u ∈ unitStabilizer (globalLabelLattice M I N) := by
  rw [Subtype.ext_iff, globalLabels_smul_val, ← (globalLabelLattice_spec M I N).1]
  let A := globalLabelLattice M I N
  change u • A.carrier = A.carrier ↔ ∀ x : K, x ∈ A.carrier ↔ (u : K) * x ∈ A.carrier
  rw [Units.smul_def]
  constructor
  · intro h x
    constructor
    · intro hx
      rw [← h]
      exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨x,hx,rfl⟩
    · intro hx
      rw [← h] at hx
      obtain ⟨y,hy,he⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
      have hxy : y = x := mul_left_cancel₀ (integralUnit u).ne_zero he
      exact hxy ▸ hy
  · intro h
    ext x
    constructor
    · intro hx
      obtain ⟨y,hy,rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
      exact (h y).mp hy
    · intro hx
      refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨(u⁻¹ : K)*x,?_,?_⟩
      · apply (h _).mpr
        simpa [← mul_assoc] using hx
      · change (u : K) * ((u⁻¹ : K)*x) = x
        simp

 

theorem signedGlobalLabel_stabilizer {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : SignedGlobalLabel M I) :
    let := signedGlobalLabelMulAction M σ I
    MulAction.stabilizer (𝓞 K)ˣ x = positiveUnitStabilizer (globalLabelLattice M I x.lattice) σ := by
  let := signedGlobalLabelMulAction M σ I
  ext u
  change (⟨u • x.lattice,(unitSigns σ u)⁻¹ * x.signs⟩ : SignedGlobalLabel M I) = x ↔ _
  rw [show (⟨u • x.lattice,(unitSigns σ u)⁻¹ * x.signs⟩ : SignedGlobalLabel M I) = x ↔
      u • x.lattice = x.lattice ∧ (unitSigns σ u)⁻¹*x.signs = x.signs from by
        constructor
        · intro h; exact ⟨congrArg SignedGlobalLabel.lattice h,congrArg SignedGlobalLabel.signs h⟩
        · rintro ⟨hN,hw⟩; exact SignedGlobalLabel.ext hN hw]
  simp only [unit_smul_globalLabel_eq_iff, _root_.mul_eq_right, inv_eq_one]
  rfl

theorem signedGlobalLabel_finite {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Finite (SignedGlobalLabel M I) := by
  let := (globalLabels_finite M hn I).to_subtype
  exact Finite.of_injective (fun x : SignedGlobalLabel M I => (x.lattice,x.signs)) (by
    intro x y h; exact SignedGlobalLabel.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

lemma positiveUnitStabilizer_inf_torsion {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (N : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) :
    positiveUnitStabilizer N σ ⊓ NumberField.Units.torsion K = ⊥ := by
  ext u
  constructor
  · rintro ⟨hu,ht⟩
    rcases NumberField.Units.torsion_eq_one_or_neg_one_of_odd_finrank (by simpa only [hn] using hodd) ⟨u,ht⟩ with h | h
    · exact h
    · change u = -1 at h
      have hp := ((mem_positiveUnitStabilizer N σ u).mp hu).2 (0 : Fin (d+1))
      simp [h,integralUnit] at hp
      norm_num at hp
  · intro hu
    rw [Subgroup.mem_bot] at hu
    subst u
    exact one_mem _

 

theorem positiveUnitStabilizer_index_eq_twice {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (N : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) :
    (positiveUnitStabilizer N σ).index =
      2 * (positiveUnitStabilizer N σ ⊔ NumberField.Units.torsion K).index := by
  have hidx : (positiveUnitStabilizer N σ).relIndex (NumberField.Units.torsion K) = 2 := by
    rw [← Subgroup.inf_relIndex_right,positiveUnitStabilizer_inf_torsion N σ hn hodd,
      Subgroup.relIndex_bot_left]
    exact NumberField.Units.torsionOrder_eq_two_of_odd_finrank (by simpa only [hn] using hodd)
  have h := Subgroup.relIndex_mul_index (show positiveUnitStabilizer N σ ≤
    positiveUnitStabilizer N σ ⊔ NumberField.Units.torsion K from le_sup_left)
  rw [Subgroup.relIndex_sup_left,hidx] at h
  exact h.symm

lemma signedGlobalLabel_orbit_volume_ratio {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : SignedGlobalLabel M I) :
    letI := signedGlobalLabelMulAction M σ I
    2 * ((orbitVolume (latticePoint (globalLabelLattice M I x.lattice) σ)).toReal /
      ZLattice.covolume (orderedLogSubgroup σ ⊤)) =
      ((MulAction.orbit (𝓞 K)ˣ x).ncard : ℝ) := by
  let := signedGlobalLabelMulAction M σ I
  rw [← MulAction.index_stabilizer,signedGlobalLabel_stabilizer,
    orbitVolume_latticePoint_ratio _ σ hn hodd,positiveUnitStabilizer_index_eq_twice _ σ hn hodd]
  push_cast
  rfl

lemma positiveSignMatrix_mem_signMatrices {n : ℕ} (hn : Odd n) (w : Fin n → SignTypeˣ) :
    positiveSignMatrix hn w ∈ signMatrices n :=
  ⟨positiveSignMatrix_diagonal hn w,positiveSignMatrix_entries hn w⟩

lemma prod_abs_ordered_unit {n : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings n K) (u : (𝓞 K)ˣ) :
    ∏ i, |σ i (u : K)| = 1 := by
  have he := congrArg Real.exp (sum_orderedUnitLog_full σ u)
  rw [Real.exp_sum,Real.exp_zero] at he
  convert he using 1
  apply Finset.prod_congr rfl
  intro i _
  exact (Real.exp_log (abs_pos.mpr ((_root_.map_ne_zero (σ i)).mpr
    (integralUnit u).ne_zero))).symm

 

lemma normalizedLattice_scale_unit {n : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (N : FullLattice n K) (σ : OrderedEmbeddings n K)
    (u : (𝓞 K)ˣ) :
    normalizedLattice (scaleFullLattice N (integralUnit u)) σ =
      (normalizedLattice N σ).map (diagonalLinear n (fun i => σ i (u : K))) := by
  have hm : embeddingMatrix (scaleFullLattice N (integralUnit u)) σ =
      embeddingMatrix N σ * Matrix.diagonal (fun i => σ i (u : K)) := by
    ext i j
    simp only [Matrix.mul_diagonal,embeddingMatrix,scaleFullLattice_basis,map_mul]
    exact mul_comm _ _
  have hd : |(embeddingMatrix (scaleFullLattice N (integralUnit u)) σ).det| =
      |(embeddingMatrix N σ).det| := by
    rw [hm,Matrix.det_mul,abs_mul,Matrix.det_diagonal,Finset.abs_prod,
      prod_abs_ordered_unit σ u,mul_one]
  unfold normalizedLattice
  dsimp only
  rw [hd,hm,← Matrix.smul_mul, rowLattice_mul_diagonal]

lemma diagonalFlow_abs_orderedUnitLog {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K) (u : (𝓞 K)ˣ) :
    (diagonalFlow (orderedUnitLog σ (Additive.ofMul u))).1 =
      Matrix.diagonal (fun i => |σ i (u : K)|) := by
  apply congrArg Matrix.diagonal
  ext i
  have hpos (j : Fin (d+1)) : 0 < |σ j (u : K)| :=
    abs_pos.mpr ((_root_.map_ne_zero (σ j)).mpr (integralUnit u).ne_zero)
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    have h := sum_orderedUnitLog_full σ u
    rw [Fin.sum_univ_castSucc] at h
    simp only [orderedUnitLog_apply]
    rw [show -(∑ j : Fin d, Real.log |σ j.castSucc (u : K)|) =
      Real.log |σ (Fin.last d) (u : K)| by linarith,Real.exp_log (hpos _)]
  · simp only [Fin.snoc_castSucc,orderedUnitLog_apply,Real.exp_log (hpos _)]

lemma signValue_unitSigns {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (u : (𝓞 K)ˣ) (i : Fin n) :
    signValue (unitSigns σ u i) * |σ i (u : K)| = σ i (u : K) :=
  sign_mul_abs _

lemma submodule_map_signed_correction {n : ℕ} (L : Submodule ℤ (Fin n → ℝ))
    (s : SignTypeˣ) (t : Fin n → ℝ) :
    L.map (diagonalLinear n (fun i => signValue s * t i)) = L.map (diagonalLinear n t) := by
  rcases signValue_eq_one_or_neg_one s with h | h
  · simp only [h,one_mul]
  · have he : diagonalLinear n (fun i => signValue s * t i) = -(diagonalLinear n t) := by
      ext x i
      simp [h,diagonalLinear]
    rw [he,Submodule.map_neg]

 

lemma unitDiagonal_matrix {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K) (hodd : Odd (d+1))
    (u : (𝓞 K)ˣ) :
    (positiveSignMatrix hodd (unitSigns σ u) * diagonalFlow (orderedUnitLog σ (Additive.ofMul u))).1 =
      Matrix.diagonal (fun i => signValue (∏ j,unitSigns σ u j) * σ i (u : K)) := by
  change (positiveSignMatrix hodd (unitSigns σ u)).1 *
    (diagonalFlow (orderedUnitLog σ (Additive.ofMul u))).1 = _
  rw [diagonalFlow_abs_orderedUnitLog]
  change Matrix.diagonal _ * Matrix.diagonal _ = _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [map_mul,mul_assoc,signValue_unitSigns]

 

theorem latticePoint_scale_unit {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (N : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) (u : (𝓞 K)ˣ) :
    latticePoint (scaleFullLattice N (integralUnit u)) σ = rightAction (latticePoint N σ)
      (positiveSignMatrix hodd (unitSigns σ u) * diagonalFlow (orderedUnitLog σ (Additive.ofMul u))) := by
  obtain ⟨g,hg⟩ := exists_SL_normalizedLattice N σ hn hodd
  let U := positiveSignMatrix hodd (unitSigns σ u) * diagonalFlow (orderedUnitLog σ (Additive.ofMul u))
  have hrow : rowLattice (g*U).1 = normalizedLattice (scaleFullLattice N (integralUnit u)) σ := by
    change rowLattice (g.1 * U.1) = _
    rw [show U.1 = _ from unitDiagonal_matrix σ hodd u,rowLattice_mul_diagonal,hg,
      submodule_map_signed_correction,normalizedLattice_scale_unit]
  rw [latticePoint_eq_of_rowLattice_eq N σ g hg,
    latticePoint_eq_of_rowLattice_eq (scaleFullLattice N (integralUnit u)) σ (g*U) hrow]
  rfl

 

def signedGlobalLabelPoint {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K) (hodd : Odd (d+1))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : SignedGlobalLabel M I) : X (d+1) :=
  rightAction (latticePoint (globalLabelLattice M I x.lattice) σ) (positiveSignMatrix hodd x.signs)

lemma signedGlobalLabelPoint_mem_packet {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K) (hodd : Odd (d+1))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : SignedGlobalLabel M I) :
    diagonalOrbit (signedGlobalLabelPoint M σ hodd I x) ∈ packetOrbits M σ :=
  ⟨globalLabelLattice M I x.lattice,(globalLabelLattice_spec M I x.lattice).2.1,
    positiveSignMatrix hodd x.signs,positiveSignMatrix_mem_signMatrices hodd x.signs,rfl⟩

lemma signedGlobalLabelPoint_unit_action {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : SignedGlobalLabel M I) (u : (𝓞 K)ˣ) :
    letI := signedGlobalLabelMulAction M σ I
    signedGlobalLabelPoint M σ hodd I (u • x) =
      orbitMap (signedGlobalLabelPoint M σ hodd I x) (orderedUnitLog σ (Additive.ofMul u)) := by
  let := signedGlobalLabelMulAction M σ I
  have hcar : (globalLabelLattice M I (u • x.lattice)).carrier =
      (scaleFullLattice (globalLabelLattice M I x.lattice) (integralUnit u)).carrier := by
    rw [(globalLabelLattice_spec M I _).1,globalLabels_smul_val,integralUnit,scaleFullLattice_unit_carrier,
      (globalLabelLattice_spec M I _).1]
  have hbase := latticePoint_eq_of_carrier_eq _ _ σ hn hodd hcar
  change rightAction (latticePoint (globalLabelLattice M I (u • x.lattice)) σ)
    (positiveSignMatrix hodd ((unitSigns σ u)⁻¹*x.signs)) = _
  rw [hbase,latticePoint_scale_unit _ σ hn hodd,positiveSignMatrix_mul,rightAction_mul]
  unfold orbitMap signedGlobalLabelPoint
  rw [rightAction_mul]
  congr 1
  rw [mul_assoc,← diagonalFlow_commute_of_diagonal (positiveSignMatrix hodd ((unitSigns σ u)⁻¹)*
    positiveSignMatrix hodd x.signs) (diagonal_mul _ _
      (positiveSignMatrix_diagonal hodd _) (positiveSignMatrix_diagonal hodd _)),← mul_assoc,
    ← mul_assoc,← positiveSignMatrix_mul,mul_inv_cancel,positiveSignMatrix_one,one_mul]

lemma diagonalLinear_comp_apply {n : ℕ} (s t : Fin n → ℝ) :
    (diagonalLinear n s).comp (diagonalLinear n t) = diagonalLinear n (fun i => s i*t i) := by
  ext x i
  simp [diagonalLinear,mul_assoc]

lemma diagonalLinear_one {n : ℕ} : diagonalLinear n (fun _ => 1) = LinearMap.id := by
  ext x i
  simp [diagonalLinear]

lemma normalizedLattice_as_map {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (N : FullLattice n K) (σ : OrderedEmbeddings n K) :
    normalizedLattice N σ = (N.carrier.map (realEmbeddingMap σ)).map
      (diagonalLinear n (fun _ => |(embeddingMatrix N σ).det| ^ (-(1:ℝ)/n))) := by
  unfold normalizedLattice
  rw [rowLattice_smul,rowLattice_embeddingMatrix]

 

theorem normalizedLattice_diagonal_homothety {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (N P : FullLattice n K) (σ : OrderedEmbeddings n K)
    (hn : Module.finrank ℚ K = n) (hpos : 0 < n)
    (t : Fin n → ℝ) (ht : ∀ i, t i ≠ 0)
    (h : (normalizedLattice N σ).map (diagonalLinear n t) = normalizedLattice P σ) :
    ∃ b : K, b ≠ 0 ∧
      (∀ i, |(embeddingMatrix N σ).det| ^ (-(1:ℝ)/n) /
        |(embeddingMatrix P σ).det| ^ (-(1:ℝ)/n) * t i = σ i b) ∧
      (P.carrier : Set K) = (fun x => b*x) '' (N.carrier : Set K) := by
  let c : ℝ := |(embeddingMatrix N σ).det| ^ (-(1:ℝ)/n)
  let e : ℝ := |(embeddingMatrix P σ).det| ^ (-(1:ℝ)/n)
  have hc : 0 < c := Real.rpow_pos_of_pos (abs_pos.mpr (embeddingMatrix_det_ne_zero N σ hn)) _
  have he : 0 < e := Real.rpow_pos_of_pos (abs_pos.mpr (embeddingMatrix_det_ne_zero P σ hn)) _
  rw [normalizedLattice_as_map,normalizedLattice_as_map] at h
  change ((N.carrier.map (realEmbeddingMap σ)).map (diagonalLinear n (fun _ => c))).map
    (diagonalLinear n t) = (P.carrier.map (realEmbeddingMap σ)).map (diagonalLinear n (fun _ => e)) at h
  have H := congrArg (fun L : Submodule ℤ (Fin n → ℝ) =>
    L.map (diagonalLinear n (fun _ => e⁻¹))) h
  simp only [← Submodule.map_comp] at H
  have hleft : (diagonalLinear n (fun _ => e⁻¹)).comp
      ((diagonalLinear n t).comp ((diagonalLinear n (fun _ => c)).comp (realEmbeddingMap σ))) =
      (diagonalLinear n (fun i => c/e*t i)).comp (realEmbeddingMap σ) := by
    ext x i
    simp only [LinearMap.comp_apply,diagonalLinear,LinearMap.coe_mk,AddHom.coe_mk]
    ring
  have hright : (diagonalLinear n (fun _ => e⁻¹)).comp
      ((diagonalLinear n (fun _ => e)).comp (realEmbeddingMap σ)) = realEmbeddingMap σ := by
    ext x i
    simp only [LinearMap.comp_apply,diagonalLinear,LinearMap.coe_mk,AddHom.coe_mk]
    rw [← mul_assoc,inv_mul_cancel₀ he.ne',one_mul]
  rw [hleft,hright] at H
  exact diagonal_lattice_equality_iff_homothety N P σ hpos _
    (fun i => mul_ne_zero (div_ne_zero hc.ne' he.ne') (ht i)) H

lemma latticePoint_rightAction_diagonal_homothety {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (N P : FullLattice n K) (σ : OrderedEmbeddings n K)
    (hn : Module.finrank ℚ K = n) (hodd : Odd n) (D : G n)
    (hD : ∀ i j, i ≠ j → D.1 i j = 0)
    (h : rightAction (latticePoint N σ) D = latticePoint P σ) :
    ∃ b : K, b ≠ 0 ∧
      (∀ i, |(embeddingMatrix N σ).det| ^ (-(1:ℝ)/n) /
        |(embeddingMatrix P σ).det| ^ (-(1:ℝ)/n) * D.1 i i = σ i b) ∧
      (P.carrier : Set K) = (fun x => b*x) '' (N.carrier : Set K) := by
  obtain ⟨g,hg⟩ := exists_SL_normalizedLattice N σ hn hodd
  obtain ⟨k,hk⟩ := exists_SL_normalizedLattice P σ hn hodd
  have hd : D.1 = Matrix.diagonal (fun i => D.1 i i) :=
    (Matrix.IsDiag.diagonal_diag hD).symm
  have hrow : rowLattice (g.1 * D.1) = rowLattice k.1 := by
    apply (quotient_eq_iff_rowLattice_eq (g*D) k).mp
    change rightAction (Quotient.mk _ g) D = Quotient.mk _ k
    rw [← latticePoint_eq_of_rowLattice_eq N σ g hg,
      ← latticePoint_eq_of_rowLattice_eq P σ k hk]
    exact h
  rw [hd,rowLattice_mul_diagonal,hg,hk] at hrow
  have hprod : ∏ i, D.1 i i = 1 := by
    have he := D.property
    rwa [hd,Matrix.det_diagonal] at he
  apply normalizedLattice_diagonal_homothety N P σ hn hodd.pos _ _ hrow
  intro i hi
  have H := Finset.prod_eq_zero (f := fun j => D.1 j j) (Finset.mem_univ i) hi
  rw [hprod] at H
  exact one_ne_zero H

lemma saturationFractionalIdeal_eq_of_carrier_eq {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (N P : FullLattice n K) (h : N.carrier = P.carrier) :
    saturationFractionalIdeal N = saturationFractionalIdeal P := by
  apply FractionalIdeal.coeToSubmodule_injective
  change Submodule.span (𝓞 K) (N.carrier : Set K) = Submodule.span (𝓞 K) (P.carrier : Set K)
  rw [h]

 

lemma exists_integralUnit_of_same_saturation {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (N P : FullLattice n K) (b : K) (hb : b ≠ 0)
    (h : (P.carrier : Set K) = (fun x => b*x) '' (N.carrier : Set K))
    (hI : saturationFractionalIdeal N = saturationFractionalIdeal P) :
    ∃ u : (𝓞 K)ˣ, (u : K) = b ∧ P.carrier = u • N.carrier := by
  let a : Kˣ := Units.mk0 b hb
  have hcar : P.carrier = (scaleFullLattice N a).carrier := by
    apply SetLike.coe_injective
    rw [scaleFullLattice_carrier]
    exact h
  have hId := saturationFractionalIdeal_eq_of_carrier_eq P (scaleFullLattice N a) hcar
  rw [saturationFractionalIdeal_scale,← hI] at hId
  have hp : FractionalIdeal.spanSingleton (𝓞 K)⁰ b = 1 := by
    apply mul_right_cancel₀ (saturationFractionalIdeal_ne_zero N)
    simpa only [a,Units.val_mk0,one_mul] using hId.symm
  rw [← FractionalIdeal.spanSingleton_one] at hp
  obtain ⟨u,hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hp.symm
  have hu' : (u : K) = b := by simpa [Units.smul_def,Algebra.smul_def] using hu
  refine ⟨u,hu',?_⟩
  have ha : a = integralUnit u := by apply Units.ext; exact hu'.symm
  rw [hcar,ha,integralUnit,scaleFullLattice_unit_carrier]

lemma rowLattice_positiveSignMatrix {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hn : Odd n) (w : Fin n → SignTypeˣ) :
    rowLattice (B * (positiveSignMatrix hn w).1) =
      (rowLattice B).map (diagonalLinear n (fun i => signValue (w i))) := by
  change rowLattice (B * Matrix.diagonal (fun i => signValue ((∏ j,w j)*w i))) = _
  simp only [map_mul]
  rw [rowLattice_mul_diagonal,submodule_map_signed_correction]

lemma signValue_sign (w : SignTypeˣ) : SignType.sign (signValue w) = w := by
  have hw := w.ne_zero
  cases h : (w : SignType) <;> simp_all [signValue]

lemma signUnits_sq (w : SignTypeˣ) : w*w = 1 := by
  apply Units.ext
  have hw := w.ne_zero
  cases h : (w : SignType) <;> simp_all

lemma signUnits_inv (w : SignTypeˣ) : w⁻¹ = w :=
  inv_eq_of_mul_eq_one_left (signUnits_sq w)

 

theorem signedGlobalLabel_orbit_injective {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x y : SignedGlobalLabel M I)
    (h : diagonalOrbit (signedGlobalLabelPoint M σ hodd I x) =
      diagonalOrbit (signedGlobalLabelPoint M σ hodd I y)) :
    letI := signedGlobalLabelMulAction M σ I
    ∃ u : (𝓞 K)ˣ, u • x = y := by
  let := signedGlobalLabelMulAction M σ I
  let N := globalLabelLattice M I x.lattice
  let P := globalLabelLattice M I y.lattice
  have hy := mem_diagonalOrbit_self (signedGlobalLabelPoint M σ hodd I y)
  rw [← h] at hy
  obtain ⟨v,hv⟩ := hy
  obtain ⟨g,hg⟩ := exists_SL_normalizedLattice N σ hn hodd
  obtain ⟨k,hk⟩ := exists_SL_normalizedLattice P σ hn hodd
  let t : Fin (d+1) → ℝ := Fin.snoc (fun i : Fin d => Real.exp (v i)) (Real.exp (-∑ i,v i))
  have ht (i : Fin (d+1)) : 0 < t i := by
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [t,Fin.snoc_last,Fin.snoc_castSucc] <;>
      exact Real.exp_pos _
  have hrow : rowLattice ((g.1 * (positiveSignMatrix hodd x.signs).1) * Matrix.diagonal t) =
      rowLattice (k.1 * (positiveSignMatrix hodd y.signs).1) := by
    apply (quotient_eq_iff_rowLattice_eq ((g*positiveSignMatrix hodd x.signs)*diagonalFlow v)
      (k*positiveSignMatrix hodd y.signs)).mp
    change orbitMap (rightAction (Quotient.mk _ g) (positiveSignMatrix hodd x.signs)) v =
      rightAction (Quotient.mk _ k) (positiveSignMatrix hodd y.signs)
    rw [← latticePoint_eq_of_rowLattice_eq N σ g hg,← latticePoint_eq_of_rowLattice_eq P σ k hk]
    exact hv
  rw [rowLattice_mul_diagonal,rowLattice_positiveSignMatrix,rowLattice_positiveSignMatrix,hg,hk] at hrow
  have HH := congrArg (fun L : Submodule ℤ (Fin (d+1) → ℝ) =>
    L.map (diagonalLinear (d+1) (fun i => signValue (y.signs i)))) hrow
  simp only [← Submodule.map_comp,diagonalLinear_comp_apply] at HH
  have hyy : (fun i => signValue (y.signs i)*signValue (y.signs i)) = fun _ => (1:ℝ) := by
    funext i; exact (pow_two _).symm.trans (signValue_sq _)
  rw [hyy,diagonalLinear_one,Submodule.map_id] at HH
  obtain ⟨b,hb,hbt,hset⟩ := normalizedLattice_diagonal_homothety N P σ hn (Nat.succ_pos d)
    _ (fun i => mul_ne_zero (by
      have HH := signValue_sq (y.signs i)
      intro hz; rw [hz,zero_pow (by omega)] at HH; exact zero_ne_one HH)
      (mul_ne_zero (ht i).ne' (by
        have HH := signValue_sq (x.signs i)
        intro hz; rw [hz,zero_pow (by omega)] at HH; exact zero_ne_one HH))) HH
  have hI : saturationFractionalIdeal N = saturationFractionalIdeal P :=
    (globalLabelLattice_spec M I x.lattice).2.2.trans (globalLabelLattice_spec M I y.lattice).2.2.symm
  obtain ⟨u,hu,hcar⟩ := exists_integralUnit_of_same_saturation N P b hb hset hI
  have hsign : unitSigns σ u = y.signs*x.signs := by
    funext i
    apply Units.ext
    change SignType.sign (σ i (u : K)) = (y.signs i : SignType)*(x.signs i : SignType)
    rw [hu,← hbt i]
    have hc : 0 < |(embeddingMatrix N σ).det| ^ (-(1:ℝ)/((d+1:ℕ):ℝ)) /
        |(embeddingMatrix P σ).det| ^ (-(1:ℝ)/((d+1:ℕ):ℝ)) := div_pos
      (Real.rpow_pos_of_pos (abs_pos.mpr (embeddingMatrix_det_ne_zero N σ hn)) _)
      (Real.rpow_pos_of_pos (abs_pos.mpr (embeddingMatrix_det_ne_zero P σ hn)) _)
    rw [sign_mul,sign_pos hc,one_mul,sign_mul,signValue_sign,sign_mul,sign_pos (ht i),
      one_mul,signValue_sign]
  refine ⟨u,SignedGlobalLabel.ext ?_ ?_⟩
  · apply Subtype.ext
    change u • x.lattice.val = y.lattice.val
    rw [← (globalLabelLattice_spec M I x.lattice).1,← (globalLabelLattice_spec M I y.lattice).1]
    exact hcar.symm
  · change (unitSigns σ u)⁻¹*x.signs = y.signs
    rw [hsign]
    funext i
    simp only [Pi.mul_apply,Pi.inv_apply, signUnits_inv]
    rw [mul_assoc,signUnits_sq,mul_one]

lemma signedGlobalLabel_orbit_eq_iff {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x y : SignedGlobalLabel M I) :
    letI := signedGlobalLabelMulAction M σ I
    diagonalOrbit (signedGlobalLabelPoint M σ hodd I x) =
      diagonalOrbit (signedGlobalLabelPoint M σ hodd I y) ↔ ∃ u : (𝓞 K)ˣ, u • x = y := by
  let := signedGlobalLabelMulAction M σ I
  constructor
  · exact signedGlobalLabel_orbit_injective M σ hn hodd I x y
  · rintro ⟨u,rfl⟩
    rw [signedGlobalLabelPoint_unit_action M σ hn hodd]
    exact (diagonalOrbit_orbitMap _ _).symm

lemma signValue_injective : Function.Injective signValue := by
  intro a b h
  apply Units.ext
  simpa only [signValue_sign] using congrArg SignType.sign h

lemma exists_fullSigns_of_signMatrix {n : ℕ} (hn : Odd n) (w : G n)
    (hw : w ∈ signMatrices n) : ∃ v : Fin n → SignTypeˣ, positiveSignMatrix hn v = w := by
  have hnz (i : Fin n) : w.1 i i ≠ 0 := by
    rcases hw.2 i with h | h <;> rw [h] <;> norm_num
  let v : Fin n → SignTypeˣ := fun i =>
    Units.map (signHom : ℝ →*₀ SignType).toMonoidHom (Units.mk0 (w.1 i i) (hnz i))
  have hv (i : Fin n) : signValue (v i) = w.1 i i := by
    change ((SignType.sign (w.1 i i) : SignType) : ℝ) = w.1 i i
    rcases hw.2 i with h | h <;> simp [h]
  have hp : ∏ i,v i = 1 := by
    apply signValue_injective
    rw [map_prod,map_one]
    simp only [hv]
    have hdiag : Matrix.diagonal (fun i => w.1 i i) = w.1 := Matrix.IsDiag.diagonal_diag hw.1
    rw [← Matrix.det_diagonal, hdiag]
    exact w.property
  refine ⟨v,?_⟩
  apply Subtype.ext
  change Matrix.diagonal (fun i => signValue ((∏ j,v j)*v i)) = w.1
  simp only [hp,one_mul,hv]
  exact Matrix.IsDiag.diagonal_diag hw.1

lemma saturation_class_eq_of_signed_orbit_eq {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (N P : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) (w z : G (d+1))
    (hw : w ∈ signMatrices (d+1)) (hz : z ∈ signMatrices (d+1))
    (h : diagonalOrbit (rightAction (latticePoint N σ) w) =
      diagonalOrbit (rightAction (latticePoint P σ) z)) :
    ClassGroup.mk K (Units.mk0 (saturationFractionalIdeal N) (saturationFractionalIdeal_ne_zero N)) =
      ClassGroup.mk K (Units.mk0 (saturationFractionalIdeal P) (saturationFractionalIdeal_ne_zero P)) := by
  have hmem := mem_diagonalOrbit_self (rightAction (latticePoint P σ) z)
  rw [← h] at hmem
  obtain ⟨v,hv⟩ := hmem
  have he := congrArg (fun x : X (d+1) => rightAction x z⁻¹) hv
  change rightAction (rightAction (rightAction (latticePoint N σ) w) (diagonalFlow v)) z⁻¹ =
    rightAction (rightAction (latticePoint P σ) z) z⁻¹ at he
  simp only [rightAction_mul,mul_inv_cancel,rightAction_one] at he
  have hD := diagonal_mul (w*diagonalFlow v) z⁻¹
    (diagonal_mul w (diagonalFlow v) hw.1 (fun i j hij => Matrix.diagonal_apply_ne _ hij))
    (diagonal_inv z hz.1)
  obtain ⟨b,hb,_,hset⟩ := latticePoint_rightAction_diagonal_homothety N P σ hn hodd _ hD he
  apply (fractionalIdeal_same_class _ _).mpr
  refine ⟨b,hb,?_⟩
  let a : Kˣ := Units.mk0 b hb
  have hcar : P.carrier = (scaleFullLattice N a).carrier := by
    apply SetLike.coe_injective
    rw [scaleFullLattice_carrier]
    exact hset
  have HI := saturationFractionalIdeal_eq_of_carrier_eq P (scaleFullLattice N a) hcar
  rw [saturationFractionalIdeal_scale] at HI
  exact HI.symm

 

abbrev AllSignedGlobalLabel {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) :=
  Σ c : ClassGroup (𝓞 K), SignedGlobalLabel M (classRepresentative K c)

@[instance_reducible] def allSignedGlobalLabelMulAction {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) : MulAction (𝓞 K)ˣ (AllSignedGlobalLabel M) := by
  letI (c : ClassGroup (𝓞 K)) := signedGlobalLabelMulAction M σ (classRepresentative K c)
  infer_instance

lemma allSignedGlobalLabel_finite {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) : Finite (AllSignedGlobalLabel M) := by
  let (c : ClassGroup (𝓞 K)) := signedGlobalLabel_finite M hn (classRepresentative K c)
  infer_instance

def allSignedGlobalLabelPoint {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K) (hodd : Odd (d+1))
    (x : AllSignedGlobalLabel M) : X (d+1) :=
  signedGlobalLabelPoint M σ hodd (classRepresentative K x.1) x.2

def allSignedGlobalLabelOrbit {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K) (hodd : Odd (d+1))
    (x : AllSignedGlobalLabel M) : packetOrbits M σ :=
  ⟨diagonalOrbit (allSignedGlobalLabelPoint M σ hodd x),
    signedGlobalLabelPoint_mem_packet M σ hodd _ x.2⟩

lemma allSignedGlobalLabelOrbit_unit_action {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (x : AllSignedGlobalLabel M) (u : (𝓞 K)ˣ) :
    letI := allSignedGlobalLabelMulAction M σ
    allSignedGlobalLabelOrbit M σ hodd (u • x) = allSignedGlobalLabelOrbit M σ hodd x := by
  let := allSignedGlobalLabelMulAction M σ
  let := signedGlobalLabelMulAction M σ (classRepresentative K x.1)
  apply Subtype.ext
  change diagonalOrbit (signedGlobalLabelPoint M σ hodd _ (u • x.2)) = _
  rw [signedGlobalLabelPoint_unit_action M σ hn hodd,diagonalOrbit_orbitMap]
  rfl

lemma allSignedGlobalLabelOrbit_eq_iff {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (x y : AllSignedGlobalLabel M) :
    letI := allSignedGlobalLabelMulAction M σ
    allSignedGlobalLabelOrbit M σ hodd x = allSignedGlobalLabelOrbit M σ hodd y ↔
      ∃ u : (𝓞 K)ˣ, u • x = y := by
  let := allSignedGlobalLabelMulAction M σ
  constructor
  · intro h
    rcases x with ⟨c,x⟩
    rcases y with ⟨e,y⟩
    have he := saturation_class_eq_of_signed_orbit_eq
      (globalLabelLattice M (classRepresentative K c) x.lattice)
      (globalLabelLattice M (classRepresentative K e) y.lattice) σ hn hodd
      (positiveSignMatrix hodd x.signs) (positiveSignMatrix hodd y.signs)
      (positiveSignMatrix_mem_signMatrices hodd x.signs)
      (positiveSignMatrix_mem_signMatrices hodd y.signs) (congrArg Subtype.val h)
    have hc : Units.mk0 (saturationFractionalIdeal (globalLabelLattice M (classRepresentative K c) x.lattice))
        (saturationFractionalIdeal_ne_zero _) = classRepresentative K c := by
      apply Units.ext
      exact (globalLabelLattice_spec M _ x.lattice).2.2
    have hd : Units.mk0 (saturationFractionalIdeal (globalLabelLattice M (classRepresentative K e) y.lattice))
        (saturationFractionalIdeal_ne_zero _) = classRepresentative K e := by
      apply Units.ext
      exact (globalLabelLattice_spec M _ y.lattice).2.2
    rw [hc,hd,classRepresentative_spec,classRepresentative_spec] at he
    subst e
    obtain ⟨u,hu⟩ := signedGlobalLabel_orbit_injective M σ hn hodd (classRepresentative K c) x y
      (congrArg Subtype.val h)
    exact ⟨u,congrArg (Sigma.mk c) hu⟩
  · rintro ⟨u,rfl⟩
    exact (allSignedGlobalLabelOrbit_unit_action M σ hn hodd x u).symm

lemma allSignedGlobalLabelOrbit_surjective {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) :
    Function.Surjective (allSignedGlobalLabelOrbit M σ hodd) := by
  rintro ⟨O,N,hMN,w,hw,rfl⟩
  obtain ⟨a,c,hc⟩ := exists_scale_to_representative N
  let P := scaleFullLattice N a
  let L : globalLabels M (classRepresentative K c) :=
    ⟨P.carrier,P,rfl,locallyHomothetic_trans hMN (locallyHomothetic_scale N a),hc⟩
  have hLP : latticePoint (globalLabelLattice M (classRepresentative K c) L) σ = latticePoint P σ :=
    latticePoint_eq_of_carrier_eq _ _ σ hn hodd (globalLabelLattice_spec M _ L).1
  obtain ⟨D,hD,heD⟩ := latticePoint_scale_diagonal N σ hn hodd a
  have heN : latticePoint N σ = rightAction (latticePoint P σ) D⁻¹ := by
    rw [show latticePoint P σ = rightAction (latticePoint N σ) D from heD,
      rightAction_mul,mul_inv_cancel,rightAction_one]
  obtain ⟨v,hv,u,he⟩ := diagonal_eq_sign_mul_flow (D⁻¹*w) (diagonal_mul _ _ (diagonal_inv D hD) hw.1)
  obtain ⟨s,hs⟩ := exists_fullSigns_of_signMatrix hodd v hv
  refine ⟨⟨c,⟨L,s⟩⟩,?_⟩
  apply Subtype.ext
  change diagonalOrbit (rightAction (latticePoint (globalLabelLattice M (classRepresentative K c) L) σ)
    (positiveSignMatrix hodd s)) = diagonalOrbit (rightAction (latticePoint N σ) w)
  rw [hLP,hs,heN,rightAction_mul,he,← rightAction_mul]
  exact (diagonalOrbit_orbitMap _ _).symm

 

def signedPacketOrbitEquiv {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) :
    letI := allSignedGlobalLabelMulAction M σ
    MulAction.orbitRel.Quotient (𝓞 K)ˣ (AllSignedGlobalLabel M) ≃ packetOrbits M σ := by
  letI := allSignedGlobalLabelMulAction M σ
  refine Equiv.ofBijective (Quotient.lift (allSignedGlobalLabelOrbit M σ hodd) ?_) ⟨?_,?_⟩
  · intro x y h
    change MulAction.orbitRel (𝓞 K)ˣ (AllSignedGlobalLabel M) x y at h
    rw [MulAction.orbitRel_apply] at h
    obtain ⟨u,hu⟩ := h
    exact (allSignedGlobalLabelOrbit_eq_iff M σ hn hodd x y).mpr ⟨u⁻¹,by rw [← hu]; simp⟩
  · intro x y
    induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y =>
        intro he
        apply Quotient.sound
        change MulAction.orbitRel (𝓞 K)ˣ (AllSignedGlobalLabel M) x y
        rw [MulAction.orbitRel_apply]
        obtain ⟨u,hu⟩ := (allSignedGlobalLabelOrbit_eq_iff M σ hn hodd x y).mp he
        exact ⟨u⁻¹,by rw [← hu]; simp⟩
  · intro O
    obtain ⟨x,hx⟩ := allSignedGlobalLabelOrbit_surjective M σ hn hodd O
    exact ⟨Quotient.mk'' x,hx⟩

lemma finite_orbitFiber_card {G α : Type*} [Group G] [MulAction G α] [Fintype α]
    (q : MulAction.orbitRel.Quotient G α) :
    Fintype.card {x : α // (Quotient.mk'' x : MulAction.orbitRel.Quotient G α) = q} =
      (MulAction.stabilizer G q.out).index := by
  have he : {x : α | (Quotient.mk'' x : MulAction.orbitRel.Quotient G α) = q} =
      MulAction.orbit G q.out := by
    ext x
    rw [← MulAction.orbitRel_apply,← Quotient.eq'',Quotient.out_eq']
    rfl
  rw [← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (Set.equivOfEq he)).trans (MulAction.index_stabilizer G q.out).symm

 

theorem sum_orbits_index_nsmul {G α A : Type*} [Group G] [MulAction G α]
    [Fintype α] [AddCommMonoid A] (f : MulAction.orbitRel.Quotient G α → A) :
    ∑ q, (MulAction.stabilizer G q.out).index • f q =
      ∑ x : α, f (Quotient.mk'' x) := by
  classical
  rw [← Fintype.sum_fiberwise (fun x : α => (Quotient.mk'' x : MulAction.orbitRel.Quotient G α))]
  apply Finset.sum_congr rfl
  intro q _
  have hi (x : {x : α // (Quotient.mk'' x : MulAction.orbitRel.Quotient G α) = q}) :
      f (Quotient.mk'' x.val) = f q := congrArg f x.property
  simp_rw [hi]
  rw [Finset.sum_const, Finset.card_univ, finite_orbitFiber_card]

lemma sum_orbits_index_eq_card {G α : Type*} [Group G] [MulAction G α] [Fintype α] :
    ∑ q : MulAction.orbitRel.Quotient G α, (MulAction.stabilizer G q.out).index =
      Fintype.card α := by
  simpa using sum_orbits_index_nsmul (G := G) (α := α)
    (fun _ : MulAction.orbitRel.Quotient G α => (1 : ℕ))

 

theorem sum_orbits_index_smul_measure {G α Y : Type*} [Group G] [MulAction G α]
    [Fintype α] [MeasurableSpace Y] (orbitMeasures : MulAction.orbitRel.Quotient G α → Measure Y) :
    ∑ q, ((MulAction.stabilizer G q.out).index : ℝ≥0∞) • orbitMeasures q =
      ∑ x : α, orbitMeasures (Quotient.mk'' x) := by
  simpa only [Nat.cast_smul_eq_nsmul ℝ≥0∞] using sum_orbits_index_nsmul orbitMeasures

lemma allSignedGlobalLabel_stabilizer {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) (x : AllSignedGlobalLabel M) :
    letI := allSignedGlobalLabelMulAction M σ
    MulAction.stabilizer (𝓞 K)ˣ x =
      positiveUnitStabilizer (globalLabelLattice M (classRepresentative K x.1) x.2.lattice) σ := by
  let := allSignedGlobalLabelMulAction M σ
  let := signedGlobalLabelMulAction M σ (classRepresentative K x.1)
  rw [← signedGlobalLabel_stabilizer M σ (classRepresentative K x.1) x.2]
  ext u
  change Sigma.mk x.1 (u • x.2) = x ↔ u • x.2 = x.2
  exact Sigma.mk.inj_iff.trans (by simp)

lemma signedPacketOrbitEquiv_mk {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) (x : AllSignedGlobalLabel M) :
    letI := allSignedGlobalLabelMulAction M σ
    signedPacketOrbitEquiv M σ hn hodd (Quotient.mk'' x) = allSignedGlobalLabelOrbit M σ hodd x := rfl

lemma allSignedGlobalLabel_volume {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) (x : AllSignedGlobalLabel M) :
    letI := allSignedGlobalLabelMulAction M σ
    orbitVolume (allSignedGlobalLabelPoint M σ hodd x) =
      ENNReal.ofReal (ZLattice.covolume (orderedLogSubgroup σ ⊤) / 2) *
        (MulAction.stabilizer (𝓞 K)ˣ x).index := by
  let := allSignedGlobalLabelMulAction M σ
  let N := globalLabelLattice M (classRepresentative K x.1) x.2.lattice
  have he : orbitVolume (allSignedGlobalLabelPoint M σ hodd x) = orbitVolume (latticePoint N σ) := by
    change orbitVolume (rightAction (latticePoint N σ) (positiveSignMatrix hodd x.2.signs)) = _
    unfold orbitVolume
    rw [periodGroup_rightAction_of_diagonal _ _ (positiveSignMatrix_diagonal hodd x.2.signs)]
  rw [he,allSignedGlobalLabel_stabilizer]
  have hp : 0 < ZLattice.covolume (orderedLogSubgroup σ ⊤) := ZLattice.covolume_pos (orderedLogSubgroup σ ⊤)
  have hv := orbitVolume_latticePoint_ratio N σ hn hodd
  have hi := positiveUnitStabilizer_index_eq_twice N σ hn hodd
  have hr : (orbitVolume (latticePoint N σ)).toReal =
      (ZLattice.covolume (orderedLogSubgroup σ ⊤) / 2) * ((positiveUnitStabilizer N σ).index : ℝ) := by
    rw [hi]
    push_cast
    rw [div_eq_iff hp.ne'] at hv
    nlinarith
  have ht : orbitVolume (latticePoint N σ) ≠ ⊤ := by
    let := latticePoint_period_isZLattice N σ hn hodd
    exact (orbitVolume_ne_zero_ne_top _).2
  apply (ENNReal.toReal_eq_toReal_iff' ht (by finiteness)).mp
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity),ENNReal.toReal_natCast]
  exact hr

lemma signedPacketOrbitEquiv_volume {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) :
    letI := allSignedGlobalLabelMulAction M σ
    ∀ q : MulAction.orbitRel.Quotient (𝓞 K)ˣ (AllSignedGlobalLabel M),
    orbitVolume (orbitBasepoint (signedPacketOrbitEquiv M σ hn hodd q)) =
      ENNReal.ofReal (ZLattice.covolume (orderedLogSubgroup σ ⊤) / 2) *
        (MulAction.stabilizer (𝓞 K)ˣ q.out).index := by
  let := allSignedGlobalLabelMulAction M σ
  intro q
  have he : diagonalOrbit (orbitBasepoint (signedPacketOrbitEquiv M σ hn hodd q)) =
      diagonalOrbit (allSignedGlobalLabelPoint M σ hodd q.out) := by
    rw [orbitBasepoint_spec]
    change _ = (allSignedGlobalLabelOrbit M σ hodd q.out).val
    rw [← signedPacketOrbitEquiv_mk M σ hn hodd,Quotient.out_eq']
  rw [orbitVolume_eq_of_diagonalOrbit_eq he]
  exact allSignedGlobalLabel_volume M σ hn hodd q.out

lemma signedPacketOrbitEquiv_probability_mk {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) (x : AllSignedGlobalLabel M) :
    letI := allSignedGlobalLabelMulAction M σ
    orbitProbability (orbitBasepoint (signedPacketOrbitEquiv M σ hn hodd (Quotient.mk'' x))) =
      orbitProbability (allSignedGlobalLabelPoint M σ hodd x) := by
  let := allSignedGlobalLabelMulAction M σ
  apply orbitProbability_eq_of_diagonalOrbit_eq
  rw [signedPacketOrbitEquiv_mk,orbitBasepoint_spec]
  rfl

 

theorem packetVolume_eq_signedLabelCount {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) :
    ∑' O : packetOrbits M σ, orbitVolume (orbitBasepoint O) =
      ENNReal.ofReal (ZLattice.covolume (orderedLogSubgroup σ ⊤)/2) * Nat.card (AllSignedGlobalLabel M) := by
  let := allSignedGlobalLabelMulAction M σ
  let := allSignedGlobalLabel_finite M hn
  let := Fintype.ofFinite (AllSignedGlobalLabel M)
  let := (packetOrbits_finite M σ hn hodd).fintype
  rw [← (signedPacketOrbitEquiv M σ hn hodd).tsum_eq]
  simp_rw [signedPacketOrbitEquiv_volume M σ hn hodd]
  rw [ENNReal.tsum_mul_left,tsum_fintype,← Nat.cast_sum,sum_orbits_index_eq_card,Nat.card_eq_fintype_card]

 

theorem packetMeasure_eq_signedLabelAverage {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) :
    packetMeasure M σ = (Nat.card (AllSignedGlobalLabel M) : ℝ≥0∞)⁻¹ •
      Measure.sum (fun x : AllSignedGlobalLabel M => orbitProbability (allSignedGlobalLabelPoint M σ hodd x)) := by
  let := allSignedGlobalLabelMulAction M σ
  let := allSignedGlobalLabel_finite M hn
  let := Fintype.ofFinite (AllSignedGlobalLabel M)
  let := (packetOrbits_finite M σ hn hodd).fintype
  let e := signedPacketOrbitEquiv M σ hn hodd
  let r := ENNReal.ofReal (ZLattice.covolume (orderedLogSubgroup σ ⊤)/2)
  have hr0 : r ≠ 0 := (ENNReal.ofReal_pos.mpr (by exact div_pos (ZLattice.covolume_pos (orderedLogSubgroup σ ⊤)) (by norm_num))).ne'
  have hrt : r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsum : Measure.sum (fun O : packetOrbits M σ =>
      orbitVolume (orbitBasepoint O) • orbitProbability (orbitBasepoint O)) =
      r • Measure.sum (fun x : AllSignedGlobalLabel M => orbitProbability (allSignedGlobalLabelPoint M σ hodd x)) := by
    rw [Measure.sum_fintype,← e.sum_comp]
    dsimp only [e]
    simp_rw [signedPacketOrbitEquiv_volume M σ hn hodd,mul_smul]
    rw [← Finset.smul_sum]
    congr 1
    rw [sum_orbits_index_smul_measure,Measure.sum_fintype]
    apply Finset.sum_congr rfl
    intro x _
    exact signedPacketOrbitEquiv_probability_mk M σ hn hodd x
  rw [packetMeasure,hsum,packetVolume_eq_signedLabelCount M σ hn hodd]
  change (r * (Nat.card (AllSignedGlobalLabel M) : ℝ≥0∞))⁻¹ • (r • _) = _
  rw [smul_smul,ENNReal.mul_inv (Or.inl hr0) (Or.inl hrt)]
  rw [mul_right_comm,ENNReal.inv_mul_cancel hr0 hrt,one_mul]

 

theorem normalized_measurable_periodic_map_eq {d : ℕ} {Y : Type*} [MeasurableSpace Y]
    (P L L' : Submodule ℤ (Fin d → ℝ))
    [DiscreteTopology P] [IsZLattice ℝ P]
    [DiscreteTopology L] [IsZLattice ℝ L]
    [DiscreteTopology L'] [IsZLattice ℝ L']
    (hLP : L ≤ P) (hL'P : L' ≤ P) {s t : Set (Fin d → ℝ)}
    (hs : IsAddFundamentalDomain L s volume) (ht : IsAddFundamentalDomain L' t volume)
    (f : (Fin d → ℝ) → Y) (hf : Measurable f)
    (hper : ∀ x p, p ∈ P → f (p+x) = f x) :
    (volume s)⁻¹ • Measure.map f (volume.restrict s) =
      (volume t)⁻¹ • Measure.map f (volume.restrict t) := by
  let F : ((Fin d → ℝ) ⧸ P.toAddSubgroup) → Y := Quotient.lift f (by
    intro u v huv
    have hmem : v-u ∈ P := by
      have h0 := QuotientAddGroup.leftRel_apply.mp huv
      rw [Submodule.mem_toAddSubgroup] at h0
      simpa only [sub_eq_neg_add] using h0
    simpa using (hper u (v-u) hmem).symm)
  have hF : Measurable F := measurable_from_quotient.mpr hf
  have h := congrArg (Measure.map F) (normalizedLatticeQuotientMeasure_eq P L L' hLP hL'P hs ht)
  have he : F ∘ (QuotientAddGroup.mk : _ → (Fin d → ℝ) ⧸ P.toAddSubgroup) = f := rfl
  simpa only [normalizedLatticeQuotientMeasure,Measure.map_smul _ hF.aemeasurable,
    Measure.map_map hF QuotientAddGroup.continuous_mk.measurable,he] using h

 

theorem normalized_periodic_lintegral_eq {d : ℕ}
    (P L L' : Submodule ℤ (Fin d → ℝ))
    [DiscreteTopology P] [IsZLattice ℝ P]
    [DiscreteTopology L] [IsZLattice ℝ L]
    [DiscreteTopology L'] [IsZLattice ℝ L']
    (hLP : L ≤ P) (hL'P : L' ≤ P) {s t : Set (Fin d → ℝ)}
    (hs : IsAddFundamentalDomain L s volume) (ht : IsAddFundamentalDomain L' t volume)
    (f : (Fin d → ℝ) → ℝ≥0∞) (hf : Measurable f)
    (hper : ∀ x p, p ∈ P → f (p+x) = f x) :
    (volume s)⁻¹ * ∫⁻ x in s, f x = (volume t)⁻¹ * ∫⁻ x in t, f x := by
  have h := congrArg (fun measure : Measure ℝ≥0∞ => ∫⁻ x, x ∂measure)
    (normalized_measurable_periodic_map_eq P L L' hLP hL'P hs ht f hf hper)
  simp only [lintegral_smul_measure,smul_eq_mul] at h
  rw [lintegral_map (f := fun x : ℝ≥0∞ => x) measurable_id hf,lintegral_map (f := fun x : ℝ≥0∞ => x) measurable_id hf] at h
  exact h

 

def packetUnitKernel {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) : Subgroup (𝓞 K)ˣ :=
  letI := allSignedGlobalLabelMulAction M σ
  (MulAction.toPermHom (𝓞 K)ˣ (AllSignedGlobalLabel M)).ker

lemma packetUnitKernel_finiteIndex {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n) :
    (packetUnitKernel M σ).FiniteIndex := by
  let := allSignedGlobalLabelMulAction M σ
  let := allSignedGlobalLabel_finite M hn
  change (MulAction.toPermHom (𝓞 K)ˣ (AllSignedGlobalLabel M)).ker.FiniteIndex
  infer_instance

lemma packetUnitKernel_action {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) {u : (𝓞 K)ˣ}
    (hu : u ∈ packetUnitKernel M σ) (x : AllSignedGlobalLabel M) :
    letI := allSignedGlobalLabelMulAction M σ
    u • x = x := by
  let := allSignedGlobalLabelMulAction M σ
  have h : (MulAction.toPermHom (𝓞 K)ˣ (AllSignedGlobalLabel M)) u = 1 := hu
  exact congrArg (fun f : Equiv.Perm (AllSignedGlobalLabel M) => f x) h

lemma allSignedGlobalLabelPoint_unit_action {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (x : AllSignedGlobalLabel M) (u : (𝓞 K)ˣ) :
    letI := allSignedGlobalLabelMulAction M σ
    allSignedGlobalLabelPoint M σ hodd (u • x) =
      orbitMap (allSignedGlobalLabelPoint M σ hodd x) (orderedUnitLog σ (Additive.ofMul u)) := by
  let := allSignedGlobalLabelMulAction M σ
  let := signedGlobalLabelMulAction M σ (classRepresentative K x.1)
  exact signedGlobalLabelPoint_unit_action M σ hn hodd (classRepresentative K x.1) x.2 u

lemma packetUnitKernel_log_le_period {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) (x : AllSignedGlobalLabel M) :
    orderedLogSubgroup σ (packetUnitKernel M σ) ≤
      (periodGroup (allSignedGlobalLabelPoint M σ hodd x)).toIntSubmodule := by
  let := allSignedGlobalLabelMulAction M σ
  intro p hp
  obtain ⟨u,hu,rfl⟩ := (mem_orderedLogSubgroup σ (packetUnitKernel M σ) p).mp hp
  change orbitMap (allSignedGlobalLabelPoint M σ hodd x) (orderedUnitLog σ (Additive.ofMul u)) = _
  rw [← allSignedGlobalLabelPoint_unit_action M σ hn hodd x u,packetUnitKernel_action M σ hu x]

lemma allSignedGlobalLabelPoint_period_isZLattice {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) (x : AllSignedGlobalLabel M) :
    IsZLattice ℝ (periodGroup (allSignedGlobalLabelPoint M σ hodd x)).toIntSubmodule := by
  constructor
  change Submodule.span ℝ ((periodGroup (rightAction (latticePoint (globalLabelLattice M _ x.2.lattice) σ)
    (positiveSignMatrix hodd x.2.signs))).toIntSubmodule : Set (LogCoordinates d)) = ⊤
  rw [periodGroup_rightAction_of_diagonal _ _ (positiveSignMatrix_diagonal hodd x.2.signs)]
  exact (latticePoint_period_isZLattice _ σ hn hodd).span_top

 

lemma signedLabelSum_periodic {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    [Fintype (AllSignedGlobalLabel M)] (f : X (d+1) → ℝ≥0∞)
    (t p : LogCoordinates d) (hp : p ∈ orderedLogSubgroup σ ⊤) :
    ∑ x : AllSignedGlobalLabel M, f (orbitMap (allSignedGlobalLabelPoint M σ hodd x) (p+t)) =
      ∑ x : AllSignedGlobalLabel M, f (orbitMap (allSignedGlobalLabelPoint M σ hodd x) t) := by
  let := allSignedGlobalLabelMulAction M σ
  obtain ⟨u,_,rfl⟩ := (mem_orderedLogSubgroup σ ⊤ p).mp hp
  simp_rw [orbitMap_add,← allSignedGlobalLabelPoint_unit_action M σ hn hodd]
  exact Equiv.sum_comp (MulAction.toPerm u) (fun x : AllSignedGlobalLabel M =>
    f (orbitMap (allSignedGlobalLabelPoint M σ hodd x) t))

 

theorem packetMeasure_lintegral_signedLogAverage {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    [Fintype (AllSignedGlobalLabel M)] {t : Set (LogCoordinates d)}
    (ht : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) t volume)
    (f : X (d+1) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂packetMeasure M σ =
      (Nat.card (AllSignedGlobalLabel M) : ℝ≥0∞)⁻¹ * ((volume t)⁻¹ *
        ∫⁻ u in t, ∑ x : AllSignedGlobalLabel M, f (orbitMap (allSignedGlobalLabelPoint M σ hodd x) u)) := by
  let := packetUnitKernel_finiteIndex M σ hn
  let P := orderedLogSubgroup σ (packetUnitKernel M σ)
  let L := orderedLogSubgroup σ ⊤
  let b := Module.Free.chooseBasis ℤ P
  let s := ZSpan.fundamentalDomain (Module.Basis.ofZLatticeBasis ℝ P b)
  have hs : IsAddFundamentalDomain P s volume := ZLattice.isAddFundamentalDomain b volume
  have hPL : P ≤ L := by
    intro p hp
    obtain ⟨u,_,rfl⟩ := (mem_orderedLogSubgroup σ (packetUnitKernel M σ) p).mp hp
    exact (mem_orderedLogSubgroup σ ⊤ _).mpr ⟨u,Subgroup.mem_top u,rfl⟩
  have hprob (x : AllSignedGlobalLabel M) : orbitProbability (allSignedGlobalLabelPoint M σ hodd x) =
      (volume s)⁻¹ • Measure.map (orbitMap (allSignedGlobalLabelPoint M σ hodd x)) (volume.restrict s) := by
    let := allSignedGlobalLabelPoint_period_isZLattice M σ hn hodd x
    exact orbitProbability_eq_normalized_map_sublattice _ P
      (packetUnitKernel_log_le_period M σ hn hodd x) hs
  rw [packetMeasure_eq_signedLabelAverage M σ hn hodd,lintegral_smul_measure,smul_eq_mul]
  congr 1
  rw [lintegral_sum_measure,tsum_fintype]
  simp_rw [hprob,lintegral_smul_measure,smul_eq_mul]
  have hmap (x : AllSignedGlobalLabel M) :
      ∫⁻ y, f y ∂Measure.map (orbitMap (allSignedGlobalLabelPoint M σ hodd x)) (volume.restrict s) =
        ∫⁻ u in s, f (orbitMap (allSignedGlobalLabelPoint M σ hodd x) u) :=
    lintegral_map hf (continuous_orbitMap _).measurable
  simp_rw [hmap]
  rw [← Finset.mul_sum]
  have hsum := lintegral_finsetSum («μ» := volume.restrict s) Finset.univ
    (f := fun x u => f (orbitMap (allSignedGlobalLabelPoint M σ hodd x) u))
    (fun x _ => hf.comp (continuous_orbitMap _).measurable)
  rw [← hsum]
  apply normalized_periodic_lintegral_eq L P L hPL le_rfl hs ht
  · exact Finset.measurable_sum _ (fun x _ => hf.comp (continuous_orbitMap _).measurable)
  · exact signedLabelSum_periodic M σ hn hodd f

def inverseQuotientHomeomorph (n : ℕ) : X n ≃ₜ (G n ⧸ integralGroup n) where
  toEquiv := QuotientGroup.quotientRightRelEquivQuotientLeftRel (integralGroup n)
  continuous_toFun := by
    apply continuous_quot_lift
    exact continuous_quotient_mk'.comp continuous_inv
  continuous_invFun := by
    apply continuous_quot_lift
    exact continuous_quotient_mk'.comp continuous_inv

instance integralGroup_discrete (n : ℕ) : DiscreteTopology (integralGroup n) := by
  unfold integralGroup
  infer_instance

instance matrixSecondCountable (n : ℕ) :
    SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℝ))

instance matrixLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℝ))

instance gSecondCountable (n : ℕ) : SecondCountableTopology (G n) :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.secondCountableTopology

instance gLocallyCompact (n : ℕ) : LocallyCompactSpace (G n) :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace

instance xT2Space (n : ℕ) : T2Space (X n) :=
  (inverseQuotientHomeomorph n).symm.t2Space

instance xSecondCountable (n : ℕ) : SecondCountableTopology (X n) :=
  (inverseQuotientHomeomorph n).secondCountableTopology

instance xLocallyCompact (n : ℕ) : LocallyCompactSpace (X n) :=
  (inverseQuotientHomeomorph n).isClosedEmbedding.locallyCompactSpace

instance xMetrizable (n : ℕ) : MetrizableSpace (X n) := by infer_instance

 

def integerRowMap {n : ℕ} (g : Matrix (Fin n) (Fin n) ℝ) :
    (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℝ) where
  toFun z := ∑ i, z i • g i
  map_add' z w := by simp [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' a z := by
    simp only [RingHom.id_apply,Pi.smul_apply,Finset.smul_sum,smul_smul,smul_eq_mul]

lemma integerRowMap_apply {n : ℕ} (g : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℤ) :
    integerRowMap g z = Matrix.vecMul (fun i => (z i : ℝ)) g := by
  ext i
  simp [integerRowMap,Matrix.vecMul,dotProduct,Finset.sum_apply,zsmul_eq_mul]

lemma integerRowMap_range {n : ℕ} (g : Matrix (Fin n) (Fin n) ℝ) :
    LinearMap.range (integerRowMap g) = rowLattice g := by
  apply le_antisymm
  · rintro x ⟨z,rfl⟩
    change (∑ i, z i • g i) ∈ Submodule.span ℤ (Set.range fun i => g i)
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i,rfl⟩))
  · apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
    refine ⟨Pi.single i 1,?_⟩
    change (∑ x : Fin n, ((Pi.single i (1:ℤ) : Fin n → ℤ) x) • g x) = g i
    simp only [Pi.single_apply,ite_smul,one_smul,zero_smul]
    simpa only [Finset.mem_univ,ite_true] using Finset.sum_ite_eq' Finset.univ i g

lemma integerRowMap_injective {n : ℕ} (g : G n) :
    Function.Injective (integerRowMap g.1) := by
  intro z w h
  simp only [integerRowMap_apply] at h
  have hunit : IsUnit g.1 := by
    apply (Matrix.isUnit_iff_isUnit_det g.1).mpr
    rw [g.property]
    exact isUnit_one
  have H := Matrix.vecMul_injective_of_isUnit hunit h
  exact funext (fun i => Int.cast_injective (congrFun H i))

 

def integerRowEquiv {n : ℕ} (g : G n) : (Fin n → ℤ) ≃ₗ[ℤ] rowLattice g.1 :=
  (LinearEquiv.ofInjective (integerRowMap g.1) (integerRowMap_injective g)).trans
    (LinearEquiv.ofEq _ _ (integerRowMap_range g.1))

@[simp] lemma integerRowEquiv_val {n : ℕ} (g : G n) (z : Fin n → ℤ) :
    (integerRowEquiv g z : Fin n → ℝ) = integerRowMap g.1 z := rfl

def nonzeroIntegerRowEquiv {n : ℕ} (g : G n) :
    {z : Fin n → ℤ // z ≠ 0} ≃ {v : rowLattice g.1 // (v : Fin n → ℝ) ≠ 0} :=
  (integerRowEquiv g).toEquiv.subtypeEquiv (by
    intro z
    change z ≠ 0 ↔ integerRowMap g.1 z ≠ 0
    constructor
    · intro hz h
      apply hz
      apply integerRowMap_injective g
      exact h.trans (map_zero _).symm
    · rintro hz rfl
      exact hz (map_zero _))

lemma continuous_integerRowMap {n : ℕ} (z : Fin n → ℤ) :
    Continuous (fun g : G n => integerRowMap g.1 z) := by
  change Continuous (fun g : G n => ∑ i, z i • g.1 i)
  apply continuous_finsetSum
  intro i _
  exact ((continuous_apply i).comp Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous).const_smul (z i)

 

def pointLattice {n : ℕ} : X n → Submodule ℤ (Fin n → ℝ) :=
  Quotient.lift (fun g : G n => rowLattice g.1) (by
    intro g h hgh
    have H := QuotientGroup.rightRel_apply.mp hgh
    obtain ⟨A,hA⟩ := H
    have hh : h = Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A * g := by
      rw [hA, inv_mul_cancel_right]
    rw [hh]
    exact (rowLattice_integral_mul A g).symm)

@[simp] lemma pointLattice_mk {n : ℕ} (g : G n) :
    pointLattice (Quotient.mk _ g : X n) = rowLattice g.1 := rfl

 

def siegelTransform {n : ℕ} (f : (Fin n → ℝ) → ℝ≥0∞) (x : X n) : ℝ≥0∞ :=
  ∑' v : {v : pointLattice x // (v : Fin n → ℝ) ≠ 0}, f v.1.1

lemma siegelTransform_mk {n : ℕ} (f : (Fin n → ℝ) → ℝ≥0∞) (g : G n) :
    siegelTransform f (Quotient.mk _ g) =
      ∑' z : {z : Fin n → ℤ // z ≠ 0}, f (integerRowMap g.1 z.1) := by
  change (∑' v : {v : rowLattice g.1 // (v : Fin n → ℝ) ≠ 0}, f v.1.1) = _
  exact ((nonzeroIntegerRowEquiv g).tsum_eq (fun v => f v.1.1)).symm

 

lemma measurable_siegelTransform {n : ℕ} {f : (Fin n → ℝ) → ℝ≥0∞}
    (hf : Measurable f) : Measurable (siegelTransform f) := by
  let : PolishSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (PolishSpace (Fin n → Fin n → ℝ))
  let : PolishSpace (G n) := Matrix.SpecialLinearGroup.isClosedEmbedding_val.polishSpace
  let : MeasurableSpace (G n) := borel (G n)
  let : BorelSpace (G n) := ⟨rfl⟩
  have hq : Measurable (Quotient.mk (QuotientGroup.rightRel (integralGroup n))) :=
    continuous_quotient_mk'.measurable
  apply (hq.measurable_comp_iff_of_surjective Quotient.mk_surjective).mp
  change Measurable (fun g : G n => siegelTransform f (Quotient.mk _ g))
  simp_rw [siegelTransform_mk]
  exact Measurable.tsum (fun z => hf.comp (continuous_integerRowMap z.1).measurable)

lemma pointLattice_latticePoint {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (N : FullLattice n K) (σ : OrderedEmbeddings n K)
    (hn : Module.finrank ℚ K = n) (hodd : Odd n) :
    pointLattice (latticePoint N σ) = normalizedLattice N σ := by
  have H := exists_SL_normalizedLattice N σ hn hodd
  unfold latticePoint
  rw [dite_eq_left H,pointLattice_mk]
  exact H.choose_spec

lemma pointLattice_rightAction_diagonal {n : ℕ} (x : X n) (D : G n) (t : Fin n → ℝ)
    (hD : D.1 = Matrix.diagonal t) :
    pointLattice (rightAction x D) = (pointLattice x).map (diagonalLinear n t) := by
  induction x using Quotient.inductionOn with
  | h g =>
    change rowLattice (g.1*D.1) = (rowLattice g.1).map _
    rw [hD,rowLattice_mul_diagonal]

 

def nonzeroSubmoduleMapEquiv {R V W : Type*} [Semiring R] [AddCommMonoid V]
    [Module R V] [AddCommMonoid W] [Module R W] (S : Submodule R V)
    (F : V →ₗ[R] W) (hF : Function.Injective F) :
    {v : S // (v : V) ≠ 0} ≃ {w : S.map F // (w : W) ≠ 0} :=
  (Submodule.equivMapOfInjective F hF S).toEquiv.subtypeEquiv (by
    intro v
    change (v : V) ≠ 0 ↔ F (v : V) ≠ 0
    constructor
    · intro hv h
      exact hv (hF (h.trans (map_zero F).symm))
    · rintro hv h
      exact hv (h ▸ map_zero F))

lemma tsum_nonzero_submodule_map {R V W : Type*} [Semiring R] [AddCommMonoid V]
    [Module R V] [AddCommMonoid W] [Module R W] (S : Submodule R V)
    (F : V →ₗ[R] W) (hF : Function.Injective F) (f : W → ℝ≥0∞) :
    ∑' w : {w : S.map F // (w : W) ≠ 0}, f w.1.1 =
      ∑' v : {v : S // (v : V) ≠ 0}, f (F v.1.1) :=
  ((nonzeroSubmoduleMapEquiv S F hF).tsum_eq (fun w => f w.1.1)).symm

lemma scaledRealEmbedding_injective {n : ℕ} {K : Type*} [Field K]
    (σ : OrderedEmbeddings n K) (hn : 0 < n) (c : ℝ) (hc : c ≠ 0)
    (t : Fin n → ℝ) (ht : ∀ i, t i ≠ 0) :
    Function.Injective ((diagonalLinear n (fun i => c*t i)).comp (realEmbeddingMap σ)) := by
  intro a b h
  apply realEmbeddingMap_injective σ hn
  ext i
  exact mul_left_cancel₀ (mul_ne_zero hc (ht i)) (congrFun h i)

 

theorem siegelTransform_latticePoint_diagonal {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (N : FullLattice n K) (σ : OrderedEmbeddings n K)
    (hn : Module.finrank ℚ K = n) (hodd : Odd n)
    (D : G n) (t : Fin n → ℝ) (hD : D.1 = Matrix.diagonal t)
    (ht : ∀ i, t i ≠ 0) (f : (Fin n → ℝ) → ℝ≥0∞) :
    siegelTransform f (rightAction (latticePoint N σ) D) =
      ∑' a : {a : N.carrier // (a : K) ≠ 0},
        f (fun i => |(embeddingMatrix N σ).det| ^ (-(1:ℝ)/n) * t i * σ i a.1.1) := by
  let c := |(embeddingMatrix N σ).det| ^ (-(1:ℝ)/n)
  have hc : c ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos
    (abs_pos.mpr (embeddingMatrix_det_ne_zero N σ hn)) _)
  have he : (diagonalLinear n t).comp (diagonalLinear n (fun _ => c)) =
      diagonalLinear n (fun i => c*t i) := by
    ext a i
    simp [diagonalLinear,mul_left_comm,mul_assoc]
  unfold siegelTransform
  rw [pointLattice_rightAction_diagonal _ D t hD,pointLattice_latticePoint N σ hn hodd,
    normalizedLattice_as_map,← Submodule.map_comp,he,← Submodule.map_comp]
  exact tsum_nonzero_submodule_map N.carrier _
    (scaledRealEmbedding_injective σ hodd.pos c hc t ht) f

 

def fullLatticeInclusionMatrix {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (N P : FullLattice n K) (h : N.carrier ≤ P.carrier) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => P.basis.repr ⟨N.basis i, h (N.basis i).property⟩ j

lemma embeddingMatrix_inclusion {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (N P : FullLattice n K) (σ : OrderedEmbeddings n K) (h : N.carrier ≤ P.carrier) :
    embeddingMatrix N σ = (fullLatticeInclusionMatrix N P h).map (Int.castRingHom ℝ) *
      embeddingMatrix P σ := by
  ext i j
  have HH := congrArg (fun x : P.carrier => (x : K))
    (P.basis.sum_repr ⟨N.basis i,h (N.basis i).property⟩)
  simp only [Submodule.coe_sum,Submodule.coe_smul] at HH
  have H := congrArg (σ j) HH
  simp only [map_sum,zsmul_eq_mul,map_mul,map_intCast] at H
  exact H.symm

lemma fullLattice_relIndex_eq_natAbs_det {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (N P : FullLattice n K) (h : N.carrier ≤ P.carrier) :
    N.carrier.toAddSubgroup.relIndex P.carrier.toAddSubgroup =
      (fullLatticeInclusionMatrix N P h).det.natAbs := by
  have H := AddSubgroup.relIndex_eq_natAbs_det N.carrier.toAddSubgroup
    P.carrier.toAddSubgroup h N.basis P.basis
  have he : P.basis.toMatrix (fun i => ⟨N.basis i,h (N.basis i).property⟩) =
      (fullLatticeInclusionMatrix N P h).transpose := by
    ext i j
    rfl
  have hd : P.basis.det (fun i => ⟨N.basis i,h (N.basis i).property⟩) =
      (fullLatticeInclusionMatrix N P h).det := by
    change (P.basis.toMatrix _).det = _
    rw [he,Matrix.det_transpose]
  exact H.trans (congrArg Int.natAbs hd)

 

theorem embeddingMatrix_abs_det_index {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (N P : FullLattice n K) (σ : OrderedEmbeddings n K) (h : N.carrier ≤ P.carrier) :
    |(embeddingMatrix N σ).det| =
      (N.carrier.toAddSubgroup.relIndex P.carrier.toAddSubgroup : ℝ) *
        |(embeddingMatrix P σ).det| := by
  rw [embeddingMatrix_inclusion N P σ h,Matrix.det_mul,abs_mul,
    fullLattice_relIndex_eq_natAbs_det N P h]
  congr 1
  change |((fullLatticeInclusionMatrix N P h).map fun x : ℤ => (x : ℝ)).det| = _
  rw [← Int.cast_det]
  simp only [Nat.cast_natAbs,Int.cast_abs]

 

def nonzeroSubmoduleInclusionEquiv {R V : Type*} [Semiring R] [AddCommMonoid V]
    [Module R V] (N P : Submodule R V) (h : N ≤ P) :
    {a : N // (a : V) ≠ 0} ≃ {a : {a : P // (a : V) ≠ 0} // (a.1 : V) ∈ N} where
  toFun a := ⟨⟨⟨a.1,h a.1.property⟩,a.2⟩,a.1.property⟩
  invFun a := ⟨⟨a.1.1,a.2⟩,a.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma tsum_nonzero_submodule_inclusion {R V : Type*} [Semiring R] [AddCommMonoid V]
    [Module R V] (N P : Submodule R V) (h : N ≤ P) (f : V → ℝ≥0∞) :
    ∑' a : {a : N // (a : V) ≠ 0}, f a.1.1 =
      ∑' a : {a : P // (a : V) ≠ 0}, if (a.1 : V) ∈ N then f a.1.1 else 0 := by
  change _ = ∑' a : {a : P // (a : V) ≠ 0},
    Set.indicator {a | (a.1 : V) ∈ N} (fun a => f a.1.1) a
  rw [← _root_.tsum_subtype]
  exact (nonzeroSubmoduleInclusionEquiv N P h).tsum_eq (fun a => f a.1.1.1)

 

theorem sum_nonzero_submodules {R V ι : Type*} [Semiring R] [AddCommMonoid V]
    [Module R V] [Fintype ι] (N : ι → Submodule R V) (P : Submodule R V)
    (h : ∀ i, N i ≤ P) (f : V → ℝ≥0∞) :
    ∑ i, ∑' a : {a : N i // (a : V) ≠ 0}, f a.1.1 =
      ∑' a : {a : P // (a : V) ≠ 0},
        (Nat.card {i : ι // (a.1 : V) ∈ N i} : ℝ≥0∞) * f a.1.1 := by
  simp_rw [tsum_nonzero_submodule_inclusion _ P (h _) f]
  rw [← tsum_fintype (L := SummationFilter.unconditional ι),ENNReal.tsum_comm]
  apply tsum_congr
  intro a
  rw [tsum_fintype]
  simp only [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]

 

def logFlowWeights {d : ℕ} (u : LogCoordinates d) : Fin (d+1) → ℝ :=
  Fin.snoc (fun i => Real.exp (u i)) (Real.exp (-∑ i, u i))

lemma logFlowWeights_pos {d : ℕ} (u : LogCoordinates d) (i : Fin (d+1)) :
    0 < logFlowWeights u i := by
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [logFlowWeights,Real.exp_pos]

lemma pointLattice_rightAction_signs {n : ℕ} (x : X n) (hn : Odd n)
    (w : Fin n → SignTypeˣ) :
    pointLattice (rightAction x (positiveSignMatrix hn w)) =
      (pointLattice x).map (diagonalLinear n (fun i => signValue (w i))) := by
  induction x using Quotient.inductionOn with
  | h g => exact rowLattice_positiveSignMatrix g.1 hn w

lemma pointLattice_signed_flow {d : ℕ} (x : X (d+1)) (hn : Odd (d+1))
    (w : Fin (d+1) → SignTypeˣ) (u : LogCoordinates d) :
    pointLattice (orbitMap (rightAction x (positiveSignMatrix hn w)) u) =
      (pointLattice x).map (diagonalLinear (d+1) (fun i => signValue (w i)*logFlowWeights u i)) := by
  unfold orbitMap
  rw [pointLattice_rightAction_diagonal _ (diagonalFlow u) (logFlowWeights u) rfl,
    pointLattice_rightAction_signs,← Submodule.map_comp]
  congr 1
  ext a i
  simp [diagonalLinear,mul_left_comm,mul_assoc]

lemma signValue_ne_zero (w : SignTypeˣ) : signValue w ≠ 0 := by
  rcases signValue_eq_one_or_neg_one w with h | h <;> simp [h]

 

theorem siegelTransform_latticePoint_signed_flow {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (N : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (w : Fin (d+1) → SignTypeˣ) (u : LogCoordinates d) (f : (Fin (d+1) → ℝ) → ℝ≥0∞) :
    siegelTransform f (orbitMap (rightAction (latticePoint N σ) (positiveSignMatrix hodd w)) u) =
      ∑' a : {a : N.carrier // (a : K) ≠ 0},
        f (fun i => |(embeddingMatrix N σ).det| ^ (-(1:ℝ)/(d+1:ℕ)) *
          (signValue (w i)*logFlowWeights u i) * σ i a.1.1) := by
  let c := |(embeddingMatrix N σ).det| ^ (-(1:ℝ)/(d+1:ℕ))
  have hc : c ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos
    (abs_pos.mpr (embeddingMatrix_det_ne_zero N σ hn)) _)
  have he : (diagonalLinear (d+1) (fun i => signValue (w i)*logFlowWeights u i)).comp
      (diagonalLinear (d+1) (fun _ => c)) =
      diagonalLinear (d+1) (fun i => c*(signValue (w i)*logFlowWeights u i)) := by
    ext a i
    simp [diagonalLinear,mul_left_comm,mul_assoc]
  unfold siegelTransform
  rw [pointLattice_signed_flow,pointLattice_latticePoint N σ hn hodd,
    normalizedLattice_as_map,← Submodule.map_comp,he,← Submodule.map_comp]
  exact tsum_nonzero_submodule_map N.carrier _
    (scaledRealEmbedding_injective σ (by omega) c hc _
      (fun i => mul_ne_zero (signValue_ne_zero _) (logFlowWeights_pos u i).ne')) f

lemma globalLabel_le_ideal {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (N : globalLabels M I) :
    N.val ≤ (I : Submodule (𝓞 K) K).restrictScalars ℤ := by
  rw [← (globalLabelLattice_spec M I N).1]
  convert le_saturation (globalLabelLattice M I N) using 1
  exact congrArg (fun J : FractionalIdeal (𝓞 K)⁰ K => (J : Submodule (𝓞 K) K).restrictScalars ℤ)
    (globalLabelLattice_spec M I N).2.2.symm

 

theorem globalLabel_abs_det {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (N : globalLabels M I) :
    |(embeddingMatrix (globalLabelLattice M I N) σ).det| =
      (saturationIndex M : ℝ) * |(embeddingMatrix (fractionalIdealFullLattice hn I) σ).det| := by
  have hi : (globalLabelLattice M I N).carrier ≤ (fractionalIdealFullLattice hn I).carrier := by
    rw [(globalLabelLattice_spec M I N).1]
    exact globalLabel_le_ideal M I N
  rw [embeddingMatrix_abs_det_index _ _ σ hi]
  congr 1
  change ((globalLabelLattice M I N).carrier.toAddSubgroup.relIndex
    ((I : Submodule (𝓞 K) K).restrictScalars ℤ).toAddSubgroup : ℝ) = _
  rw [(globalLabelLattice_spec M I N).1,globalLabel_relIndex M hn I N]

lemma relativeElementIdeal_le_one_iff {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : Kˣ) :
    (relativeElementIdeal I a : FractionalIdeal (𝓞 K)⁰ K) ≤ 1 ↔
      (a : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [← FractionalIdeal.spanSingleton_le_iff_mem]
  constructor
  · intro h
    simp only [relativeElementIdeal,Units.val_mul,coe_toPrincipalIdeal] at h
    have H := mul_le_mul_right h (I : FractionalIdeal (𝓞 K)⁰ K)
    rw [mul_comm (I : FractionalIdeal (𝓞 K)⁰ K) (_ * _),mul_assoc,
      Units.inv_mul,mul_one,mul_one] at H
    exact H
  · intro h
    have H := mul_le_mul_right h (↑(I⁻¹) : FractionalIdeal (𝓞 K)⁰ K)
    simpa only [relativeElementIdeal,Units.val_mul,coe_toPrincipalIdeal,Units.mul_inv,Units.inv_mul,mul_comm,mul_left_comm,mul_assoc] using H

lemma relativeElementIdeal_class {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : Kˣ) :
    ClassGroup.mk K (relativeElementIdeal I a) = (ClassGroup.mk K I)⁻¹ := by
  have hp : ClassGroup.mk K (toPrincipalIdeal (𝓞 K) K a) = 1 := by
    exact ClassGroup.mk_eq_one_iff.mpr (by
      rw [coe_toPrincipalIdeal,FractionalIdeal.coe_spanSingleton]
      exact ⟨⟨(a : K),rfl⟩⟩)
  simp only [relativeElementIdeal,map_mul,hp,map_inv,one_mul]

lemma relativeElementIdeal_eq_iff {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a b : Kˣ) :
    relativeElementIdeal I a = relativeElementIdeal I b ↔
      ∃ z : (𝓞 K)ˣ, z • (a : K) = (b : K) := by
  rw [relativeElementIdeal,relativeElementIdeal,mul_right_cancel_iff,Units.ext_iff,
    coe_toPrincipalIdeal,coe_toPrincipalIdeal,FractionalIdeal.spanSingleton_eq_spanSingleton]

 

def integralIdealClassFiber {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :=
  {J : (FractionalIdeal (𝓞 K)⁰ K)ˣ //
    (J : FractionalIdeal (𝓞 K)⁰ K) ≤ 1 ∧ ClassGroup.mk K J = (ClassGroup.mk K I)⁻¹}

 

def nonzeroIdealElements {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :=
  {a : Kˣ // (a : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K)}

def relativeElementClassMap {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : nonzeroIdealElements I) : integralIdealClassFiber I :=
  ⟨relativeElementIdeal I a.val,(relativeElementIdeal_le_one_iff I a.val).mpr a.property,
    relativeElementIdeal_class I a.val⟩

theorem relativeElementClassMap_surjective {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Function.Surjective (relativeElementClassMap I) := by
  intro J
  have hclass : ClassGroup.mk K I⁻¹ = ClassGroup.mk K J.val := by rw [map_inv,J.property.2]
  obtain ⟨a,ha,h⟩ := (fractionalIdeal_same_class I⁻¹ J.val).mp hclass
  have he : relativeElementIdeal I (Units.mk0 a ha) = J.val := by
    apply Units.ext
    simpa only [relativeElementIdeal,Units.val_mul,coe_toPrincipalIdeal,Units.val_mk0] using h
  refine ⟨⟨Units.mk0 a ha,?_⟩,Subtype.ext he⟩
  apply (relativeElementIdeal_le_one_iff I _).mp
  rw [he]
  exact J.property.1

 

def idealElementRepresentative {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (J : integralIdealClassFiber I) : nonzeroIdealElements I :=
  (relativeElementClassMap_surjective I J).choose

lemma idealElementRepresentative_spec {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (J : integralIdealClassFiber I) :
    relativeElementClassMap I (idealElementRepresentative I J) = J :=
  (relativeElementClassMap_surjective I J).choose_spec

 

def idealElementUnitAction {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (z : (𝓞 K)ˣ) (a : nonzeroIdealElements I) :
    nonzeroIdealElements I :=
  ⟨Units.map (algebraMap (𝓞 K) K).toMonoidHom z * a.val,
    show z • (a.val : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K) from
      (I : Submodule (𝓞 K) K).smul_mem (z : 𝓞 K) a.property⟩

lemma relativeElementClassMap_unitAction {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (z : (𝓞 K)ˣ) (a : nonzeroIdealElements I) :
    relativeElementClassMap I (idealElementUnitAction I z a) = relativeElementClassMap I a := by
  apply Subtype.ext
  apply ((relativeElementIdeal_eq_iff I a.val _).mpr ⟨z,rfl⟩).symm

lemma idealElementUnitAction_injective {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : nonzeroIdealElements I) :
    Function.Injective (fun z : (𝓞 K)ˣ => idealElementUnitAction I z a) := by
  intro z w h
  have he := congrArg (fun b : nonzeroIdealElements I => b.val) h
  change Units.map (algebraMap (𝓞 K) K).toMonoidHom z * a.val =
    Units.map (algebraMap (𝓞 K) K).toMonoidHom w * a.val at he
  have hh := congrArg (fun b : Kˣ => (b : K)) (mul_right_cancel he)
  apply Units.ext
  exact (IsFractionRing.injective (𝓞 K) K) hh

 

theorem exists_unique_unit_of_relativeElementClassMap_eq
    {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a b : nonzeroIdealElements I)
    (h : relativeElementClassMap I a = relativeElementClassMap I b) :
    ∃! z : (𝓞 K)ˣ, idealElementUnitAction I z a = b := by
  obtain ⟨z,hz⟩ := (relativeElementIdeal_eq_iff I a.val b.val).mp
    (congrArg Subtype.val h)
  refine ⟨z,?_,?_⟩
  · apply Subtype.ext
    apply Units.ext
    exact hz
  · intro w hw
    apply idealElementUnitAction_injective I a
    exact hw.trans (by apply Subtype.ext; apply Units.ext; exact hz.symm)

def idealElementDecompositionMap {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (Σ _J : integralIdealClassFiber I, (𝓞 K)ˣ) → nonzeroIdealElements I :=
  fun x => idealElementUnitAction I x.2 (idealElementRepresentative I x.1)

 

def idealElementDecomposition {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (Σ _J : integralIdealClassFiber I, (𝓞 K)ˣ) ≃ nonzeroIdealElements I :=
  Equiv.ofBijective (idealElementDecompositionMap I) (by
    constructor
    · rintro ⟨J,z⟩ ⟨L,w⟩ h
      have he := congrArg (relativeElementClassMap I) h
      simp only [idealElementDecompositionMap,relativeElementClassMap_unitAction,
        idealElementRepresentative_spec] at he
      subst L
      have hz : z = w := idealElementUnitAction_injective I _ h
      subst w
      rfl
    · intro a
      let J := relativeElementClassMap I a
      obtain ⟨z,hz,_⟩ := exists_unique_unit_of_relativeElementClassMap_eq I
        (idealElementRepresentative I J) a (idealElementRepresentative_spec I J)
      exact ⟨⟨J,z⟩,hz⟩)

 

def nonzeroIdealElementEquiv {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    {a : (I : Submodule (𝓞 K) K).restrictScalars ℤ // (a : K) ≠ 0} ≃
      nonzeroIdealElements I where
  toFun a := ⟨Units.mk0 a.1.1 a.2,a.1.2⟩
  invFun a := ⟨⟨a.1,a.2⟩,a.1.ne_zero⟩
  left_inv _ := rfl
  right_inv a := by apply Subtype.ext; apply Units.ext; rfl

 

theorem globalLabel_siegelTransform_average {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) [Fintype (globalLabels M I)]
    (w : Fin (d+1) → SignTypeˣ) (u : LogCoordinates d) (f : (Fin (d+1) → ℝ) → ℝ≥0∞) :
    (Nat.card (globalLabels M I) : ℝ≥0∞)⁻¹ *
      ∑ N : globalLabels M I, siegelTransform f
        (orbitMap (signedGlobalLabelPoint M σ hodd I ⟨N,w⟩) u) =
      ∑' a : nonzeroIdealElements I, globalIdealWeight M (relativeElementIdeal I a.1) *
        f (fun i => ((saturationIndex M : ℝ) *
          |(embeddingMatrix (fractionalIdealFullLattice hn I) σ).det|) ^ (-(1:ℝ)/(d+1:ℕ)) *
          (signValue (w i)*logFlowWeights u i) * σ i a.1.1) := by
  let c := ((saturationIndex M : ℝ) *
    |(embeddingMatrix (fractionalIdealFullLattice hn I) σ).det|) ^ (-(1:ℝ)/(d+1:ℕ))
  let F : K → ℝ≥0∞ := fun a => f (fun i => c * (signValue (w i)*logFlowWeights u i) * σ i a)
  have he (N : globalLabels M I) : siegelTransform f
        (orbitMap (signedGlobalLabelPoint M σ hodd I ⟨N,w⟩) u) =
      ∑' a : {a : N.val // (a : K) ≠ 0}, F a.1.1 := by
    unfold signedGlobalLabelPoint
    rw [siegelTransform_latticePoint_signed_flow _ σ hn hodd w u f,globalLabel_abs_det M σ hn I N]
    change (∑' a : {a : (globalLabelLattice M I N).carrier // (a : K) ≠ 0}, F a.1.1) = _
    rw [(globalLabelLattice_spec M I N).1]
  simp_rw [he]
  rw [sum_nonzero_submodules _ ((I : Submodule (𝓞 K) K).restrictScalars ℤ)
    (globalLabel_le_ideal M I) F,← ENNReal.tsum_mul_left]
  rw [← (nonzeroIdealElementEquiv I).tsum_eq]
  apply tsum_congr
  intro a
  rw [← mul_assoc,mul_comm ((Nat.card (globalLabels M I) : ℝ≥0∞)⁻¹),← div_eq_mul_inv]
  change _ * F a.1.1 = globalIdealWeight M (relativeElementIdeal I (Units.mk0 a.1.1 a.2)) * F a.1.1
  congr 1
  exact globalContainment_eq_relativeIdealWeight M hn I (Units.mk0 a.1.1 a.2) a.1.2

 

theorem tsum_comp_surjective_addHom {A B : Type*} [AddGroup A] [AddGroup B]
    (additiveMap : A →+ B) (hφ : Function.Surjective additiveMap) [Finite additiveMap.ker]
    (f : B → ℝ≥0∞) :
    (∑' a, f (additiveMap a)) = (Nat.card additiveMap.ker : ℝ≥0∞) * ∑' b, f b := by
  rw [← ENNReal.tsum_fiberwise (fun a => f (additiveMap a)) additiveMap,← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro b
  let e := AddMonoidHom.fiberEquivKerOfSurjective hφ b
  let := Fintype.ofFinite additiveMap.ker
  let := Fintype.ofEquiv additiveMap.ker e.symm
  calc
    (∑' a : additiveMap ⁻¹' {b}, f (additiveMap a)) = ∑' _a : additiveMap ⁻¹' {b}, f b := by
      apply tsum_congr
      intro a
      rw [show additiveMap a = b from a.property]
    _ = (Nat.card additiveMap.ker : ℝ≥0∞) * f b := by
      rw [tsum_fintype,Finset.sum_const,nsmul_eq_mul,Finset.card_univ,
        ← Nat.card_eq_fintype_card,Nat.card_congr e]

 

theorem lintegral_tsum_addHom_fundamentalDomain {d : ℕ} {A : Type*} [AddGroup A]
    (L : Submodule ℤ (Fin d → ℝ)) [Countable L]
    (additiveMap : A →+ L) (hφ : Function.Surjective additiveMap) [Finite additiveMap.ker]
    {t : Set (Fin d → ℝ)} (ht : IsAddFundamentalDomain L t volume)
    (f : (Fin d → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ u in t, ∑' a, f ((additiveMap a : Fin d → ℝ)+u)) =
      (Nat.card additiveMap.ker : ℝ≥0∞) * ∫⁻ v, f v := by
  have he (u : Fin d → ℝ) : (∑' a, f ((additiveMap a : Fin d → ℝ)+u)) =
      (Nat.card additiveMap.ker : ℝ≥0∞) * ∑' p : L, f ((p : Fin d → ℝ)+u) :=
    tsum_comp_surjective_addHom additiveMap hφ (fun p => f ((p : Fin d → ℝ)+u))
  have : VAddInvariantMeasure L (Fin d → ℝ) volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup (Fin d → ℝ) volume)
  simp_rw [he]
  rw [lintegral_const_mul _ (by fun_prop)]
  congr 1
  rw [ht.lintegral_eq_tsum'' f]
  exact lintegral_tsum (fun p => (hf.comp (measurable_const.add measurable_id)).aemeasurable)

 

def signedFlowSum {d : ℕ} (f : (Fin (d+1) → ℝ) → ℝ≥0∞)
    (v : Fin (d+1) → ℝ) (u : LogCoordinates d) : ℝ≥0∞ :=
  ∑ w : Fin (d+1) → SignTypeˣ, f (fun i => signValue (w i)*logFlowWeights u i*v i)

lemma logFlowWeights_add {d : ℕ} (u t : LogCoordinates d) :
    logFlowWeights (u+t) = logFlowWeights u * logFlowWeights t := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [logFlowWeights,Real.exp_add,Finset.sum_add_distrib,mul_comm]

lemma continuous_logFlowWeights {d : ℕ} : Continuous (@logFlowWeights d) := by
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [logFlowWeights,Fin.snoc_last,Fin.snoc_castSucc]
  · fun_prop
  · fun_prop

lemma measurable_signedFlowSum {d : ℕ} {f : (Fin (d+1) → ℝ) → ℝ≥0∞}
    (hf : Measurable f) (v : Fin (d+1) → ℝ) : Measurable (signedFlowSum f v) := by
  unfold signedFlowSum
  apply Finset.measurable_sum
  intro w _
  exact hf.comp (Measurable.of_eval (fun i =>
    (((measurable_pi_apply i).comp continuous_logFlowWeights.measurable).const_mul _).mul_const _))

lemma signedFlowSum_sign_log_translate {d : ℕ} (f : (Fin (d+1) → ℝ) → ℝ≥0∞)
    (v : Fin (d+1) → ℝ) (s : Fin (d+1) → SignTypeˣ) (p u : LogCoordinates d) :
    signedFlowSum f (fun i => signValue (s i)*logFlowWeights p i*v i) u =
      signedFlowSum f v (p+u) := by
  have he := Equiv.sum_comp (Equiv.mulLeft s)
    (fun w : Fin (d+1) → SignTypeˣ => f (fun i => signValue (w i)*logFlowWeights (p+u) i*v i))
  unfold signedFlowSum
  rw [← he]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  ext i
  simp only [Equiv.coe_mulLeft,Pi.mul_apply,map_mul,logFlowWeights_add]
  ring

lemma logFlowWeights_orderedUnitLog {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K) (z : (𝓞 K)ˣ) :
    logFlowWeights (orderedUnitLog σ (Additive.ofMul z)) = fun i => |σ i (z : K)| := by
  have h := diagonalFlow_abs_orderedUnitLog σ z
  have H (i : Fin (d+1)) := congrArg (fun A : Matrix (Fin (d+1)) (Fin (d+1)) ℝ => A i i) h
  funext i
  exact by simpa only [diagonalFlow,logFlowWeights,Matrix.diagonal_apply_eq] using H i

 

lemma signedFlowSum_mul_unit {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (f : (Fin (d+1) → ℝ) → ℝ≥0∞) (c : ℝ) (a : K) (z : (𝓞 K)ˣ) (u : LogCoordinates d) :
    signedFlowSum f (fun i => c*σ i ((z : K)*a)) u =
      signedFlowSum f (fun i => c*σ i a) (orderedUnitLog σ (Additive.ofMul z)+u) := by
  rw [← signedFlowSum_sign_log_translate f (fun i => c*σ i a) (unitSigns σ z)]
  congr 1
  ext i
  rw [logFlowWeights_orderedUnitLog,signValue_unitSigns,map_mul]
  ring

 

def orderedUnitLogOnto {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K) :
    Additive ((𝓞 K)ˣ) →+ orderedLogSubgroup σ ⊤ :=
  (orderedUnitLog σ).codRestrict (orderedLogSubgroup σ ⊤).toAddSubgroup
    (fun u => (mem_orderedLogSubgroup σ ⊤ _).mpr ⟨u.toMul,Subgroup.mem_top _,rfl⟩)

lemma orderedUnitLogOnto_surjective {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K) :
    Function.Surjective (orderedUnitLogOnto σ) := by
  intro p
  obtain ⟨u,_,hu⟩ := (mem_orderedLogSubgroup σ ⊤ p.val).mp p.property
  exact ⟨Additive.ofMul u,Subtype.ext hu⟩

lemma orderedUnitLogOnto_ker {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K) :
    (orderedUnitLogOnto σ).ker = (NumberField.Units.torsion K).toAddSubgroup := by
  rw [orderedUnitLogOnto,AddMonoidHom.ker_codRestrict,orderedUnitLog_ker]

lemma orderedUnitLogOnto_ker_card {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hodd : Odd (Module.finrank ℚ K)) : Nat.card (orderedUnitLogOnto σ).ker = 2 := by
  rw [orderedUnitLogOnto_ker]
  let e : (NumberField.Units.torsion K).toAddSubgroup ≃ NumberField.Units.torsion K :=
    ⟨(fun u => ⟨u.val.toMul,u.property⟩),(fun u => ⟨Additive.ofMul u.val,u.property⟩),
      (fun _ => rfl),(fun _ => rfl)⟩
  rw [Nat.card_congr e]
  exact NumberField.Units.torsionOrder_eq_two_of_odd_finrank hodd

 

theorem lintegral_signedFlowSum_unit {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hodd : Odd (Module.finrank ℚ K))
    {t : Set (LogCoordinates d)} (ht : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) t volume)
    (f : (Fin (d+1) → ℝ) → ℝ≥0∞) (hf : Measurable f) (c : ℝ) (a : K) :
    (∫⁻ u in t, ∑' z : (𝓞 K)ˣ, signedFlowSum f (fun i => c*σ i ((z : K)*a)) u) =
      2 * ∫⁻ u, signedFlowSum f (fun i => c*σ i a) u := by
  simp_rw [signedFlowSum_mul_unit σ f c a]
  let unitLog := orderedUnitLogOnto σ
  let : Finite unitLog.ker := Nat.finite_of_card_ne_zero (by rw [orderedUnitLogOnto_ker_card σ hodd]; decide)
  have he := lintegral_tsum_addHom_fundamentalDomain (orderedLogSubgroup σ ⊤) unitLog
    (orderedUnitLogOnto_surjective σ) ht (signedFlowSum f (fun i => c*σ i a))
    (measurable_signedFlowSum hf _)
  rw [orderedUnitLogOnto_ker_card σ hodd] at he
  exact he

 

def productFiberVector {d : ℕ} (z : ℝ) : Fin (d+1) → ℝ := Fin.snoc (fun _ => 1) z

 

def productFiberIntegral {d : ℕ} (f : (Fin (d+1) → ℝ) → ℝ≥0∞) (z : ℝ) : ℝ≥0∞ :=
  ∑ w : Fin (d+1) → SignTypeˣ, ∫⁻ u : LogCoordinates d,
    f (Fin.snoc (fun i => signValue (w i.castSucc)*Real.exp (u i))
      (signValue (w (Fin.last d))*z*Real.exp (-∑ i, u i)))

lemma lintegral_signedFlowSum_productFiberVector {d : ℕ}
    (f : (Fin (d+1) → ℝ) → ℝ≥0∞) (hf : Measurable f) (z : ℝ) :
    (∫⁻ u, signedFlowSum f (productFiberVector z) u) = productFiberIntegral f z := by
  unfold signedFlowSum productFiberIntegral
  rw [lintegral_finsetSum _ (by
    intro w _
    exact hf.comp (Measurable.of_eval (fun i =>
      (((measurable_pi_apply i).comp continuous_logFlowWeights.measurable).const_mul _).mul_const _)))]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  funext u
  congr 1
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [productFiberVector,logFlowWeights,mul_comm,mul_left_comm]

 

theorem lintegral_signedFlowSum_eq_productFiberIntegral {d : ℕ}
    (f : (Fin (d+1) → ℝ) → ℝ≥0∞) (hf : Measurable f)
    (v : Fin (d+1) → ℝ) (hv : ∀ i, v i ≠ 0) :
    (∫⁻ u, signedFlowSum f v u) = productFiberIntegral f (∏ i, |v i|) := by
  let p : LogCoordinates d := fun i => Real.log |v i.castSucc|
  let s : Fin (d+1) → SignTypeˣ := fun i =>
    Units.map (signHom : ℝ →*₀ SignType).toMonoidHom (Units.mk0 (v i) (hv i))
  have hs (i : Fin (d+1)) : signValue (s i) * |v i| = v i := sign_mul_abs _
  have hp : logFlowWeights p (Fin.last d) = (∏ i : Fin d, |v i.castSucc|)⁻¹ := by
    simp only [logFlowWeights,Fin.snoc_last,Real.exp_neg,Real.exp_sum]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    exact Real.exp_log (abs_pos.mpr (hv _))
  have hp0 : (∏ i : Fin d, |v i.castSucc|) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => abs_ne_zero.mpr (hv _))
  have he : v = fun i => signValue (s i)*logFlowWeights p i*productFiberVector (∏ j, |v j|) i := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [productFiberVector,Fin.snoc_last,hp,Fin.prod_univ_castSucc]
      rw [mul_assoc,inv_mul_cancel_left₀ hp0,hs]
    · simp only [productFiberVector,Fin.snoc_castSucc,logFlowWeights,p,mul_one]
      rw [Real.exp_log (abs_pos.mpr (hv _)),hs]
  conv_lhs => rw [he]
  simp_rw [signedFlowSum_sign_log_translate]
  rw [lintegral_add_left_eq_self,lintegral_signedFlowSum_productFiberVector f hf]

 

lemma tsum_relativeElementIdeal {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (W : (FractionalIdeal (𝓞 K)⁰ K)ˣ → ℝ≥0∞) (F : K → ℝ≥0∞) :
    (∑' a : nonzeroIdealElements I, W (relativeElementIdeal I a.1) * F a.1.1) =
      ∑' J : integralIdealClassFiber I, W J.1 *
        ∑' z : (𝓞 K)ˣ, F ((z : K)*(idealElementRepresentative I J).1.1) := by
  rw [← (idealElementDecomposition I).tsum_eq,ENNReal.tsum_sigma']
  apply tsum_congr
  intro J
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro z
  have h := congrArg Subtype.val ((relativeElementClassMap_unitAction I z
    (idealElementRepresentative I J)).trans (idealElementRepresentative_spec I J))
  change W (relativeElementIdeal I (idealElementUnitAction I z (idealElementRepresentative I J)).1) *
    F ((z : K)*(idealElementRepresentative I J).1.1) = _
  rw [show relativeElementIdeal I (idealElementUnitAction I z (idealElementRepresentative I J)).1 = J.1 from h]

 

theorem lintegral_weighted_idealElements {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hodd : Odd (Module.finrank ℚ K))
    {t : Set (LogCoordinates d)} (ht : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) t volume)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (W : (FractionalIdeal (𝓞 K)⁰ K)ˣ → ℝ≥0∞)
    (f : (Fin (d+1) → ℝ) → ℝ≥0∞) (hf : Measurable f) (c : ℝ) (hc : c ≠ 0) :
    (∫⁻ u in t, ∑' a : nonzeroIdealElements I,
      W (relativeElementIdeal I a.1)*signedFlowSum f (fun i => c*σ i a.1.1) u) =
      2 * ∑' J : integralIdealClassFiber I, W J.1 *
        productFiberIntegral f (∏ i, |c*σ i (idealElementRepresentative I J).1.1|) := by
  let : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable (𝓞 K) := RingOfIntegers.coe_injective.countable
  let : Countable Kˣ := Units.val_injective.countable
  let : Countable (𝓞 K)ˣ := Units.val_injective.countable
  let : Countable (nonzeroIdealElements I) := by
    change Countable {a : Kˣ // (a : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K)}
    infer_instance
  let : Countable (integralIdealClassFiber I) := (relativeElementClassMap_surjective I).countable
  have he (u : LogCoordinates d) := tsum_relativeElementIdeal I W
    (fun a => signedFlowSum f (fun i => c*σ i a) u)
  simp_rw [he]
  rw [lintegral_tsum (fun J => ((Measurable.tsum (fun z : (𝓞 K)ˣ =>
    measurable_signedFlowSum hf (fun i => c*σ i ((z : K)*(idealElementRepresentative I J).1.1)))).const_mul _).aemeasurable)]
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro J
  rw [lintegral_const_mul _ (Measurable.tsum (fun z : (𝓞 K)ˣ => measurable_signedFlowSum hf _)),
    lintegral_signedFlowSum_unit σ hodd ht f hf c,
    lintegral_signedFlowSum_eq_productFiberIntegral f hf _ (fun i =>
      mul_ne_zero hc (by simpa only [_root_.map_zero] using (σ i).injective.ne (idealElementRepresentative I J).1.ne_zero))]
  ring

lemma logSubgroup_top {K : Type*} [Field K] [NumberField K] :
    logSubgroup (⊤ : Subgroup (𝓞 K)ˣ) = NumberField.Units.unitLattice K := rfl

 

def orderedDeletedPlacesEquiv {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K) :
    Fin d ≃ {w : NumberField.InfinitePlace K // w ≠ orderedRealPlaces σ (Fin.last d)} :=
  (finSuccAboveEquiv (Fin.last d)).trans
    ((orderedRealPlaces σ).subtypeEquiv (fun _ => not_congr (orderedRealPlaces σ).injective.eq_iff.symm))

lemma orderedUnitRank {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K) :
    NumberField.Units.rank K = d := by
  rw [← NumberField.Units.finrank_eq_rank]
  rw [(orderedLogCoordinatesEquiv σ).finrank_eq]
  simp

 

theorem orderedLogSubgroup_covolume_eq_regulator {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K) :
    ZLattice.covolume (orderedLogSubgroup σ ⊤) = NumberField.Units.regulator K := by
  let ec := orderedLogCoordinatesEquiv σ
  let er : Fin (NumberField.Units.rank K) ≃ Fin d := finCongr (orderedUnitRank σ)
  let b := ((NumberField.Units.basisUnitLattice K).ofZLatticeComap ℝ
    (NumberField.Units.unitLattice K) ec.symm).reindex er
  have hb : ∀ i j, (b i : Fin d → ℝ) j =
      Real.log |σ j.castSucc (NumberField.Units.fundSystem K (er.symm i) : K)| := by
    intro i j
    simp only [b,Basis.reindex_apply,Basis.ofZLatticeComap_apply,LinearEquiv.symm_symm]
    rw [← NumberField.Units.logEmbedding_fundSystem]
    exact orderedUnitLog_apply σ _ j
  let : DiscreteTopology (ZLattice.comap ℝ (NumberField.Units.unitLattice K) ec.symm.toLinearMap) :=
    ZLattice.comap_discreteTopology ℝ _ ec.symm.toContinuousLinearEquiv.continuous ec.symm.injective
  let : IsZLattice ℝ (ZLattice.comap ℝ (NumberField.Units.unitLattice K) ec.symm.toLinearMap) :=
    instIsZLatticeComap ℝ _ ec.symm.toContinuousLinearEquiv
  change ZLattice.covolume (ZLattice.comap ℝ (logSubgroup ⊤) ec.symm.toLinearMap) = _
  rw [logSubgroup_top,ZLattice.covolume_eq_det _ b]
  let ep := orderedDeletedPlacesEquiv σ
  have hr := NumberField.Units.regulator_eq_det K (orderedRealPlaces σ (Fin.last d))
    (ep.symm.trans er.symm)
  rw [hr]
  congr 1
  let A : Matrix {w : NumberField.InfinitePlace K // w ≠ orderedRealPlaces σ (Fin.last d)}
      {w : NumberField.InfinitePlace K // w ≠ orderedRealPlaces σ (Fin.last d)} ℝ :=
    fun i w => (NumberField.InfinitePlace.mult w.val : ℝ) *
      Real.log (w.val (NumberField.Units.fundSystem K ((ep.symm.trans er.symm) i) : K))
  change (Matrix.of ((↑) ∘ b)).det = A.det
  rw [← Matrix.det_reindex_self ep.symm A]
  congr 1
  ext i j
  change (b i : Fin d → ℝ) j =
    ((ep j).val.mult : ℝ)*Real.log ((ep j).val
      (NumberField.Units.fundSystem K (er.symm (ep.symm (ep i))) : K))
  rw [hb,Equiv.symm_apply_apply,(NumberField.IsTotallyReal.isReal _).mult_eq_one]
  simp only [Nat.cast_one,one_mul,ep,orderedDeletedPlacesEquiv,Equiv.trans_apply,
    Equiv.subtypeEquiv_apply,finSuccAboveEquiv_apply,Fin.succAbove_last,orderedRealPlaces_apply]

 

def integralFractionalIdeals (K : Type*) [Field K] [NumberField K] :=
  {J : (FractionalIdeal (𝓞 K)⁰ K)ˣ // (J : FractionalIdeal (𝓞 K)⁰ K) ≤ 1}

 

def idealClassPartitionEquiv (K : Type*) [Field K] [NumberField K] :
    (Σ c : ClassGroup (𝓞 K), integralIdealClassFiber (classRepresentative K c)) ≃
      integralFractionalIdeals K where
  toFun x := ⟨x.2.1,x.2.2.1⟩
  invFun J := ⟨(ClassGroup.mk K J.1)⁻¹,
    ⟨J.1,J.2,by rw [classRepresentative_spec,inv_inv]⟩⟩
  left_inv := by
    rintro ⟨c,J⟩
    have h : (ClassGroup.mk K J.1)⁻¹ = c := by rw [J.2.2,classRepresentative_spec,inv_inv]
    apply Sigma.ext h
    exact (Subtype.heq_iff_coe_eq (fun x => by
      change (x.val ≤ 1 ∧ ClassGroup.mk K x = (ClassGroup.mk K (classRepresentative K ((ClassGroup.mk K J.val)⁻¹)))⁻¹) ↔ _
      rw [h])).mpr rfl
  right_inv _ := rfl

lemma tsum_idealClassPartition (K : Type*) [Field K] [NumberField K]
    (F : (FractionalIdeal (𝓞 K)⁰ K)ˣ → ℝ≥0∞) :
    (∑' c : ClassGroup (𝓞 K), ∑' J : integralIdealClassFiber (classRepresentative K c), F J.1) =
      ∑' J : integralFractionalIdeals K, F J.1 := by
  calc
    _ = ∑' x : (Σ c : ClassGroup (𝓞 K), integralIdealClassFiber (classRepresentative K c)), F x.2.1 :=
      (ENNReal.tsum_sigma' (fun x : (Σ c : ClassGroup (𝓞 K), integralIdealClassFiber (classRepresentative K c)) => F x.2.1)).symm
    _ = _ := (idealClassPartitionEquiv K).tsum_eq (fun J : integralFractionalIdeals K => F J.val)

 

def integralFractionalIdealsEquiv (K : Type*) [Field K] [NumberField K] :
    {J : Ideal (𝓞 K) // J ≠ ⊥} ≃ integralFractionalIdeals K :=
  Equiv.ofBijective (fun J =>
    ⟨Units.mk0 (J.1 : FractionalIdeal (𝓞 K)⁰ K) (by simpa using J.2),FractionalIdeal.coeIdeal_le_one⟩)
    ⟨by
      intro J L h
      apply Subtype.ext
      apply FractionalIdeal.coeIdeal_injective (K := K)
      exact congrArg (fun a : integralFractionalIdeals K => a.1.val) h,
    by
      rintro ⟨J,hJ⟩
      obtain ⟨I,hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hJ
      have hI0 : I ≠ ⊥ := by
        intro he
        subst I
        simp only [FractionalIdeal.coeIdeal_bot] at hI
        exact J.ne_zero hI.symm
      refine ⟨⟨I,hI0⟩,?_⟩
      apply Subtype.ext
      apply Units.ext
      exact hI⟩

lemma tsum_integralFractionalIdeals (K : Type*) [Field K] [NumberField K]
    (F : FractionalIdeal (𝓞 K)⁰ K → ℝ≥0∞) :
    (∑' J : integralFractionalIdeals K, F J.1) = ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥}, F J.1 :=
  ((integralFractionalIdealsEquiv K).tsum_eq (fun J => F J.1)).symm

 

def orderedComplexEmbeddings {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n) : Fin n ≃ (K →ₐ[ℚ] ℂ) :=
  Equiv.ofBijective (fun i => RingHom.equivRatAlgHom K ℂ (Complex.ofRealHom.comp (σ i)))
    (Fintype.bijective_iff_injective_and_card _ |>.mpr ⟨by
      intro i j h
      apply σ.injective
      ext a
      apply Complex.ofReal_injective
      exact congrArg (fun f : K →ₐ[ℚ] ℂ => f a) h,
      by rw [Fintype.card_fin,AlgHom.card,hn]⟩)

lemma integralEmbeddingMatrix_det_sq {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n)
    (b : Basis (Fin n) ℤ (𝓞 K)) :
    (Matrix.det (fun i j => σ j (b i)))^2 = (NumberField.discr K : ℝ) := by
  let bQ := b.localizationLocalization ℚ ℤ⁰ K
  let B : Matrix (Fin n) (Fin n) ℝ := fun i j => σ j (b i)
  have h := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ bQ (orderedComplexEmbeddings σ hn)
  have hm : Algebra.embeddingsMatrixReindex ℚ ℂ bQ (orderedComplexEmbeddings σ hn) =
      B.map Complex.ofRealHom := by
    ext i j
    change Complex.ofReal (σ j (bQ i)) = Complex.ofReal (σ j (b i))
    rw [show bQ i = (algebraMap (𝓞 K) K) (b i) from b.localizationLocalization_apply ℚ ℤ⁰ K i]
  rw [hm,show (B.map Complex.ofRealHom).det = Complex.ofRealHom B.det from
    (Complex.ofRealHom.map_det B).symm] at h
  have hd : Algebra.discr ℚ bQ = (NumberField.discr K : ℚ) := by
    dsimp only [bQ]
    rw [Algebra.discr_localizationLocalization,NumberField.discr_eq_discr]
    rfl
  rw [hd] at h
  apply Complex.ofReal_injective
  simpa only [B,map_intCast,Complex.ofRealHom_eq_coe,Complex.ofReal_intCast,Complex.ofReal_pow] using h.symm

lemma embeddingMatrix_det_basisChange {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K)
    (b : Basis (Fin n) ℚ K) :
    (embeddingMatrix M σ).det = (b.det (fun i => (M.basis i : K)) : ℝ)*
      Matrix.det (fun i j => σ j (b i)) := by
  let C := b.toMatrix (fun i => (M.basis i : K))
  let B : Matrix (Fin n) (Fin n) ℝ := fun i j => σ j (b i)
  have hm : embeddingMatrix M σ = C.transpose.map (algebraMap ℚ ℝ) * B := by
    ext i j
    have h := congrArg (σ j) (b.sum_repr (M.basis i : K))
    simp only [Algebra.smul_def,map_sum,map_mul,RingHom.map_rat_algebraMap] at h
    exact h.symm
  rw [hm,Matrix.det_mul,show (C.transpose.map (algebraMap ℚ ℝ)).det =
    algebraMap ℚ ℝ C.transpose.det from ((algebraMap ℚ ℝ).map_det C.transpose).symm,
    Matrix.det_transpose]
  rfl

 

theorem embeddingMatrix_abs_det_fractionalIdeal {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    |(embeddingMatrix (fractionalIdealFullLattice hn I) σ).det| =
      Real.sqrt |(NumberField.discr K : ℝ)| * (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := by
  let b : Basis (Fin n) ℤ (𝓞 K) := (Module.Free.chooseBasis ℤ (𝓞 K)).reindex
    (Fintype.equivFinOfCardEq (by rw [← Module.finrank_eq_card_basis (Module.Free.chooseBasis ℤ (𝓞 K)),RingOfIntegers.rank,hn]))
  rw [embeddingMatrix_det_basisChange _ σ (b.localizationLocalization ℚ ℤ⁰ K),abs_mul]
  have hnrm := FractionalIdeal.abs_det_basis_change b (I : FractionalIdeal (𝓞 K)⁰ K)
    (fractionalIdealFullLattice hn I).basis
  have hnrm' : |((b.localizationLocalization ℚ ℤ⁰ K).det
      (fun i => ((fractionalIdealFullLattice hn I).basis i : K)) : ℝ)| =
        (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := by
    exact_mod_cast hnrm
  rw [hnrm']
  have hdet : |Matrix.det (fun i j => σ j ((b.localizationLocalization ℚ ℤ⁰ K) i))| =
      Real.sqrt |(NumberField.discr K : ℝ)| := by
    simp only [Basis.localizationLocalization_apply]
    conv_rhs => rw [← integralEmbeddingMatrix_det_sq σ hn b,abs_of_nonneg (sq_nonneg _),Real.sqrt_sq_eq_abs]
  rw [hdet,mul_comm]

lemma prod_orderedEmbeddings {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n) (a : K) :
    ∏ i, σ i a = (Algebra.norm ℚ a : ℝ) := by
  apply Complex.ofReal_injective
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ a
  rw [← (orderedComplexEmbeddings σ hn).prod_comp] at h
  change (algebraMap ℚ ℂ) (Algebra.norm ℚ a) = ∏ i, Complex.ofReal (σ i a) at h
  rw [← Complex.ofReal_prod] at h
  change (Algebra.norm ℚ a : ℂ) = _ at h
  simpa only [Complex.ofReal_ratCast] using h.symm

lemma prod_abs_orderedEmbeddings {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n) (a : K) :
    ∏ i, |σ i a| = |(Algebra.norm ℚ a : ℝ)| := by
  rw [← Finset.abs_prod,prod_orderedEmbeddings σ hn]

lemma fractionalIdeal_absNorm_pos {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    0 < (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := by
  exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg I.1)
    (fun h => I.ne_zero (FractionalIdeal.absNorm_eq_zero_iff.mp h.symm))

lemma normalization_rpow_pow {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    (x^(-(1:ℝ)/(n:ℝ)))^n = x⁻¹ := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hx.le]
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [div_mul_cancel₀ _ hn',Real.rpow_neg_one]

lemma normalized_ideal_coordinate_product {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n) (hnpos : 0 < n)
    {q : ℝ} (hq : 0 < q) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : K) :
    (∏ i, |(q*|(embeddingMatrix (fractionalIdealFullLattice hn I) σ).det|)^(-(1:ℝ)/n)*σ i a|) =
      (FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ a *
        (I⁻¹).val) : ℝ)/(q*Real.sqrt |(NumberField.discr K : ℝ)|) := by
  have hD : 0 < Real.sqrt |(NumberField.discr K : ℝ)| := by
    apply Real.sqrt_pos.mpr
    exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  have hI := fractionalIdeal_absNorm_pos I
  rw [embeddingMatrix_abs_det_fractionalIdeal σ hn I]
  simp_rw [abs_mul,Finset.prod_mul_distrib]
  rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,abs_of_pos (Real.rpow_pos_of_pos (mul_pos hq (mul_pos hD hI)) _),
    normalization_rpow_pow hnpos (mul_pos hq (mul_pos hD hI)),prod_abs_orderedEmbeddings σ hn]
  have hinv : FractionalIdeal.absNorm (I⁻¹).val =
      (FractionalIdeal.absNorm I.1)⁻¹ := by
    have h := congrArg (fun J : FractionalIdeal (𝓞 K)⁰ K => FractionalIdeal.absNorm J) (Units.mul_inv I)
    rw [map_mul,map_one] at h
    exact eq_inv_of_mul_eq_one_right h
  rw [map_mul,FractionalIdeal.absNorm_span_singleton,hinv,Rat.cast_mul,Rat.cast_inv,Rat.cast_abs]
  ring

lemma packetUnfoldingCoefficient {n : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (hn : Module.finrank ℚ K = n) (hodd : Odd n) :
    2 / ((NumberField.classNumber K : ℝ) * 2^n * NumberField.Units.regulator K) =
      1 / (Real.sqrt |(NumberField.discr K : ℝ)| * NumberField.dedekindZeta_residue K) := by
  have hd : Real.sqrt |(NumberField.discr K : ℝ)| ≠ 0 :=
    (Real.sqrt_pos.mpr (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K))).ne'
  have hc : (NumberField.classNumber K : ℝ) ≠ 0 := by
    exact_mod_cast (NumberField.classNumber_pos K).ne'
  rw [NumberField.dedekindZeta_residue_def,← NumberField.IsTotallyReal.finrank,
    NumberField.IsTotallyReal.nrComplexPlaces_eq_zero,
    NumberField.Units.torsionOrder_eq_two_of_odd_finrank (hn ▸ hodd),hn]
  simp only [pow_zero,mul_one,Nat.cast_ofNat]
  field_simp

lemma packetUnfoldingCoefficient_ennreal {n : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (hn : Module.finrank ℚ K = n) (hodd : Odd n) :
    ((NumberField.classNumber K : ℝ≥0∞)*2^n)⁻¹ *
        (ENNReal.ofReal (NumberField.Units.regulator K))⁻¹ * 2 =
      (ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|) *
        ENNReal.ofReal (NumberField.dedekindZeta_residue K))⁻¹ := by
  have hc := congrArg ENNReal.ofReal (packetUnfoldingCoefficient hn hodd)
  rw [ENNReal.ofReal_div_of_pos (mul_pos (mul_pos (by exact_mod_cast NumberField.classNumber_pos K) (pow_pos (by norm_num) _)) (NumberField.Units.regulator_pos K)),ENNReal.ofReal_div_of_pos (by
    exact mul_pos (Real.sqrt_pos.mpr (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K)))
      (NumberField.dedekindZeta_residue_pos K))] at hc
  simp only [ENNReal.ofReal_ofNat,ENNReal.ofReal_one,one_div] at hc
  rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (by norm_num),ENNReal.ofReal_ofNat,ENNReal.ofReal_mul (by positivity)] at hc
  rw [← ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inl (by finiteness))] 
  simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hc

 

def signedGlobalLabelEquiv {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    SignedGlobalLabel M I ≃ globalLabels M I × (Fin n → SignTypeˣ) where
  toFun x := (x.lattice,x.signs)
  invFun x := ⟨x.1,x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma allSignedGlobalLabel_card {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) :
    Nat.card (AllSignedGlobalLabel M) =
      NumberField.classNumber K * (Nat.card (globalLabels M 1) * 2^n) := by
  let : Finite (globalLabels M 1) := (globalLabels_finite M hn 1).to_subtype
  let e : AllSignedGlobalLabel M ≃ ClassGroup (𝓞 K) ×
      (globalLabels M 1 × (Fin n → SignTypeˣ)) :=
    (Equiv.sigmaCongrRight (fun c => (signedGlobalLabelEquiv M (classRepresentative K c)).trans
      (Equiv.prodCongr (globalLabelsEquiv M hn (classRepresentative K c) 1) (Equiv.refl _)))).trans
        (Equiv.sigmaEquivProd _ _)
  rw [Nat.card_congr e,Nat.card_prod,Nat.card_prod,Nat.card_fun,Nat.card_fin]
  have hs : Nat.card SignTypeˣ = 2 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_units]
    decide
  rw [hs,Nat.card_eq_fintype_card]
  rfl

lemma sum_signedGlobalLabel {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    [Fintype (SignedGlobalLabel M I)] [Fintype (globalLabels M I)]
    (F : SignedGlobalLabel M I → ℝ≥0∞) :
    (∑ x : SignedGlobalLabel M I, F x) =
      ∑ w : Fin n → SignTypeˣ, ∑ N : globalLabels M I, F ⟨N,w⟩ := by
  let e := (signedGlobalLabelEquiv M I).trans (Equiv.prodComm _ _)
  calc
    _ = ∑ x : (Fin n → SignTypeˣ) × globalLabels M I, F ⟨x.2,x.1⟩ :=
      (e.symm.sum_comp F).symm
    _ = _ := Fintype.sum_prod_type _

 

lemma signedLabel_siegelTransform_average {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    [Fintype (SignedGlobalLabel M I)] [Fintype (globalLabels M I)]
    (u : LogCoordinates d) (f : (Fin (d+1) → ℝ) → ℝ≥0∞) :
    (Nat.card (globalLabels M I) : ℝ≥0∞)⁻¹ *
      ∑ x : SignedGlobalLabel M I, siegelTransform f (orbitMap (signedGlobalLabelPoint M σ hodd I x) u) =
      ∑' a : nonzeroIdealElements I, globalIdealWeight M (relativeElementIdeal I a.1) *
        signedFlowSum f (fun i => ((saturationIndex M : ℝ) *
          |(embeddingMatrix (fractionalIdealFullLattice hn I) σ).det|) ^ (-(1:ℝ)/(d+1:ℕ)) * σ i a.1.1) u := by
  rw [sum_signedGlobalLabel,Finset.mul_sum]
  simp_rw [globalLabel_siegelTransform_average M σ hn hodd]
  rw [← tsum_fintype (L := SummationFilter.unconditional _),ENNReal.tsum_comm]
  apply tsum_congr
  intro a
  rw [tsum_fintype, signedFlowSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  congr 2
  ext i
  ring

lemma signedLabel_siegelTransform_sum {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    [Fintype (SignedGlobalLabel M I)] [Fintype (globalLabels M I)]
    (u : LogCoordinates d) (f : (Fin (d+1) → ℝ) → ℝ≥0∞) :
    (∑ x : SignedGlobalLabel M I, siegelTransform f (orbitMap (signedGlobalLabelPoint M σ hodd I x) u)) =
      (Nat.card (globalLabels M I) : ℝ≥0∞) *
      ∑' a : nonzeroIdealElements I, globalIdealWeight M (relativeElementIdeal I a.1) *
        signedFlowSum f (fun i => ((saturationIndex M : ℝ) *
          |(embeddingMatrix (fractionalIdealFullLattice hn I) σ).det|) ^ (-(1:ℝ)/(d+1:ℕ)) * σ i a.1.1) u := by
  rw [← signedLabel_siegelTransform_average M σ hn hodd I u f]
  exact (ENNReal.mul_inv_cancel_left (by exact_mod_cast (globalLabels_card_pos M hn I).ne') (by finiteness)).symm

 

theorem signedLabel_siegelTransform_lintegral {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    [Fintype (SignedGlobalLabel M I)] [Fintype (globalLabels M I)]
    {t : Set (LogCoordinates d)} (ht : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) t volume)
    (f : (Fin (d+1) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ u in t, ∑ x : SignedGlobalLabel M I,
      siegelTransform f (orbitMap (signedGlobalLabelPoint M σ hodd I x) u)) =
      (Nat.card (globalLabels M I) : ℝ≥0∞) * (2 *
      ∑' J : integralIdealClassFiber I, globalIdealWeight M J.1 *
        productFiberIntegral f ((FractionalIdeal.absNorm J.1.val : ℝ) /
          ((saturationIndex M : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)|))) := by
  let : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable Kˣ := Units.val_injective.countable
  let : Countable (nonzeroIdealElements I) := by
    change Countable {a : Kˣ // (a : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K)}
    infer_instance
  let c := ((saturationIndex M : ℝ) *
    |(embeddingMatrix (fractionalIdealFullLattice hn I) σ).det|) ^ (-(1:ℝ)/(d+1:ℕ))
  have hq : 0 < (saturationIndex M : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (saturationIndex_ne_zero M)
  have hc : c ≠ 0 := (Real.rpow_pos_of_pos (mul_pos hq
    (abs_pos.mpr (embeddingMatrix_det_ne_zero _ σ hn))) _).ne'
  simp_rw [signedLabel_siegelTransform_sum M σ hn hodd I]
  rw [lintegral_const_mul _ (Measurable.tsum (fun a : nonzeroIdealElements I =>
    (measurable_signedFlowSum hf (fun i => c*σ i a.1.1)).const_mul _))]
  rw [lintegral_weighted_idealElements σ (hn ▸ hodd) ht I (globalIdealWeight M) f hf c hc]
  congr 2
  apply tsum_congr
  intro J
  congr 2
  rw [show (∏ i, |c*σ i (idealElementRepresentative I J).1.1|) =
      (FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰
        (idealElementRepresentative I J).1.1 * (I⁻¹).val) : ℝ) /
        ((saturationIndex M : ℝ)*Real.sqrt |(NumberField.discr K : ℝ)|) from
    normalized_ideal_coordinate_product σ hn (Nat.succ_pos _) hq I _]
  have hJ := congrArg (fun J : integralIdealClassFiber I => J.1.val) (idealElementRepresentative_spec I J)
  simp only [relativeElementClassMap,relativeElementIdeal,Units.val_mul,coe_toPrincipalIdeal] at hJ
  rw [hJ]

lemma orderedLogFundamentalDomain_volume {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    {t : Set (LogCoordinates d)} (ht : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) t volume) :
    volume t = ENNReal.ofReal (NumberField.Units.regulator K) := by
  have hr : (volume t).toReal = NumberField.Units.regulator K :=
    (ZLattice.covolume_eq_measure_fundamentalDomain (orderedLogSubgroup σ ⊤) volume ht).symm.trans
      (orderedLogSubgroup_covolume_eq_regulator σ)
  have htop : volume t ≠ ⊤ := by
    intro h
    apply NumberField.Units.regulator_ne_zero K
    simpa only [h,ENNReal.toReal_top] using hr.symm
  rw [← hr, ENNReal.ofReal_toReal htop]

lemma cancel_label_average {a b L R S : ℝ≥0∞} (hL0 : L ≠ 0) (hLt : L ≠ ⊤) :
    (a*(L*b))⁻¹ * (R⁻¹ * (L*(2*S))) = (a*b)⁻¹ * R⁻¹ * 2 * S := by
  rw [show a*(L*b) = (a*b)*L by ring,ENNReal.mul_inv (Or.inr hLt) (Or.inr hL0)]
  calc
    _ = (a*b)⁻¹ * R⁻¹ * 2 * ((L⁻¹*L)*S) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hL0 hLt,one_mul]

 

lemma allSignedLabel_siegelTransform_lintegral {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    [∀ c : ClassGroup (𝓞 K), Fintype (SignedGlobalLabel M (classRepresentative K c))]
    [∀ c : ClassGroup (𝓞 K), Fintype (globalLabels M (classRepresentative K c))]
    {t : Set (LogCoordinates d)} (ht : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) t volume)
    (f : (Fin (d+1) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ u in t, ∑ x : AllSignedGlobalLabel M,
      siegelTransform f (orbitMap (allSignedGlobalLabelPoint M σ hodd x) u)) =
      (Nat.card (globalLabels M 1) : ℝ≥0∞) * (2 *
      ∑' J : integralFractionalIdeals K, globalIdealWeight M J.1 *
        productFiberIntegral f ((FractionalIdeal.absNorm J.1.val : ℝ) /
          ((saturationIndex M : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)|))) := by
  simp only [AllSignedGlobalLabel,Fintype.sum_sigma,allSignedGlobalLabelPoint]
  rw [lintegral_finsetSum Finset.univ (f := fun c u =>
    ∑ x : SignedGlobalLabel M (classRepresentative K c),
      siegelTransform f (orbitMap (signedGlobalLabelPoint M σ hodd (classRepresentative K c) x) u))
    (fun c _ => Finset.measurable_sum _ (fun x _ =>
      (measurable_siegelTransform hf).comp (continuous_orbitMap _).measurable))]
  simp_rw [signedLabel_siegelTransform_lintegral M σ hn hodd _ ht f hf]
  have hcard (c : ClassGroup (𝓞 K)) :
      Nat.card (globalLabels M (classRepresentative K c)) = Nat.card (globalLabels M 1) :=
    Nat.card_congr (globalLabelsEquiv M hn (classRepresentative K c) 1)
  simp_rw [hcard]
  rw [← Finset.mul_sum,← Finset.mul_sum]
  congr 2
  rw [← tsum_fintype (L := SummationFilter.unconditional _)]
  exact tsum_idealClassPartition K (fun J => globalIdealWeight M J *
    productFiberIntegral f ((FractionalIdeal.absNorm J.val : ℝ) /
      ((saturationIndex M : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)|)))

 

theorem packetMeasure_siegel_unfolding_fractional {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (f : (Fin (d+1) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, siegelTransform f x ∂packetMeasure M σ) =
      (ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|) *
        ENNReal.ofReal (NumberField.dedekindZeta_residue K))⁻¹ *
      ∑' J : integralFractionalIdeals K, globalIdealWeight M J.1 *
        productFiberIntegral f ((FractionalIdeal.absNorm J.1.val : ℝ) / packetScale M) := by
  let (c : ClassGroup (𝓞 K)) : Finite (SignedGlobalLabel M (classRepresentative K c)) :=
    signedGlobalLabel_finite M hn _
  let (c : ClassGroup (𝓞 K)) : Fintype (SignedGlobalLabel M (classRepresentative K c)) := Fintype.ofFinite _
  let (c : ClassGroup (𝓞 K)) : Fintype (globalLabels M (classRepresentative K c)) :=
    (globalLabels_finite M hn _).fintype
  let b := Module.Free.chooseBasis ℤ (orderedLogSubgroup σ ⊤)
  let t := ZSpan.fundamentalDomain (Module.Basis.ofZLatticeBasis ℝ (orderedLogSubgroup σ ⊤) b)
  have ht : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) t volume :=
    ZLattice.isAddFundamentalDomain b volume
  rw [packetMeasure_lintegral_signedLogAverage M σ hn hodd ht _ (measurable_siegelTransform hf),
    allSignedLabel_siegelTransform_lintegral M σ hn hodd ht f hf,
    orderedLogFundamentalDomain_volume σ ht,allSignedGlobalLabel_card M hn]
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [cancel_label_average (by exact_mod_cast (globalLabels_card_pos M hn 1).ne') (by finiteness),
    packetUnfoldingCoefficient_ennreal hn hodd]
  rfl

 

def nonzeroIdealWeight {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (J : {J : Ideal (𝓞 K) // J ≠ ⊥}) : ℝ≥0∞ :=
  globalIdealWeight M (Units.mk0 (J.1 : FractionalIdeal (𝓞 K)⁰ K) (by simpa using J.2))

 

theorem packetMeasure_siegel_unfolding {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (f : (Fin (d+1) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, siegelTransform f x ∂packetMeasure M σ) =
      (ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|) *
        ENNReal.ofReal (NumberField.dedekindZeta_residue K))⁻¹ *
      ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥}, nonzeroIdealWeight M J *
        productFiberIntegral f ((Ideal.absNorm J.1 : ℝ) / packetScale M) := by
  rw [packetMeasure_siegel_unfolding_fractional M σ hn hodd f hf]
  congr 1
  rw [← (integralFractionalIdealsEquiv K).tsum_eq]
  apply tsum_congr
  intro J
  change nonzeroIdealWeight M J *
    productFiberIntegral f ((FractionalIdeal.absNorm (J.1 : FractionalIdeal (𝓞 K)⁰ K) : ℝ) / packetScale M) = _
  rw [FractionalIdeal.coeIdeal_absNorm,Rat.cast_natCast]

lemma signValue_abs (w : SignTypeˣ) : |signValue w| = 1 := by
  have hw := w.ne_zero
  cases h : (w : SignType) <;> simp_all [signValue]

 

def coordinateBox {n : ℕ} (w : Fin n → ℝ) (ε : ℝ) : Set (Fin n → ℝ) :=
  {v | ∀ i, |v i-w i| ≤ ε}

def boxIndicator {n : ℕ} (w : Fin n → ℝ) (ε : ℝ) : (Fin n → ℝ) → ℝ≥0∞ :=
  (coordinateBox w ε).indicator (fun _ => 1)

lemma measurableSet_coordinateBox {n : ℕ} (w : Fin n → ℝ) (ε : ℝ) :
    MeasurableSet (coordinateBox w ε) := by
  simp only [coordinateBox, ofPred_forall]
  exact MeasurableSet.iInter (fun i =>
    (isClosed_le (by fun_prop : Continuous (fun v : Fin n → ℝ => |v i-w i|))
      continuous_const).measurableSet)

lemma measurable_boxIndicator {n : ℕ} (w : Fin n → ℝ) (ε : ℝ) :
    Measurable (boxIndicator w ε) :=
  measurable_const.indicator (measurableSet_coordinateBox w ε)

lemma abs_prod_sub_prod_bound {ι : Type*} (s : Finset ι) (v w : ι → ℝ)
    {B ε : ℝ} (hB : 1 ≤ B) (hε : 0 ≤ ε)
    (hv : ∀ i ∈ s, |v i| ≤ B) (hw : ∀ i ∈ s, |w i| ≤ B)
    (hd : ∀ i ∈ s, |v i-w i| ≤ ε) :
    |∏ i ∈ s, v i - ∏ i ∈ s, w i| ≤ (s.card:ℝ)*ε*B^s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hv' : ∀ i ∈ s, |v i| ≤ B := fun i hi => hv i (Finset.mem_insert_of_mem hi)
    have hw' : ∀ i ∈ s, |w i| ≤ B := fun i hi => hw i (Finset.mem_insert_of_mem hi)
    have hd' : ∀ i ∈ s, |v i-w i| ≤ ε := fun i hi => hd i (Finset.mem_insert_of_mem hi)
    have hi := ih hv' hw' hd'
    have hp : |∏ i ∈ s, w i| ≤ B^s.card := by
      rw [Finset.abs_prod]
      exact (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) hw').trans_eq (by simp)
    simp only [Finset.prod_insert ha,Finset.card_insert_of_notMem ha,Nat.cast_add,Nat.cast_one]
    calc
      |v a * ∏ i ∈ s, v i - w a * ∏ i ∈ s, w i| =
          |v a * ((∏ i ∈ s, v i)-(∏ i ∈ s, w i)) + (v a-w a)*(∏ i ∈ s,w i)| := by ring_nf
      _ ≤ |v a| *|((∏ i ∈ s, v i)-(∏ i ∈ s, w i))| + |v a-w a| *|∏ i ∈ s,w i| := by
        simpa only [abs_mul] using abs_add_le (v a * ((∏ i ∈ s,v i)-(∏ i ∈ s,w i)))
          ((v a-w a)*(∏ i ∈ s,w i))
      _ ≤ B*((s.card:ℝ)*ε*B^s.card)+ε*B^s.card := by
        exact add_le_add (mul_le_mul (hv a (Finset.mem_insert_self _ _)) hi
          (abs_nonneg _) (by linarith))
          (mul_le_mul (hd a (Finset.mem_insert_self _ _)) hp (abs_nonneg _) hε)
      _ ≤ ((s.card:ℝ)+1)*ε*B^(s.card+1) := by
        rw [pow_succ]
        nlinarith [mul_le_mul_of_nonneg_right hB (mul_nonneg hε (pow_nonneg (show 0 ≤ B by linarith) s.card))]

lemma log_interval_width_bound {a c ε : ℝ} (hc : 0 < c) (ha : c ≤ a)
    (hε : 0 ≤ ε) (hεc : ε ≤ c/2) :
    Real.log (a+ε)-Real.log (a-ε) ≤ 4*ε/c := by
  have hlo : 0 < a-ε := by linarith
  have hhi : 0 < a+ε := by linarith
  rw [← Real.log_div hhi.ne' hlo.ne']
  have H := Real.log_le_sub_one_of_pos (div_pos hhi hlo)
  apply H.trans
  have he : (a+ε)/(a-ε)-1 = 2*ε/(a-ε) := by field_simp; ring
  rw [he]
  apply (div_le_div_iff₀ hlo hc).mpr
  nlinarith

lemma fiberPoint_abs_prod {d : ℕ} (w : Fin (d+1) → SignTypeˣ) (z : ℝ)
    (u : LogCoordinates d) :
    (∏ i, |(Fin.snoc (fun i => signValue (w i.castSucc)*Real.exp (u i))
      (signValue (w (Fin.last d))*z*Real.exp (-∑ i, u i))) i|) = |z| := by
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last,abs_mul,signValue_abs,one_mul,
    abs_of_pos (Real.exp_pos _)]
  rw [← Real.exp_sum,← mul_assoc, mul_comm (Real.exp (∑ i, u i)) |z|,
    mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]

 

theorem productFiberIntegral_box_le {d : ℕ} (w : Fin (d+1) → ℝ) {c ε : ℝ}
    (hc : 0 < c) (hw : ∀ i, c ≤ |w i|) (hε : 0 ≤ ε) (hεc : ε ≤ c/2) (z : ℝ) :
    productFiberIntegral (boxIndicator w ε) z ≤
      (Fintype.card (Fin (d+1) → SignTypeˣ) : ℝ≥0∞) * ENNReal.ofReal ((4*ε/c)^d) := by
  let a : LogCoordinates d := fun i => Real.log (|w i.castSucc|-ε)
  let b : LogCoordinates d := fun i => Real.log (|w i.castSucc|+ε)
  have H (s : Fin (d+1) → SignTypeˣ) :
      (∫⁻ u : LogCoordinates d, boxIndicator w ε
        (Fin.snoc (fun i => signValue (s i.castSucc)*Real.exp (u i))
          (signValue (s (Fin.last d))*z*Real.exp (-∑ i, u i)))) ≤ ENNReal.ofReal ((4*ε/c)^d) := by
    calc
      _ ≤ ∫⁻ u : LogCoordinates d, (Set.Icc a b).indicator (fun _ => (1:ℝ≥0∞)) u := by
        apply lintegral_mono
        intro u
        by_cases hu : Fin.snoc (fun i => signValue (s i.castSucc)*Real.exp (u i))
            (signValue (s (Fin.last d))*z*Real.exp (-∑ i, u i)) ∈ coordinateBox w ε
        · have hab : u ∈ Set.Icc a b := by
            constructor <;> intro i
            all_goals
              have hv := hu i.castSucc
              simp only [Fin.snoc_castSucc] at hv
              have he : |signValue (s i.castSucc)*Real.exp (u i)| = Real.exp (u i) := by
                rw [abs_mul,signValue_abs,one_mul,abs_of_pos (Real.exp_pos _)]
              have hlo : |w i.castSucc|-ε ≤ Real.exp (u i) := by
                have := abs_sub_abs_le_abs_sub (w i.castSucc) (signValue (s i.castSucc)*Real.exp (u i))
                rw [abs_sub_comm,he] at this
                linarith
              have hhi : Real.exp (u i) ≤ |w i.castSucc|+ε := by
                have := abs_sub_abs_le_abs_sub (signValue (s i.castSucc)*Real.exp (u i)) (w i.castSucc)
                rw [he] at this
                linarith
            · exact (Real.log_le_iff_le_exp (by have := hw i.castSucc; linarith)).mpr hlo
            · exact (Real.le_log_iff_exp_le (by have := hw i.castSucc; linarith)).mpr hhi
          simp only [boxIndicator,Set.indicator_of_mem hu,Set.indicator_of_mem hab,le_refl]
        · simp only [boxIndicator,Set.indicator_of_notMem hu]
          exact bot_le
      _ = volume (Set.Icc a b) := by rw [lintegral_indicator measurableSet_Icc]; simp
      _ = ∏ i : Fin d, ENNReal.ofReal (b i-a i) := Real.volume_Icc_pi
      _ ≤ ∏ _i : Fin d, ENNReal.ofReal (4*ε/c) := by
        apply Finset.prod_le_prod (fun i _ => ENNReal.ofReal_le_ofReal ?_)
        exact log_interval_width_bound hc (hw i.castSucc) hε hεc
      _ = _ := by simp [← ENNReal.ofReal_pow (by positivity : 0 ≤ 4*ε/c)]
  unfold productFiberIntegral
  exact (Finset.sum_le_sum (fun s _ => H s)).trans_eq (by simp [nsmul_eq_mul])

lemma coordinateBox_product_bound {n : ℕ} {w v : Fin n → ℝ} {b ε : ℝ}
    (hb : 0 ≤ b) (hw : ∀ i, |w i| ≤ b) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hv : v ∈ coordinateBox w ε) :
    |(∏ i, |v i|) - (∏ i, |w i|)| ≤ (n:ℝ)*(b+1)^n*ε := by
  have hd (i : Fin n) : abs (abs (v i) - abs (w i)) ≤ ε := by
    apply abs_le.mpr
    constructor
    · have H := abs_sub_abs_le_abs_sub (w i) (v i)
      rw [abs_sub_comm] at H
      have := hv i
      linarith
    · exact (abs_sub_abs_le_abs_sub (v i) (w i)).trans (hv i)
  have hv' (i : Fin n) : |v i| ≤ b+1 := by
    have H := abs_sub_abs_le_abs_sub (v i) (w i)
    have := hv i
    have := hw i
    linarith
  have H := abs_prod_sub_prod_bound Finset.univ (fun i => |v i|) (fun i => |w i|)
    (show 1 ≤ b+1 by linarith) hε
    (fun i _ => by simpa only [abs_abs] using hv' i)
    (fun i _ => by simpa only [abs_abs] using (hw i).trans (by linarith : b ≤ b+1))
    (fun i _ => hd i)
  simpa only [Finset.card_univ,Fintype.card_fin,mul_right_comm] using H

 

theorem productFiberIntegral_box_supported {d : ℕ} (w : Fin (d+1) → ℝ)
    {c b ε z : ℝ} (hc : 0 < c) (hb : 0 ≤ b)
    (hwlo : ∀ i, c ≤ |w i|) (hwhi : ∀ i, |w i| ≤ b)
    (hε : 0 ≤ ε) (hεc : ε ≤ c/2) (hε1 : ε ≤ 1) (hz : 0 < z) :
    productFiberIntegral (boxIndicator w ε) z ≤
      if |z-(∏ i, |w i|)| ≤ ((d+1:ℕ):ℝ)*(b+1)^(d+1)*ε then
        (Fintype.card (Fin (d+1) → SignTypeˣ) : ℝ≥0∞) * ENNReal.ofReal ((4*ε/c)^d)
      else 0 := by
  classical
  split_ifs with ht
  · exact productFiberIntegral_box_le w hc hwlo hε hεc z
  · have Hzero (s : Fin (d+1) → SignTypeˣ) (u : LogCoordinates d) :
        boxIndicator w ε
          (Fin.snoc (fun i => signValue (s i.castSucc)*Real.exp (u i))
            (signValue (s (Fin.last d))*z*Real.exp (-∑ i, u i))) = 0 := by
      apply Set.indicator_of_notMem
      intro hu
      have H := coordinateBox_product_bound hb hwhi hε hε1 hu
      rw [fiberPoint_abs_prod,abs_of_pos hz] at H
      exact ht H
    simp only [productFiberIntegral,Hzero,lintegral_zero,Finset.sum_const_zero,le_refl]

end PrimeDegreePackets
end
end

end OAI
