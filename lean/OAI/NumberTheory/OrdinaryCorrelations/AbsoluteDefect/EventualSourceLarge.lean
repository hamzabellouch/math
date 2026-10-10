import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OneBounded
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.EventualRoughBox
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.CardFourLeIntervalEnergy

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory

namespace OrdinaryRoughEnergy
open OrdinaryCorrelations SourceRoughFourier SourceRoughRealScale SourceRoughCountIntegration SourceBoxSieve SourcePrimeBoxSieve Finset Filter
lemma eventual_source_D_large : ∀ᶠ L : ℝ in Filter.atTop,
    2 ≤ (1/2:ℝ)*Real.exp (L^(9999/10000:ℝ)) := by
  filter_upwards [Filter.eventually_ge_atTop (16:ℝ)] with L hL
  have hr : (4:ℝ) ≤ L^(9999/10000:ℝ) := by
    calc
      4 = (16:ℝ)^(1/2:ℝ) := by rw [← Real.sqrt_eq_rpow]; norm_num
      _ ≤ L^(1/2:ℝ) := Real.rpow_le_rpow (by norm_num) hL (by norm_num)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have := Real.add_one_le_exp (L^(9999/10000:ℝ))
  linarith

theorem eventual_real_energy : ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in Filter.atTop,
    ∀ D : ℝ, (1/2:ℝ)*Real.exp (L^(9999/10000:ℝ)) ≤ D →
    ∀ Z : Finset ℕ,
      (∀ z ∈ Z, D ≤ z ∧ z < 2*D ∧ IsRough (Real.exp (L^(199979/200000:ℝ))) z) →
      (natAdditiveEnergy Z:ℝ) ≤ C*D^3*L^(-199979/50000:ℝ) := by
  obtain ⟨C,hC,h⟩ := SourceTailoredBoxSieve.eventual_rough_box
  refine ⟨8*C,by positivity,?_⟩
  filter_upwards [h,eventual_source_D_large,Filter.eventually_ge_atTop (1:ℝ)] with L hL hbig hL1
  intro D hD Z hZ
  have hD2 : 2 ≤ D := hbig.trans hD
  obtain ⟨hDN,hND,hgeom⟩ := floor_geometry D hD2
  let a := ⌊D⌋₊
  let N := 2*a
  have hNp : 0 < N := by
    have : (0:ℝ) < N := (by linarith : (0:ℝ) < D).trans_le hDN
    exact_mod_cast this
  have hNz : (N:ℝ) ≠ 0 := by positivity
  have he : (natAdditiveEnergy Z:ℝ) ≤ (goodBox ⌊Real.exp (L^(199979/200000:ℝ))⌋₊ a N).card := by
    exact_mod_cast energy_le_goodBox Z a N _ (Real.exp_pos _).le
      (fun z hz => ⟨(hgeom z (hZ z hz).1 (hZ z hz).2.1).1,
        (hgeom z (hZ z hz).1 (hZ z hz).2.1).2,(hZ z hz).2.2⟩)
  have hden := hL a N (hD.trans hDN)
  calc
    _ ≤ ((goodBox ⌊Real.exp (L^(199979/200000:ℝ))⌋₊ a N).card:ℝ) := he
    _ = (N:ℝ)^3*density (fun p : Primes ⌊Real.exp (L^(199979/200000:ℝ))⌋₊ => p.val) a N := by
      rw [density_eq_card]
      field_simp
    _ ≤ (N:ℝ)^3*(C*L^(-199979/50000:ℝ)) := mul_le_mul_of_nonneg_left hden (by positivity)
    _ ≤ (2*D)^3*(C*L^(-199979/50000:ℝ)) := by gcongr
    _ = _ := by ring

theorem eventual_real_count : ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in Filter.atTop,
    ∀ D : ℝ, (1/2:ℝ)*Real.exp (L^(9999/10000:ℝ)) ≤ D →
    ∀ Z : Finset ℕ,
      (∀ z ∈ Z, D ≤ z ∧ z < 2*D ∧ IsRough (Real.exp (L^(199979/200000:ℝ))) z) →
      (Z.card:ℝ) ≤ C*D*L^(-199979/200000:ℝ) := by
  obtain ⟨C,hC,h⟩ := eventual_real_energy
  refine ⟨4*C+1,by positivity,?_⟩
  filter_upwards [h,eventual_source_D_large,Filter.eventually_ge_atTop (1:ℝ)] with L hL hbig hL1
  intro D hD Z hZ
  have hD2 : 2 ≤ D := hbig.trans hD
  obtain ⟨hDN,hND,hgeom⟩ := floor_geometry D hD2
  let a := ⌊D⌋₊
  let N := 2*a
  have hc : (Z.card:ℝ)^4 ≤ 2*(N:ℝ)*(natAdditiveEnergy Z:ℝ) := by
    exact_mod_cast card_four_le_interval_energy Z a N
      (fun z hz => hgeom z (hZ z hz).1 (hZ z hz).2.1)
  have he : (Z.card:ℝ)^4 ≤ 4*D*(C*D^3*L^(-199979/50000:ℝ)) := by
    calc
      _ ≤ 2*(N:ℝ)*(natAdditiveEnergy Z:ℝ) := hc
      _ ≤ 2*(2*D)*(C*D^3*L^(-199979/50000:ℝ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hND (by norm_num))
          (hL D hD Z hZ) (by positivity) (by positivity)
      _ = _ := by ring
  have hex : (L^(-199979/200000:ℝ))^4 = L^(-199979/50000:ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith : 0 ≤ L)]
    norm_num
  apply le_of_pow_le_pow_left₀ (by norm_num : (4:ℕ) ≠ 0) (by positivity)
  calc
    (Z.card:ℝ)^4 ≤ 4*D*(C*D^3*L^(-199979/50000:ℝ)) := he
    _ = (4*C)*D^4*(L^(-199979/200000:ℝ))^4 := by rw [hex]; ring
    _ ≤ (4*C+1)^4*D^4*(L^(-199979/200000:ℝ))^4 := by
      gcongr
      exact (by linarith : 4*C ≤ 4*C+1).trans (le_self_pow₀ (by linarith) (by norm_num : (4:ℕ) ≠ 0))
    _ = _ := by ring

theorem eventual_real_mass : ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in Filter.atTop,
    ∀ D : ℝ, (1/2:ℝ)*Real.exp (L^(9999/10000:ℝ)) ≤ D →
    ∀ Z : Finset ℕ,
      (∀ z ∈ Z, D ≤ z ∧ z < 2*D ∧ IsRough (Real.exp (L^(199979/200000:ℝ))) z) →
      (∑ z ∈ Z, (z:ℝ)⁻¹) ≤ C*L^(-199979/200000:ℝ) := by
  obtain ⟨C,hC,h⟩ := eventual_real_count
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventual_source_D_large] with L hL hbig
  intro D hD Z hZ
  have hDp : 0 < D := by linarith [hbig.trans hD]
  calc
    _ ≤ ∑ _z ∈ Z, D⁻¹ := sum_le_sum (fun z hz => inv_anti₀ hDp (hZ z hz).1)
    _ = (Z.card:ℝ)/D := by simp [div_eq_mul_inv]
    _ ≤ (C*D*L^(-199979/200000:ℝ))/D := div_le_div_of_nonneg_right (hL D hD Z hZ) hDp.le
    _ = _ := by field_simp

end OrdinaryRoughEnergy

end

end OAI
