import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.RoughPolynomial
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

namespace OrdinaryCorrelations.SourceRoughFourierComplete
open Classical Finset
open SourceRoughFourier SourceRoughCircleIntegration SourceRoughRealScale

lemma fourth_le_real_energy (Z : Finset ℕ) (h : ℕ) (D : ℝ) (hh : 0 < h) (hD : 0 < D)
    (hZ : ∀ z ∈ Z, D ≤ (z:ℝ)) :
    (∫ θ in (0:ℝ)..1, ‖roughPolynomial Z h θ‖^4) ≤
      (natAdditiveEnergy Z:ℝ)*D⁻¹^4 := by
  rw [← SourceCircleFourier.meanR_eq_interval (fun θ => ‖roughPolynomial Z h θ‖^4)]
  unfold roughPolynomial
  have heq (i j u v : ℕ) :
      ((h*i:ℕ):ℤ)+((h*j:ℕ):ℤ) = ((h*u:ℕ):ℤ)+((h*v:ℕ):ℤ) ↔ i+j=u+v := by
    simp only [← Nat.cast_add,← Nat.mul_add,Nat.cast_inj]
    exact Nat.mul_left_cancel_iff hh
  have hf := SourceCircleFourier.fourth_moment_real Z (fun z => (z:ℝ)⁻¹)
    (fun z => ((h*z:ℕ):ℤ))
  simp only [Complex.ofReal_inv,Complex.ofReal_natCast,heq] at hf
  rw [hf]
  have hre : (∑ i ∈ Z, ∑ j ∈ Z, ∑ u ∈ Z, ∑ v ∈ Z,
      if i+j=u+v then ((i:ℝ)⁻¹*(j:ℝ)⁻¹)*((u:ℝ)⁻¹*(v:ℝ)⁻¹) else 0) =
      ∑ q ∈ natEnergyQuadruples Z,
        ((q.1.1:ℝ)⁻¹*(q.1.2:ℝ)⁻¹)*((q.2.1:ℝ)⁻¹*(q.2.2:ℝ)⁻¹) := by
    simp only [natEnergyQuadruples,sum_filter,sum_product]
  rw [hre]
  calc
    _ ≤ ∑ _q ∈ natEnergyQuadruples Z, D⁻¹^4 := by
      apply sum_le_sum
      intro q hq
      obtain ⟨hq,_⟩ := mem_filter.mp hq
      obtain ⟨h12,h34⟩ := mem_product.mp hq
      obtain ⟨h1,h2⟩ := mem_product.mp h12
      obtain ⟨h3,h4⟩ := mem_product.mp h34
      have hw (z : ℕ) (hz : z ∈ Z) : (z:ℝ)⁻¹ ≤ D⁻¹ :=
        inv_anti₀ (by exact_mod_cast hD) (by exact_mod_cast hZ z hz)
      calc
        _ ≤ (D⁻¹*D⁻¹)*(D⁻¹*D⁻¹) := by
          exact mul_le_mul
            (mul_le_mul (hw _ h1) (hw _ h2) (by positivity) (by positivity))
            (mul_le_mul (hw _ h3) (hw _ h4) (by positivity) (by positivity))
            (by positivity) (by positivity)
        _ = _ := by ring
    _ = _ := by simp [natAdditiveEnergy,nsmul_eq_mul]

theorem eventual_real_count : ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in Filter.atTop,
    ∀ D : ℝ, (1/2:ℝ)*Real.exp (L^(199/200:ℝ)) ≤ D →
    ∀ Z : Finset ℕ,
      (∀ z ∈ Z, D ≤ z ∧ z < 2*D ∧ IsRough (Real.exp (L^(99/100:ℝ))) z) →
      (Z.card:ℝ) ≤ C*D*L^(-99/100:ℝ) := by
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
  have he : (Z.card:ℝ)^4 ≤ 4*D*(C*D^3*L^(-99/25:ℝ)) := by
    calc
      _ ≤ 2*(N:ℝ)*(natAdditiveEnergy Z:ℝ) := hc
      _ ≤ 2*(2*D)*(C*D^3*L^(-99/25:ℝ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hND (by norm_num))
          (hL D hD Z hZ) (by positivity) (by positivity)
      _ = _ := by ring
  have hex : (L^(-99/100:ℝ))^4 = L^(-99/25:ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith : 0 ≤ L)]
    norm_num
  apply le_of_pow_le_pow_left₀ (by norm_num : (4:ℕ) ≠ 0) (by positivity)
  calc
    (Z.card:ℝ)^4 ≤ 4*D*(C*D^3*L^(-99/25:ℝ)) := he
    _ = (4*C)*D^4*(L^(-99/100:ℝ))^4 := by rw [hex]; ring
    _ ≤ (4*C+1)^4*D^4*(L^(-99/100:ℝ))^4 := by
      gcongr
      exact (by linarith : 4*C ≤ 4*C+1).trans (le_self_pow₀ (by linarith) (by norm_num : (4:ℕ) ≠ 0))
    _ = _ := by ring

theorem eventual_real_mass : ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in Filter.atTop,
    ∀ D : ℝ, (1/2:ℝ)*Real.exp (L^(199/200:ℝ)) ≤ D →
    ∀ Z : Finset ℕ,
      (∀ z ∈ Z, D ≤ z ∧ z < 2*D ∧ IsRough (Real.exp (L^(99/100:ℝ))) z) →
      (∑ z ∈ Z, (z:ℝ)⁻¹) ≤ C*L^(-99/100:ℝ) := by
  obtain ⟨C,hC,h⟩ := eventual_real_count
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventual_source_D_large] with L hL hbig
  intro D hD Z hZ
  have hDp : 0 < D := by linarith [hbig.trans hD]
  calc
    _ ≤ ∑ _z ∈ Z, D⁻¹ := sum_le_sum (fun z hz => inv_anti₀ hDp (hZ z hz).1)
    _ = (Z.card:ℝ)/D := by simp [div_eq_mul_inv]
    _ ≤ (C*D*L^(-99/100:ℝ))/D := div_le_div_of_nonneg_right (hL D hD Z hZ) hDp.le
    _ = _ := by field_simp

theorem source_rough_fourier : ∃ C : ℝ, 0 < C ∧ ∃ L₀ : ℝ,
    ∀ L : ℝ, L₀ ≤ L → ∀ (h : ℕ), 0 < h → ∀ D : ℝ,
    (1/2:ℝ)*Real.exp (L^(199/200:ℝ)) ≤ D → D ≤ Real.exp (2*L) →
    ∀ Z : Finset ℕ,
      (∀ z ∈ Z, D ≤ z ∧ z < 2*D ∧ IsRough (Real.exp (L^(99/100:ℝ))) z) →
      (∀ θ : AddCircle (1:ℝ), ‖roughPolynomial Z h θ‖ ≤ C*L^(-99/100:ℝ)) ∧
      (∫ θ in (0:ℝ)..1, ‖roughPolynomial Z h θ‖^4) ≤ C*D⁻¹*L^(-99/25:ℝ) := by
  obtain ⟨C1,hC1,h1⟩ := eventual_real_mass
  obtain ⟨C4,hC4,h4⟩ := eventual_real_energy
  have hfinal : ∀ᶠ L : ℝ in Filter.atTop,
      ∀ (h : ℕ), 0 < h → ∀ D : ℝ,
      (1/2:ℝ)*Real.exp (L^(199/200:ℝ)) ≤ D → D ≤ Real.exp (2*L) →
      ∀ Z : Finset ℕ,
        (∀ z ∈ Z, D ≤ z ∧ z < 2*D ∧ IsRough (Real.exp (L^(99/100:ℝ))) z) →
        (∀ θ : AddCircle (1:ℝ), ‖roughPolynomial Z h θ‖ ≤ (max C1 C4)*L^(-99/100:ℝ)) ∧
        (∫ θ in (0:ℝ)..1, ‖roughPolynomial Z h θ‖^4) ≤ (max C1 C4)*D⁻¹*L^(-99/25:ℝ) := by
    filter_upwards [h1,h4,eventual_source_D_large,Filter.eventually_ge_atTop (1:ℝ)] with L hL1 hL4 hbig hLpos
    intro h hh D hD _hupper Z hZ
    have hDp : 0 < D := by linarith [hbig.trans hD]
    constructor
    · intro θ
      calc
        _ ≤ ∑ z ∈ Z, (z:ℝ)⁻¹ := roughPolynomial_norm Z h θ
        _ ≤ C1*L^(-99/100:ℝ) := hL1 D hD Z hZ
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · calc
        _ ≤ (natAdditiveEnergy Z:ℝ)*D⁻¹^4 :=
          fourth_le_real_energy Z h D hh hDp (fun z hz => (hZ z hz).1)
        _ ≤ (C4*D^3*L^(-99/25:ℝ))*D⁻¹^4 :=
          mul_le_mul_of_nonneg_right (hL4 D hD Z hZ) (by positivity)
        _ = C4*D⁻¹*L^(-99/25:ℝ) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) (by positivity)
  obtain ⟨L₀,hL₀⟩ := Filter.eventually_atTop.mp hfinal
  exact ⟨max C1 C4,lt_of_lt_of_le hC1 (le_max_left _ _),L₀,hL₀⟩

end OrdinaryCorrelations.SourceRoughFourierComplete

end

end OAI
