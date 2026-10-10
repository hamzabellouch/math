import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.GoodBox

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

namespace OrdinaryCorrelations.SourceRoughCountIntegration
open Classical Finset
open scoped Pointwise
open SourceRoughFourier

lemma card_four_le_energy (Z : Finset ℕ) (D : ℕ)
    (hZ : ∀ z ∈ Z, D ≤ z ∧ z < 2*D) :
    Z.card^4 ≤ 2*D*natAdditiveEnergy Z := by
  have hc : (Z+Z).card ≤ 2*D := by
    have hs : Z+Z ⊆ Ico (2*D) (4*D) := by
      intro n hn
      obtain ⟨x,hx,y,hy,rfl⟩ := mem_add.mp hn
      have := hZ x hx
      have := hZ y hy
      apply Finset.mem_Ico.mpr
      omega
    have := Finset.card_le_card hs
    simp only [Nat.card_Ico] at this
    omega
  have he : Z.card^2*Z.card^2 ≤ (Z+Z).card*natAdditiveEnergy Z := by
    simpa only [Finset.addEnergy_eq_card_filter,natAdditiveEnergy,natEnergyQuadruples] using
      Finset.le_card_add_mul_addEnergy Z Z
  calc
    _ = Z.card^2*Z.card^2 := by ring
    _ ≤ _ := he
    _ ≤ _ := Nat.mul_le_mul_right _ hc

theorem eventual_roughIntegers : ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in Filter.atTop,
    ∀ D : ℕ, (1/2:ℝ)*Real.exp (L^(199/200:ℝ)) ≤ D →
      ((roughIntegers D (Real.exp (L^(99/100:ℝ)))).card:ℝ) ≤
        C*(D:ℝ)*L^(-99/100:ℝ) := by
  obtain ⟨C,hC,h⟩ := eventual_roughTriples
  refine ⟨2*C+1,by positivity,?_⟩
  filter_upwards [h,Filter.eventually_ge_atTop (1:ℝ)] with L hL hL1
  intro D hD
  let Z := roughIntegers D (Real.exp (L^(99/100:ℝ)))
  have hZ (z : ℕ) (hz : z ∈ Z) : D ≤ z ∧ z < 2*D ∧ IsRough (Real.exp (L^(99/100:ℝ))) z := by
    exact ⟨(mem_Ico.mp (mem_filter.mp hz).1).1,
      (mem_Ico.mp (mem_filter.mp hz).1).2,(mem_filter.mp hz).2⟩
  have he : (Z.card:ℝ)^4 ≤ 2*(D:ℝ)*natAdditiveEnergy Z := by
    exact_mod_cast card_four_le_energy Z D (fun z hz => ⟨(hZ z hz).1,(hZ z hz).2.1⟩)
  have he' : (natAdditiveEnergy Z:ℝ) ≤ C*(D:ℝ)^3*L^(-99/25:ℝ) := by
    have hbound : (natAdditiveEnergy Z:ℝ) ≤ (roughTriples D (Real.exp (L^(99/100:ℝ)))).card := by
      exact_mod_cast energy_le_roughTriples Z D _ hZ
    exact hbound.trans (hL D hD)
  have hex : (L^(-99/100:ℝ))^4 = L^(-99/25:ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith : 0 ≤ L)]
    norm_num
  apply le_of_pow_le_pow_left₀ (by norm_num : (4:ℕ) ≠ 0) (by positivity)
  calc
    (Z.card:ℝ)^4 ≤ 2*(D:ℝ)*(C*(D:ℝ)^3*L^(-99/25:ℝ)) :=
      he.trans (mul_le_mul_of_nonneg_left he' (by positivity))
    _ = (2*C)*(D:ℝ)^4*(L^(-99/100:ℝ))^4 := by rw [hex]; ring
    _ ≤ (2*C+1)^4*(D:ℝ)^4*(L^(-99/100:ℝ))^4 := by
      gcongr
      exact (by linarith : 2*C ≤ 2*C+1).trans (le_self_pow₀ (by linarith) (by norm_num : (4:ℕ) ≠ 0))
    _ = _ := by ring

theorem eventual_rough_mass : ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in Filter.atTop,
    ∀ D : ℕ, (1/2:ℝ)*Real.exp (L^(199/200:ℝ)) ≤ D →
    ∀ Z : Finset ℕ,
      (∀ z ∈ Z, D ≤ z ∧ z < 2*D ∧ IsRough (Real.exp (L^(99/100:ℝ))) z) →
      (∑ z ∈ Z, (z:ℝ)⁻¹) ≤ C*L^(-99/100:ℝ) := by
  obtain ⟨C,hC,h⟩ := eventual_roughIntegers
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with L hL
  intro D hD Z hZ
  have hDp : 0 < D := by
    have hp : 0 < (1/2:ℝ)*Real.exp (L^(199/200:ℝ)) := by positivity
    exact_mod_cast hp.trans_le hD
  calc
    _ ≤ (roughIntegers D (Real.exp (L^(99/100:ℝ)))).card / (D:ℝ) :=
      reciprocal_mass_le_rough_count Z D _ hDp hZ
    _ ≤ (C*(D:ℝ)*L^(-99/100:ℝ)) / D :=
      div_le_div_of_nonneg_right (hL D hD) (by positivity)
    _ = _ := by
      have hDz : (D:ℝ) ≠ 0 := by positivity
      field_simp

theorem eventual_rough_cyclic_fourth : ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in Filter.atTop,
    ∀ D : ℕ, (1/2:ℝ)*Real.exp (L^(199/200:ℝ)) ≤ D →
    ∀ (h N : ℕ) [NeZero N], 0 < h → 4*h*D ≤ N →
    ∀ Z : Finset ℕ,
      (∀ z ∈ Z, D ≤ z ∧ z < 2*D ∧ IsRough (Real.exp (L^(99/100:ℝ))) z) →
      meanR (fun k : ZMod N =>
        ‖poly Z (fun z => (z:ℂ)⁻¹) (fun z => ((h*z:ℕ):ZMod N)) k‖^4) ≤
          C*(D:ℝ)⁻¹*L^(-99/25:ℝ) := by
  obtain ⟨C,hC,h⟩ := eventual_roughTriples
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with L hL
  intro D hD h N inst hh hN Z hZ
  have hDp : 0 < D := by
    have hp : 0 < (1/2:ℝ)*Real.exp (L^(199/200:ℝ)) := by positivity
    exact_mod_cast hp.trans_le hD
  have he : (natAdditiveEnergy Z:ℝ) ≤ C*(D:ℝ)^3*L^(-99/25:ℝ) := by
    have hbound : (natAdditiveEnergy Z:ℝ) ≤ (roughTriples D (Real.exp (L^(99/100:ℝ)))).card := by
      exact_mod_cast energy_le_roughTriples Z D _ hZ
    exact hbound.trans (hL D hD)
  calc
    _ ≤ (natAdditiveEnergy Z:ℝ)*(D:ℝ)⁻¹^4 :=
      reciprocal_fourth_moment_le Z h D hh hDp (fun z hz => ⟨(hZ z hz).1,(hZ z hz).2.1⟩) hN
    _ ≤ (C*(D:ℝ)^3*L^(-99/25:ℝ))*(D:ℝ)⁻¹^4 :=
      mul_le_mul_of_nonneg_right he (by positivity)
    _ = _ := by
      have hDz : (D:ℝ) ≠ 0 := by positivity
      field_simp

end OrdinaryCorrelations.SourceRoughCountIntegration

end

end OAI
