import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.MeanR
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.CardFourLeEnergy

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

namespace OrdinaryCorrelations.SourceRoughCircleIntegration
open Classical Finset
open SourceRoughFourier SourceRoughCountIntegration
open scoped BigOperators

noncomputable def roughPolynomial (Z : Finset ℕ) (h : ℕ) (θ : AddCircle (1:ℝ)) : ℂ :=
  SourceCircleFourier.poly Z (fun z => (z:ℂ)⁻¹) (fun z => (h*z:ℕ)) θ

lemma roughPolynomial_eq (Z : Finset ℕ) (h : ℕ) (θ : ℝ) :
    roughPolynomial Z h θ = ∑ z ∈ Z, (z:ℂ)⁻¹ *
      Complex.exp (2*Real.pi*Complex.I*(h*z:ℕ)*θ) := by
  simp [roughPolynomial,SourceCircleFourier.poly]

lemma roughPolynomial_norm (Z : Finset ℕ) (h : ℕ) (θ : AddCircle (1:ℝ)) :
    ‖roughPolynomial Z h θ‖ ≤ ∑ z ∈ Z, (z:ℝ)⁻¹ := by
  simpa only [roughPolynomial,norm_inv,Complex.norm_natCast] using
    SourceCircleFourier.poly_norm_le Z (fun z => (z:ℂ)⁻¹) (fun z => (h*z:ℕ)) θ

lemma fourth_le_energy (Z : Finset ℕ) (h D : ℕ) (hh : 0 < h) (hD : 0 < D)
    (hZ : ∀ z ∈ Z, D ≤ z) :
    (∫ θ in (0:ℝ)..1, ‖roughPolynomial Z h θ‖^4) ≤
      (natAdditiveEnergy Z:ℝ)*(D:ℝ)⁻¹^4 := by
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
    _ ≤ ∑ _q ∈ natEnergyQuadruples Z, (D:ℝ)⁻¹^4 := by
      apply sum_le_sum
      intro q hq
      obtain ⟨hq,_⟩ := mem_filter.mp hq
      obtain ⟨h12,h34⟩ := mem_product.mp hq
      obtain ⟨h1,h2⟩ := mem_product.mp h12
      obtain ⟨h3,h4⟩ := mem_product.mp h34
      have hw (z : ℕ) (hz : z ∈ Z) : (z:ℝ)⁻¹ ≤ (D:ℝ)⁻¹ :=
        inv_anti₀ (by exact_mod_cast hD) (by exact_mod_cast hZ z hz)
      calc
        _ ≤ ((D:ℝ)⁻¹*(D:ℝ)⁻¹)*((D:ℝ)⁻¹*(D:ℝ)⁻¹) := by
          exact mul_le_mul
            (mul_le_mul (hw _ h1) (hw _ h2) (by positivity) (by positivity))
            (mul_le_mul (hw _ h3) (hw _ h4) (by positivity) (by positivity))
            (by positivity) (by positivity)
        _ = _ := by ring
    _ = _ := by simp [natAdditiveEnergy,nsmul_eq_mul]

theorem eventual_rough_fourier : ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in Filter.atTop,
    ∀ D : ℕ, (1/2:ℝ)*Real.exp (L^(199/200:ℝ)) ≤ D →
    ∀ h : ℕ, 0 < h → ∀ Z : Finset ℕ,
      (∀ z ∈ Z, D ≤ z ∧ z < 2*D ∧ IsRough (Real.exp (L^(99/100:ℝ))) z) →
      (∀ θ : AddCircle (1:ℝ), ‖roughPolynomial Z h θ‖ ≤ C*L^(-99/100:ℝ)) ∧
      (∫ θ in (0:ℝ)..1, ‖roughPolynomial Z h θ‖^4) ≤ C*(D:ℝ)⁻¹*L^(-99/25:ℝ) := by
  obtain ⟨C1,hC1,h1⟩ := eventual_rough_mass
  obtain ⟨C4,hC4,h4⟩ := eventual_roughTriples
  refine ⟨max C1 C4,lt_of_lt_of_le hC1 (le_max_left _ _),?_⟩
  filter_upwards [h1,h4,Filter.eventually_ge_atTop (1:ℝ)] with L hL1 hL4 hLpos
  intro D hD h hh Z hZ
  have hDp : 0 < D := by
    have hp : 0 < (1/2:ℝ)*Real.exp (L^(199/200:ℝ)) := by positivity
    exact_mod_cast hp.trans_le hD
  have he : (natAdditiveEnergy Z:ℝ) ≤ C4*(D:ℝ)^3*L^(-99/25:ℝ) := by
    have hbound : (natAdditiveEnergy Z:ℝ) ≤ (roughTriples D (Real.exp (L^(99/100:ℝ)))).card := by
      exact_mod_cast energy_le_roughTriples Z D _ hZ
    exact hbound.trans (hL4 D hD)
  constructor
  · intro θ
    calc
      _ ≤ ∑ z ∈ Z, (z:ℝ)⁻¹ := roughPolynomial_norm Z h θ
      _ ≤ C1*L^(-99/100:ℝ) := hL1 D hD Z hZ
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · calc
      _ ≤ (natAdditiveEnergy Z:ℝ)*(D:ℝ)⁻¹^4 :=
        fourth_le_energy Z h D hh hDp (fun z hz => (hZ z hz).1)
      _ ≤ (C4*(D:ℝ)^3*L^(-99/25:ℝ))*(D:ℝ)⁻¹^4 :=
        mul_le_mul_of_nonneg_right he (by positivity)
      _ = C4*(D:ℝ)⁻¹*L^(-99/25:ℝ) := by
        have hDz : (D:ℝ) ≠ 0 := by positivity
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) (by positivity)

end OrdinaryCorrelations.SourceRoughCircleIntegration

end

end OAI
