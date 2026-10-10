import OAI.NumberTheory.CubicMoment.Angular.AngularStructuredFrequencyPolynomial
import OAI.NumberTheory.CubicMoment.Estimates.DilatedNoncubeMass
import OAI.NumberTheory.CubicMoment.Estimates.LogarithmicNoncube
import OAI.NumberTheory.CubicMoment.Angular.AngularFullPrimeConvolution

namespace OAI

/-! Nonexceptional frequency mass for the literal untruncated prime
convolution, at the same length scale as the exceptional moment bounds. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_full_logarithmic_noncube (hHuxley : HuxleyAdditiveLargeSieve)
    {κ δ R : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) (hR : 1 ≤ R) :
    ∃ η C ν : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < C ∧ 0 < ν ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ T₀ : ℝ, ∀ (r : γ) (X : ι → ℝ) (p q : ℝ) (v e : Eisenstein) (u : ℝ)
      (Ram S T J H : Finset Eisenstein), T₀ ≤ L r →
      (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      0 ≤ p → 0 ≤ q → p+2*q ≤ 1+η → κ ≤ p+2*q →
      δ ≤ |p-1|+|q| → δ ≤ |p-1/3|+|q-1/3| →
      (∀ s ∈ S, primary s ∧ Squarefree s ∧ norm s ≤ (L r)^p) →
      (∀ t ∈ T, primary t ∧ Squarefree t ∧ norm t ≤ (L r)^q) →
      H ⊆ coprimeResidualSupport Ram J (coprimePairs S T) →
      (∑ h ∈ H, ‖fullStructuredAngularPrimeSum ℓ R h 1 v e u (W r) X‖^2) ≤
        C*(Ram.card:ℝ)*J.card*(L r)^2*((L r)^p*((L r)^q)^2)^(1/3:ℝ)*(L r)^(-ν) := by
  have hK : 1 ≤ R^(Fintype.card ι) := one_le_pow₀ hR
  obtain ⟨η,C,ν,hη,hηhi,hC,hν,hraw⟩ := quantitative_dilated_noncube_mass hHuxley hK hκ hδ
  refine ⟨η,C,ν/2,hη,hηhi,hC,by positivity,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨T₀,henergy⟩ := logarithmic_structured_coefficient_energy hW
    (show 0 ≤ R by linarith) (show 0 < ν/2 by positivity) hlo hhi
  refine ⟨T₀,?_⟩
  intro r X p q v e u Ram S T J H hT₀ hX hprod hp hq hsize hlarge hfirst hbalanced hS hT hH
  let Z := R/2*L r
  let A := structuredFrequencySupport (W r) X Z
  let β := structuredAngularFrequencyCoefficient ℓ v e u (W r) X Z
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hXp : ∀ i, 0 < X i := fun i => zero_lt_one.trans_le (hX i)
  have hA : ∀ a ∈ A, primary a ∧ Squarefree a ∧ norm a ≤ R^(Fintype.card ι)*L r := by
    intro a ha
    simpa only [hprod] using structuredFrequencySupport_bounds (W r) X hXp
      (show 0 ≤ R by linarith) (hlo r) (hhi r) Z a ha
  have hE : (∑ a ∈ A, ‖β a‖^2) ≤ (L r)^(1+ν/2) :=
    (structuredAngularFrequencyCoefficient_energy_le ℓ v e u (W r) X Z).trans
      (henergy r X Z (hL r) hT₀ hXp hprod)
  have hm := hraw (L r) p q (hL r) hp hq hsize hlarge hfirst hbalanced
    A Ram S T J H hA hS hT hH β
  have hfull (h : Eisenstein) : fullStructuredAngularPrimeSum ℓ R h 1 v e u (W r) X =
      structuredAngularPrimeSum ℓ h 1 v e u (W r) X Z := by
    apply fullStructuredAngularPrimeSum_eq ℓ h 1 v e u (W r) X hXp (hhi r)
    intro i
    have hi : X i ≤ L r := by simpa only [hprod] using coordinate_le_product X hX i
    dsimp [Z]
    nlinarith [mul_le_mul_of_nonneg_left hi (show 0 ≤ R by linarith)]
  have heq : (∑ h ∈ H, ‖fullStructuredAngularPrimeSum ℓ R h 1 v e u (W r) X‖^2) =
      ∑ h ∈ H, ‖∑ a ∈ A, β a*cubicSymbol a h‖^2 := by
    apply Finset.sum_congr rfl
    intro h hh
    rw [hfull h,structuredAngularPrimeSum_eq_frequency ℓ]
  rw [heq]
  simpa only [neg_div] using noncube_energy_absorption hC.le (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hLp (Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg hLp.le _) (sq_nonneg _)) _)
    hE hm

end CubicFirstMoment

end

end OAI
