import OAI.NumberTheory.CubicMoment.Angular.AngularDyadicNoncubeMoment
import OAI.NumberTheory.CubicMoment.Angular.AngularExceptionalResidualMoment
import OAI.NumberTheory.CubicMoment.Estimates.ExceptionalCubeBound

namespace OAI

/-! A single saving across the entire large-conductor region. The cube
factor is proved small where the exceptional moment is needed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_large_conductor_structured_moment (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {c R κ : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R) (hκ : 0 < κ)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ η σ C ν : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧ 0 < C ∧ 0 < ν ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ T₀ : ℝ, ∀ (r : γ) (X : ι → ℝ) (p q : ℝ) (v e : Eisenstein) (u : ℝ)
      (Ram S T J H : Finset Eisenstein), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      0 ≤ p → 0 ≤ q → p+2*q ≤ 1+η → κ ≤ p+2*q →
      v ≠ 0 → e ≠ 0 → norm v ≤ (L r)^σ → norm e ≤ (L r)^σ →
      1+|u| ≤ (L r)^(9/25:ℝ) →
      (∀ a ∈ Ram, a ≠ 0 ∧ norm a ≤ (L r)^σ) →
      (∀ j ∈ J, j ≠ 0 ∧ norm j^3*((L r)^p*((L r)^q)^2) ≤ (L r)^(1+η)) →
      (∀ s ∈ S, gramDyad ((L r)^p) s) → (∀ t ∈ T, gramDyad ((L r)^q) t) →
      H ⊆ coprimeResidualSupport Ram J (coprimePairs S T) →
      (∑ h ∈ H, ‖fullStructuredAngularPrimeSum ℓ R h 1 v e u (W r) X‖^2) ≤
        C*(Ram.card:ℝ)*J.card*(L r)^2*((L r)^p*((L r)^q)^2)^(1/3:ℝ)*(L r)^(-ν) := by
  obtain ⟨σ,νE,hσ,hνE,hE⟩ := angular_exceptional_residual_moment ℓ (γ := γ) (ι := ι)
    hpub hHuxley hperiod hc hc₁ hR hGI hGQ
  let δ := σ/8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨ηN,CN,νN,hηN,hηNhi,hCN,hνN,hN⟩ := angular_dyadic_full_noncube ℓ (γ := γ) (ι := ι)
    hHuxley hκ hδ hR
  let η := min ηN (σ/8)
  let C := max 1 CN
  let ν := min νE νN
  have hη : 0 < η := lt_min hηN (by positivity)
  have hηhi : η ≤ 1 := (min_le_left _ _).trans hηNhi
  have hδσ : δ ≤ σ := by dsimp [δ]; linarith
  have hηδ : η+3*δ ≤ 3*σ := by dsimp [η,δ]; linarith [min_le_right ηN (σ/8)]
  refine ⟨η,σ,C,ν,hη,hηhi,hσ,lt_of_lt_of_le zero_lt_one (le_max_left _ _),lt_min hνE hνN,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨TE,hBE⟩ := hE L W hL hW hlo hhi
  obtain ⟨TN,hBN⟩ := hN L W hL hW hlo hhi
  refine ⟨max TE TN,?_⟩
  intro r X p q v e u Ram S T J H hT₀ hprod hX hp hq hsize hlarge hv he hvL heL hu hRam hJ hS hT hH
  let A := (Ram.card:ℝ)*J.card*(L r)^2*((L r)^p*((L r)^q)^2)^(1/3:ℝ)
  have hA : 0 ≤ A :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (sq_nonneg _)) (Real.rpow_nonneg
        (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (hL r)) _) (sq_nonneg _)) _)
  have hXone : ∀ i, 1 ≤ X i := fun i => (Real.one_le_rpow
    (show 1 ≤ 2*L r by linarith [hL r]) hc.le).trans (hX i).le
  have hPE : ∀ z ∈ coprimePairs S T,
      gramDyad ((L r)^p) z.1 ∧ gramDyad ((L r)^q) z.2 ∧ IsCoprime z.1 z.2 := by
    intro z hz
    have hh := Finset.mem_filter.mp hz
    have hz' := Finset.mem_product.mp hh.1
    exact ⟨hS z.1 hz'.1,hT z.2 hz'.2,hh.2⟩
  have exceptional (hcase : (|p-1| ≤ δ ∧ 0 ≤ q ∧ q ≤ δ) ∨
      (|p-1/3| ≤ δ ∧ |q-1/3| ≤ δ)) :
      (∑ h ∈ H, ‖fullStructuredAngularPrimeSum ℓ R h 1 v e u (W r) X‖^2) ≤ C*A*(L r)^(-ν) := by
    have hcE : (|p-1| ≤ σ ∧ 0 ≤ q ∧ q ≤ σ) ∨ (|p-1/3| ≤ σ ∧ |q-1/3| ≤ σ) := by
      rcases hcase with ⟨hp,hq,hq'⟩ | ⟨hp,hq⟩
      · exact Or.inl ⟨hp.trans hδσ,hq,hq'.trans hδσ⟩
      · exact Or.inr ⟨hp.trans hδσ,hq.trans hδσ⟩
    have hjE : ∀ j ∈ J, j ≠ 0 ∧ norm j ≤ (L r)^σ := by
      intro j hj
      exact ⟨(hJ j hj).1,cube_factor_exceptional_bound (hL r) (norm_nonneg j) hηδ
        (exceptional_conductor_lower hδ.le hcase) (hJ j hj).2⟩
    have hh := hBE r X v e u p q Ram J H (coprimePairs S T) ((le_max_left _ _).trans hT₀)
      hprod hX hv he hvL heL hu hRam hjE hPE hcE hH
    have hs := moment_constant_saving_mono hA (show (0:ℝ) ≤ 1 by norm_num)
      (show (1:ℝ) ≤ C from le_max_left _ _) (hL r) (min_le_left νE νN)
    apply hh.trans
    simpa only [one_mul,A,mul_assoc] using hs
  have goal_eq : C*A*(L r)^(-ν) =
      C*(Ram.card:ℝ)*J.card*(L r)^2*((L r)^p*((L r)^q)^2)^(1/3:ℝ)*(L r)^(-ν) := by dsimp [A]; ring
  rw [← goal_eq]
  by_cases hf : δ ≤ |p-1|+|q|
  · by_cases hb : δ ≤ |p-1/3|+|q-1/3|
    · have hh := hBN r X p q v e u Ram S T J H ((le_max_right _ _).trans hT₀)
        hXone hprod hp hq (hsize.trans (by dsimp [η]; linarith [min_le_left ηN (σ/8)]))
        hlarge hf hb hS hT hH
      have hs := moment_constant_saving_mono hA hCN.le (show CN ≤ C from le_max_right _ _)
        (hL r) (min_le_right νE νN)
      apply hh.trans
      simpa only [A,mul_assoc] using hs
    · apply exceptional (Or.inr ?_)
      constructor <;> linarith [lt_of_not_ge hb,abs_nonneg (p-1/3),abs_nonneg (q-1/3)]
  · apply exceptional (Or.inl ?_)
    have hh : |p-1|+q < δ := by simpa only [abs_of_nonneg hq] using lt_of_not_ge hf
    exact ⟨by linarith, hq, by linarith [abs_nonneg (p-1)]⟩

end CubicFirstMoment

end

end OAI
