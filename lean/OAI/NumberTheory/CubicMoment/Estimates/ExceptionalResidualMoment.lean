import OAI.NumberTheory.CubicMoment.Estimates.FullExceptionalMoment
import OAI.NumberTheory.CubicMoment.Estimates.ExceptionalBenchmark
import OAI.NumberTheory.CubicMoment.Estimates.StructuredResidualFrequencies

namespace OAI

/-! The exceptional structured estimate on the actual ramified/cube
frequency block, including its local dispersion normalization. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma double_sum_real_const (S T : Finset Eisenstein) (x : ℝ) :
    (∑ _s ∈ S, ∑ _t ∈ T, x) = (S.card:ℝ)*T.card*x := by
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

lemma norm_mul_small_power {Y δ ρ : ℝ} (hY : 1 ≤ Y) (hδ : 2*δ ≤ ρ)
    {v r : Eisenstein} (hv : norm v ≤ Y^δ) (hr : norm r ≤ Y^δ) : norm (v*r) ≤ Y^ρ := by
  rw [norm_mul_eq]
  calc
    _ ≤ Y^δ*Y^δ := mul_le_mul hv hr (norm_nonneg _) (Real.rpow_nonneg (by linarith) _)
    _ = Y^(2*δ) := by rw [← Real.rpow_add (by linarith : 0 < Y)]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hY hδ

theorem exceptional_residual_moment (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {c R : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ δ ν : ℝ, 0 < δ ∧ 0 < ν ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ T : ℝ, ∀ (r : γ) (X : ι → ℝ) (v e : Eisenstein) (u p q : ℝ)
      (Ram J H : Finset Eisenstein) (P : Finset (Eisenstein × Eisenstein)), T ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      v ≠ 0 → e ≠ 0 → norm v ≤ (L r)^δ → norm e ≤ (L r)^δ →
      1+|u| ≤ (L r)^(9/25:ℝ) →
      (∀ a ∈ Ram, a ≠ 0 ∧ norm a ≤ (L r)^δ) →
      (∀ j ∈ J, j ≠ 0 ∧ norm j ≤ (L r)^δ) →
      (∀ z ∈ P, gramDyad ((L r)^p) z.1 ∧ gramDyad ((L r)^q) z.2 ∧ IsCoprime z.1 z.2) →
      ((|p-1| ≤ δ ∧ 0 ≤ q ∧ q ≤ δ) ∨ (|p-1/3| ≤ δ ∧ |q-1/3| ≤ δ)) →
      H ⊆ coprimeResidualSupport Ram J P →
      (∑ h ∈ H, ‖fullStructuredPrimeSum R h 1 v e u (W r) X‖^2) ≤
        (Ram.card:ℝ)*J.card*(L r)^2*((L r)^p*((L r)^q)^2)^(1/3:ℝ)*(L r)^(-ν) := by
  obtain ⟨ρ,ε,hρ,hε,hraw⟩ := full_exceptional_structured_moment (γ := γ) (ι := ι)
    hpub hHuxley hperiod hc hc₁ hR hGI hGQ
  let δ := min ρ ε/4
  have hδ : 0 < δ := div_pos (lt_min hρ hε) (by norm_num)
  have hδρ : 2*δ ≤ ρ := by dsimp [δ]; linarith [min_le_left ρ ε]
  have hδρ' : δ ≤ ρ := by linarith
  have hδε : δ ≤ ε/2 := by dsimp [δ]; linarith [min_le_right ρ ε]
  refine ⟨δ,ε/2,hδ,by positivity,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨T,hbound⟩ := hraw L W hL hW hlo hhi
  refine ⟨T,?_⟩
  intro r X v e u p q Ram J H P hT hprod hX hv he hvL heL hu hRam hJ hP hcase hH
  have hcase' : (|p-1| ≤ ρ ∧ 0 ≤ q ∧ q ≤ ρ) ∨ (|p-1/3| ≤ ρ ∧ |q-1/3| ≤ ρ) := by
    rcases hcase with ⟨hp,hq,hq'⟩ | ⟨hp,hq⟩
    · exact Or.inl ⟨hp.trans hδρ',hq,hq'.trans hδρ'⟩
    · exact Or.inr ⟨hp.trans hδρ',hq.trans hδρ'⟩
  have hb (a : Eisenstein) (ha : a ∈ Ram) (j : Eisenstein) (hj : j ∈ J) :
      (∑ z ∈ P, ‖fullStructuredPrimeSum R z.1 z.2 (v*a) (e*j) u (W r) X‖^2) ≤
        (L r)^(7/3-ε) := hbound r X (v*a) (e*j) u p q P hT hprod hX
      (mul_ne_zero hv (hRam a ha).1) (mul_ne_zero he (hJ j hj).1)
      (norm_mul_small_power (hL r) hδρ hvL (hRam a ha).2)
      (norm_mul_small_power (hL r) hδρ heL (hJ j hj).2) hu hP hcase'
  have hbenchmark := exceptional_moment_benchmark (hL r) hδ.le hδε hcase
    (le_rfl : (L r)^(7/3-ε) ≤ (L r)^(7/3-ε))
  calc
    _ ≤ ∑ a ∈ Ram, ∑ j ∈ J, ∑ z ∈ P,
        ‖fullStructuredPrimeSum R z.1 z.2 (v*a) (e*j) u (W r) X‖^2 :=
      fullStructured_residual_mass_le R Ram J H P hH v e u (W r) X
    _ ≤ ∑ _a ∈ Ram, ∑ _j ∈ J, (L r)^(7/3-ε) :=
      Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun j hj => hb a ha j hj))
    _ = (Ram.card:ℝ)*J.card*(L r)^(7/3-ε) := double_sum_real_const Ram J _
    _ ≤ (Ram.card:ℝ)*J.card*((L r)^2*((L r)^p*((L r)^q)^2)^(1/3:ℝ)*(L r)^(-ε/2)) :=
      mul_le_mul_of_nonneg_left hbenchmark (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ = _ := by rw [neg_div]; ring

end CubicFirstMoment

end

end OAI
