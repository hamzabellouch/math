import OAI.NumberTheory.CubicMoment.Angular.AngularTwistedConvolutionNeighborhood
import OAI.NumberTheory.CubicMoment.Angular.AngularTwistedPrimeExpansion
import OAI.NumberTheory.CubicMoment.Estimates.FiniteMomentSaving

namespace OAI

/-! Original von Mangoldt convolutions with independent factor twists inherit
the short-factor power saving by an exact finite expansion. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_first_twisted_vonMangoldt_neighborhood (hpub : PrimitiveAngularHeckeInput)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0)
    (hVhi : ∀ x, 2 < x → V x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (Y N : ℝ) (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
      (t : ι → ℝ) (P : Finset Eisenstein), Y₀ ≤ Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) → (∀ i, q i ≠ 0) →
      (∀ i, AngularUnitCompatible (q i) (η i) ℓ) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(361/1000:ℝ)) → (∀ a ∈ P, gramDyad N a) →
      (∑ a ∈ P, ‖primaryComplexProductPolynomial (fun i => angularTwistArithmetic ℓ (q i) (η i) (t i) idealVonMangoldt)
        (mixedCubic a 1) V Y‖^2) ≤ Y^(7/3-ε) := by
  choose κ hκ hκhi e he T hb using fun S : Finset ι =>
    angular_first_twisted_convolution_neighborhood ℓ (ι := shortBranchIndex S) hpub V hV hpos hsm hVlo hVhi hGI hGQ
  obtain ⟨κ₀,hκ₀,hκall⟩ := finite_positive_lower_bound κ hκ
  obtain ⟨d,hd,T₁,hT₁,hsave⟩ := finite_weighted_moment_saving e he (shortBranchScalar (ι := ι))
  refine ⟨min κ₀ (1/10000),by positivity,min_le_right _ _,d,hd,max T₁ (1+∑ S, |T S|),?_⟩
  intro Y N q η t P hY hNlo hNhi hq hη hqY ht hP
  have hYT₁ : T₁ ≤ Y := (le_max_left _ _).trans hY
  have hY1 : 1 ≤ Y := hT₁.trans hYT₁
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hYT (S : Finset ι) : T S ≤ Y := by
    have hS : |T S| ≤ ∑ U : Finset ι, |T U| :=
      Finset.single_le_sum (fun U _ => abs_nonneg (T U)) (Finset.mem_univ S)
    have hh : 1+∑ U : Finset ι, |T U| ≤ Y := (le_max_right _ _).trans hY
    linarith [le_abs_self (T S)]
  let f : Finset ι → P → ℂ := fun S a =>
    primaryComplexProductPolynomial (fun j : shortBranchIndex S =>
      angularTwistArithmetic ℓ (q (shortBranchSource S j)) (η (shortBranchSource S j))
        (t (shortBranchSource S j)) (shortBranchFactor (2*Y) S j)) (mixedCubic a 1) V Y
  have hf (S : Finset ι) : (∑ a : P, ‖f S a‖^2) ≤ Y^(7/3-e S) := by
    have h := hb S (2*Y) Y N (shortBranchFactor (2*Y) S)
      (fun j => q (shortBranchSource S j)) (fun j => η (shortBranchSource S j))
      (fun j => t (shortBranchSource S j)) P
      (hYT S)
      ((Real.rpow_le_rpow_of_exponent_le hY1
        (by have := (min_le_left κ₀ (1/10000)).trans (hκall S); linarith)).trans hNlo)
      (hNhi.trans (Real.rpow_le_rpow_of_exponent_le hY1
        (by have := (min_le_left κ₀ (1/10000)).trans (hκall S); linarith))) le_rfl (shortBranchFactor_spec (2*Y) S)
      (fun j => hq _) (fun j => hη _) (fun j => hqY _) (fun j => ht _) hP
    change (∑ a ∈ P.attach, ‖f S a‖^2) ≤ _
    dsimp only [f]
    rw [Finset.sum_attach (f := fun a : Eisenstein =>
      ‖primaryComplexProductPolynomial (fun j : shortBranchIndex S =>
      angularTwistArithmetic ℓ (q (shortBranchSource S j)) (η (shortBranchSource S j))
        (t (shortBranchSource S j)) (shortBranchFactor (2*Y) S j)) (mixedCubic a 1) V Y‖^2)]
    exact h
  have hm := hsave Y hYT₁ P f hf
  simp_rw [primaryAngularTwistedPrimeWeight_expansion ℓ q η t _ V hYp]
  change (∑ a ∈ P.attach, ‖∑ S, shortBranchScalar S*f S a‖^2) ≤ _ at hm
  dsimp only [f] at hm
  rw [Finset.sum_attach (f := fun a : Eisenstein =>
    ‖∑ S : Finset ι, shortBranchScalar S*
      primaryComplexProductPolynomial (fun j : shortBranchIndex S =>
      angularTwistArithmetic ℓ (q (shortBranchSource S j)) (η (shortBranchSource S j))
        (t (shortBranchSource S j)) (shortBranchFactor (2*Y) S j)) (mixedCubic a 1) V Y‖^2)] at hm
  exact hm

theorem angular_balanced_twisted_vonMangoldt_neighborhood (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0)
    (hVhi : ∀ x, 2 < x → V x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (Y : ℝ) (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
      (t : ι → ℝ) (P : Finset (Eisenstein × Eisenstein)), Y₀ ≤ Y → (∀ i, q i ≠ 0) →
      (∀ i, AngularUnitCompatible (q i) (η i) ℓ) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(361/1000:ℝ)) → (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
      (∑ a ∈ P, ‖primaryComplexProductPolynomial (fun i => angularTwistArithmetic ℓ (q i) (η i) (t i) idealVonMangoldt)
        (mixedCubic (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2) V Y‖^2) ≤ Y^(7/3-ε) := by
  choose κ hκ hκhi e he T hb using fun S : Finset ι =>
    angular_balanced_twisted_convolution_neighborhood ℓ (ι := shortBranchIndex S) hpub hHuxley V hV hpos hsm hVlo hVhi hGI hGQ
  obtain ⟨κ₀,hκ₀,hκall⟩ := finite_positive_lower_bound κ hκ
  obtain ⟨d,hd,T₁,hT₁,hsave⟩ := finite_weighted_moment_saving e he (shortBranchScalar (ι := ι))
  refine ⟨min κ₀ (1/10000),by positivity,min_le_right _ _,d,hd,max T₁ (1+∑ S, |T S|),?_⟩
  intro Y q η t P hY hq hη hqY ht hP
  have hYT₁ : T₁ ≤ Y := (le_max_left _ _).trans hY
  have hY1 : 1 ≤ Y := hT₁.trans hYT₁
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hYT (S : Finset ι) : T S ≤ Y := by
    have hS : |T S| ≤ ∑ U : Finset ι, |T U| :=
      Finset.single_le_sum (fun U _ => abs_nonneg (T U)) (Finset.mem_univ S)
    have hh : 1+∑ U : Finset ι, |T U| ≤ Y := (le_max_right _ _).trans hY
    linarith [le_abs_self (T S)]
  let f : Finset ι → P → ℂ := fun S a =>
    primaryComplexProductPolynomial (fun j : shortBranchIndex S =>
      angularTwistArithmetic ℓ (q (shortBranchSource S j)) (η (shortBranchSource S j))
        (t (shortBranchSource S j)) (shortBranchFactor (2*Y) S j)) (mixedCubic (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2) V Y
  have hf (S : Finset ι) : (∑ a : P, ‖f S a‖^2) ≤ Y^(7/3-e S) := by
    have h := hb S (2*Y) Y (shortBranchFactor (2*Y) S)
      (fun j => q (shortBranchSource S j)) (fun j => η (shortBranchSource S j))
      (fun j => t (shortBranchSource S j)) P
      (hYT S) le_rfl (shortBranchFactor_spec (2*Y) S)
      (fun j => hq _) (fun j => hη _) (fun j => hqY _) (fun j => ht _)
      (fun a ha => ⟨(hP a ha).1,
        (hP a ha).2.1.trans (Real.rpow_le_rpow_of_exponent_le hY1
          (by have := (min_le_left κ₀ (1/10000)).trans (hκall S); linarith)),
        (hP a ha).2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hY1
          (by have := (min_le_left κ₀ (1/10000)).trans (hκall S); linarith)),(hP a ha).2.2.2⟩)
    change (∑ a ∈ P.attach, ‖f S a‖^2) ≤ _
    dsimp only [f]
    rw [Finset.sum_attach (f := fun a : Eisenstein × Eisenstein =>
      ‖primaryComplexProductPolynomial (fun j : shortBranchIndex S =>
      angularTwistArithmetic ℓ (q (shortBranchSource S j)) (η (shortBranchSource S j))
        (t (shortBranchSource S j)) (shortBranchFactor (2*Y) S j)) (mixedCubic (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2) V Y‖^2)]
    exact h
  have hm := hsave Y hYT₁ P f hf
  simp_rw [primaryAngularTwistedPrimeWeight_expansion ℓ q η t _ V hYp]
  change (∑ a ∈ P.attach, ‖∑ S, shortBranchScalar S*f S a‖^2) ≤ _ at hm
  dsimp only [f] at hm
  rw [Finset.sum_attach (f := fun a : Eisenstein × Eisenstein =>
    ‖∑ S : Finset ι, shortBranchScalar S*
      primaryComplexProductPolynomial (fun j : shortBranchIndex S =>
      angularTwistArithmetic ℓ (q (shortBranchSource S j)) (η (shortBranchSource S j))
        (t (shortBranchSource S j)) (shortBranchFactor (2*Y) S j)) (mixedCubic (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2) V Y‖^2)] at hm
  exact hm

end CubicFirstMoment

end

end OAI
