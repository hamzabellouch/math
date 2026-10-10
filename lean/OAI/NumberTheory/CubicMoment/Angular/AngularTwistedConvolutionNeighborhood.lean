import OAI.NumberTheory.CubicMoment.Angular.AngularComplexWeightedConvolution
import OAI.NumberTheory.CubicMoment.Angular.AngularFirstUnsplitNeighborhood
import OAI.NumberTheory.CubicMoment.Angular.AngularBalancedUnsplitNeighborhood

namespace OAI

/-! Exceptional moments for actual complex convolutions with an independent
residue character and Mellin height on each factor. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_first_twisted_convolution_neighborhood (hpub : PrimitiveAngularHeckeInput)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0)
    (hVhi : ∀ x, 2 < x → V x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F Y N : ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
      (t : ι → ℝ) (P : Finset Eisenstein),
      Y₀ ≤ Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) → F ≤ 2*Y → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, q i ≠ 0) →
      (∀ i, AngularUnitCompatible (q i) (η i) ℓ) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(361/1000:ℝ)) → (∀ a ∈ P, gramDyad N a) →
      (∑ a ∈ P, ‖primaryComplexProductPolynomial (fun i => angularTwistArithmetic ℓ (q i) (η i) (t i) (A i)) (mixedCubic a 1) V Y‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,ε,hε,T,hbound⟩ := angular_first_unsplit_tuple_neighborhood ℓ (ι := ι)
    hpub V hV hpos hsm hVlo hVhi hGI hGQ
  refine ⟨κ,hκ,hκhi,ε,hε,max 1 T,?_⟩
  intro F Y N A q η t P hY hNlo hNhi hF hA hq hη hqY ht hP
  have hYp : 0 < Y := zero_lt_one.trans_le ((le_max_left _ _).trans hY)
  have he (a : Eisenstein) (ha : a ∈ P) :
      primaryComplexProductPolynomial (fun i => angularTwistArithmetic ℓ (q i) (η i) (t i) (A i)) (mixedCubic a 1) V Y =
        primaryAngularUnsplitTuple ℓ A a 1 q η t V Y :=
    angularTwistedProductPolynomial_eq_unsplit ℓ A (hP a ha).1 (by norm_num [primary])
      q η hη t V hYp hVhi
  calc
    _ = ∑ a ∈ P, ‖primaryAngularUnsplitTuple ℓ A a 1 q η t V Y‖^2 :=
      Finset.sum_congr rfl (fun a ha => by rw [he a ha])
    _ ≤ _ := hbound F Y N A q η t P
      ((le_max_right _ _).trans hY) hNlo hNhi hF hA hq hη hqY ht hP

theorem angular_balanced_twisted_convolution_neighborhood (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0)
    (hVhi : ∀ x, 2 < x → V x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F Y : ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
      (t : ι → ℝ) (P : Finset (Eisenstein × Eisenstein)),
      Y₀ ≤ Y → F ≤ 2*Y → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, q i ≠ 0) →
      (∀ i, AngularUnitCompatible (q i) (η i) ℓ) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(361/1000:ℝ)) → (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
      (∑ a ∈ P, ‖primaryComplexProductPolynomial (fun i => angularTwistArithmetic ℓ (q i) (η i) (t i) (A i)) (mixedCubic a.1 a.2) V Y‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,ε,hε,T,hbound⟩ := angular_balanced_unsplit_tuple_neighborhood ℓ (ι := ι)
    hpub hHuxley V hV hpos hsm hVlo hVhi hGI hGQ
  refine ⟨κ,hκ,hκhi,ε,hε,max 1 T,?_⟩
  intro F Y A q η t P hY hF hA hq hη hqY ht hP
  have hYp : 0 < Y := zero_lt_one.trans_le ((le_max_left _ _).trans hY)
  have he (a : Eisenstein × Eisenstein) (ha : a ∈ P) :
      primaryComplexProductPolynomial (fun i => angularTwistArithmetic ℓ (q i) (η i) (t i) (A i)) (mixedCubic a.1 a.2) V Y =
        primaryAngularUnsplitTuple ℓ A a.1 a.2 q η t V Y :=
    angularTwistedProductPolynomial_eq_unsplit ℓ A (hP a ha).1.1 (hP a ha).1.2.1
      q η hη t V hYp hVhi
  calc
    _ = ∑ a ∈ P, ‖primaryAngularUnsplitTuple ℓ A a.1 a.2 q η t V Y‖^2 :=
      Finset.sum_congr rfl (fun a ha => by rw [he a ha])
    _ ≤ _ := hbound F Y A q η t P
      ((le_max_right _ _).trans hY) hF hA hq hη hqY ht hP

end CubicFirstMoment

end

end OAI
