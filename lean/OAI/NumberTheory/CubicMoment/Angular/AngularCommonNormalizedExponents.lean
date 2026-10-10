import OAI.NumberTheory.CubicMoment.Angular.AngularWideLogDenominator
import OAI.NumberTheory.CubicMoment.Angular.AngularCommonCoordinateExponents
import OAI.NumberTheory.CubicMoment.Angular.AngularNormalizedCoordinateMoments

namespace OAI

/-! Both normalized prime moments uniformly over actual smooth-weight families. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem angular_first_common_normalized_exponents (hpub : PrimitiveAngularHeckeInput)
    {c : ℝ} (hc : 0 < c)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
    (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (W : γ → ι → ℝ → ℂ), UniformLogWeights (fun z : γ × ι => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → ∃ Y₀ : ℝ,
      ∀ (r : γ) (Y N : ℝ) (X : ι → ℝ) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset Eisenstein),
      Y₀ ≤ Y → 0 < Y → 1 ≤ Real.log Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) →
      (∀ i, Y^c ≤ X i) → (∀ i, X i ≤ Y^2) → (∀ i, q i ≠ 0) →
      (∀ i, AngularUnitCompatible (q i) (η i) ℓ) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(721/2000:ℝ)) →
      (∀ a ∈ P, gramDyad N a) →
      (∑ a ∈ P, ‖primaryAngularNormalizedVonMangoldtTuple ℓ a 1 q η t (W r) X V Y‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,e,he,hraw⟩ := angular_first_common_coordinate_exponents ℓ
    (γ := γ × (ι → wideLogWeightParameters c)) (ι := ι) hpub V hV hposV hsmV hVlo hVhi hGI hGQ
  refine ⟨κ,hκ,hκhi,e,he,?_⟩
  intro W hW hWlo
  let L : (γ × (ι → wideLogWeightParameters c)) → ι → ℝ → ℂ :=
    fun r i => logDenominatorWeight c (W r.1 i) (r.2 i)
  have hL : UniformLogWeights (fun z : (γ × (ι → wideLogWeightParameters c)) × ι => L z.1 z.2) :=
    uniformCoordinateWideLogDenominatorWeights hc hW
  obtain ⟨T,hfamily⟩ := hraw L hL
  refine ⟨T,?_⟩
  intro r Y N X q η t P hYT hY0 hlog hNlo hNhi hXlo hXhi hq hη hqY ht hP
  let p : ι → wideLogWeightParameters c := fun i =>
    ⟨(Real.log (X i)/Real.log Y,1/Real.log Y),wideLogWeightParameters_mem hY0 hlog (hXlo i) (hXhi i)⟩
  have hb := hfamily (r,p) Y N X q η t P hYT hNlo hNhi
    (fun i => (Real.rpow_pos_of_pos hY0 c).trans_le (hXlo i)) hq hη hqY ht hP
  apply le_trans _ hb
  apply Finset.sum_le_sum
  intro a ha
  exact pow_le_pow_left₀ (_root_.norm_nonneg _)
    (angular_normalizedCoordinate_norm_le_lower ℓ hc hY0 hlog a 1 q η t (W r) X V (hWlo r) hXlo) 2

 theorem angular_balanced_common_normalized_exponents (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) {c : ℝ} (hc : 0 < c)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
    (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (W : γ → ι → ℝ → ℂ), UniformLogWeights (fun z : γ × ι => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → ∃ Y₀ : ℝ,
      ∀ (r : γ) (Y : ℝ) (X : ι → ℝ) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
      (P : Finset (Eisenstein × Eisenstein)),
      Y₀ ≤ Y → 0 < Y → 1 ≤ Real.log Y →
      (∀ i, Y^c ≤ X i) → (∀ i, X i ≤ Y^2) → (∀ i, q i ≠ 0) →
      (∀ i, AngularUnitCompatible (q i) (η i) ℓ) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(721/2000:ℝ)) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
      (∑ a ∈ P, ‖primaryAngularNormalizedVonMangoldtTuple ℓ a.1 a.2 q η t (W r) X V Y‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,e,he,hraw⟩ := angular_balanced_common_coordinate_exponents ℓ
    (γ := γ × (ι → wideLogWeightParameters c)) (ι := ι) hpub hHuxley V hV hposV hsmV hVlo hVhi hGI hGQ
  refine ⟨κ,hκ,hκhi,e,he,?_⟩
  intro W hW hWlo
  let L : (γ × (ι → wideLogWeightParameters c)) → ι → ℝ → ℂ :=
    fun r i => logDenominatorWeight c (W r.1 i) (r.2 i)
  have hL : UniformLogWeights (fun z : (γ × (ι → wideLogWeightParameters c)) × ι => L z.1 z.2) :=
    uniformCoordinateWideLogDenominatorWeights hc hW
  obtain ⟨T,hfamily⟩ := hraw L hL
  refine ⟨T,?_⟩
  intro r Y X q η t P hYT hY0 hlog hXlo hXhi hq hη hqY ht hP
  let p : ι → wideLogWeightParameters c := fun i =>
    ⟨(Real.log (X i)/Real.log Y,1/Real.log Y),wideLogWeightParameters_mem hY0 hlog (hXlo i) (hXhi i)⟩
  have hb := hfamily (r,p) Y X q η t P hYT
    (fun i => (Real.rpow_pos_of_pos hY0 c).trans_le (hXlo i)) hq hη hqY ht hP
  apply le_trans _ hb
  apply Finset.sum_le_sum
  intro a ha
  exact pow_le_pow_left₀ (_root_.norm_nonneg _)
    (angular_normalizedCoordinate_norm_le_lower ℓ hc hY0 hlog a.1 a.2 q η t (W r) X V (hWlo r) hXlo) 2

end CubicFirstMoment

end

end OAI
