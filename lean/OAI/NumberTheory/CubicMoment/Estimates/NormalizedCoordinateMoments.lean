import OAI.NumberTheory.CubicMoment.Estimates.NormalizedCoordinateTuple
import OAI.NumberTheory.CubicMoment.Estimates.FirstUniformCoordinateNeighborhood
import OAI.NumberTheory.CubicMoment.Estimates.BalancedUniformCoordinateNeighborhood

namespace OAI

/-! The actual normalized von Mangoldt factors inherit both exceptional
moment savings. Their logarithmic denominators have been constructed, not
postulated as an additional smooth-weight input. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma normalizedCoordinate_norm_le {c Y : ℝ} (hc : 0 < c) (hY0 : 0 < Y)
    (hY : 1 ≤ Real.log Y) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ)
    (hWlo : ∀ i x, x < 1 → W i x = 0)
    (hXlo : ∀ i, Y^c ≤ X i) (hXhi : ∀ i, X i ≤ Y) :
    ‖primaryNormalizedVonMangoldtTuple a b q η t W X V Y‖ ≤
      ‖primaryCoordinateWeightedTuple (fun _ : ι => idealVonMangoldt)
        a b q η t (fun i => logDenominatorWeight c (W i)
          (Real.log (X i)/Real.log Y,1/Real.log Y)) X V Y‖ := by
  rw [primaryNormalizedVonMangoldtTuple_eq hc hY0 hY a b q η t W X V hWlo hXlo hXhi,
    norm_mul,norm_pow]
  apply mul_le_of_le_one_left (_root_.norm_nonneg _)
  apply pow_le_one₀ (_root_.norm_nonneg _) _
  rw [norm_div,norm_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith)]
  exact (div_le_one (by linarith)).mpr hY

 theorem first_normalized_vonMangoldt_neighborhood (hpub : PrimitiveResidueHeckeInput)
    {c : ℝ} (hc : 0 < c)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
    (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (W : ι → ℝ → ℂ) (hW : ∀ i, HasCompactSupport (W i))
    (hposW : ∀ i, tsupport (W i) ⊆ Ioi 0) (hsmW : ∀ i, ContDiff ℝ ∞ (W i))
    (hWlo : ∀ i x, x < 1 → W i x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ,
      ∀ (Y N : ℝ) (X : ι → ℝ) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset Eisenstein),
      Y₀ ≤ Y → 0 < Y → 1 ≤ Real.log Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) →
      (∀ i, Y^c ≤ X i) → (∀ i, X i ≤ Y) → (∀ i, q i ≠ 0) →
      (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(9/25:ℝ)) →
      (∀ a ∈ P, gramDyad N a) →
      (∑ a ∈ P, ‖primaryNormalizedVonMangoldtTuple a 1 q η t W X V Y‖^2) ≤
        Y^(7/3-ε) := by
  let L : (ι → logWeightParameters c) → ι → ℝ → ℂ :=
    fun p i => logDenominatorWeight c (W i) (p i)
  have hL := coordinateLogDenominatorWeights hc W hW hposW hsmW
  obtain ⟨κ,hκ,hκhi,e,he,T,hraw⟩ := first_uniform_coordinate_vonMangoldt_neighborhood
    hpub V hV hposV hsmV hVlo hVhi L hL hGI hGQ
  refine ⟨κ,hκ,hκhi,e,he,T,?_⟩
  intro Y N X q η t P hYT hY0 hlog hNlo hNhi hXlo hXhi hq hη hqY ht hP
  let p : ι → logWeightParameters c := fun i =>
    ⟨(Real.log (X i)/Real.log Y,1/Real.log Y),logWeightParameters_mem hc hY0 hlog (hXlo i) (hXhi i)⟩
  have hb := hraw p Y N X q η t P hYT hNlo hNhi
    (fun i => (Real.rpow_pos_of_pos hY0 c).trans_le (hXlo i)) hq hη hqY ht hP
  apply le_trans _ hb
  apply Finset.sum_le_sum
  intro a ha
  exact pow_le_pow_left₀ (_root_.norm_nonneg _)
    (normalizedCoordinate_norm_le hc hY0 hlog a 1 q η t W X V hWlo hXlo hXhi) 2

 theorem balanced_normalized_vonMangoldt_neighborhood (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) {c : ℝ} (hc : 0 < c)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
    (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (W : ι → ℝ → ℂ) (hW : ∀ i, HasCompactSupport (W i))
    (hposW : ∀ i, tsupport (W i) ⊆ Ioi 0) (hsmW : ∀ i, ContDiff ℝ ∞ (W i))
    (hWlo : ∀ i x, x < 1 → W i x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ,
      ∀ (Y : ℝ) (X : ι → ℝ) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
      (P : Finset (Eisenstein × Eisenstein)),
      Y₀ ≤ Y → 0 < Y → 1 ≤ Real.log Y →
      (∀ i, Y^c ≤ X i) → (∀ i, X i ≤ Y) → (∀ i, q i ≠ 0) →
      (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(9/25:ℝ)) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
      (∑ a ∈ P, ‖primaryNormalizedVonMangoldtTuple a.1 a.2 q η t W X V Y‖^2) ≤
        Y^(7/3-ε) := by
  let L : (ι → logWeightParameters c) → ι → ℝ → ℂ :=
    fun p i => logDenominatorWeight c (W i) (p i)
  have hL := coordinateLogDenominatorWeights hc W hW hposW hsmW
  obtain ⟨κ,hκ,hκhi,e,he,T,hraw⟩ := balanced_uniform_coordinate_vonMangoldt_neighborhood
    hpub hHuxley V hV hposV hsmV hVlo hVhi L hL hGI hGQ
  refine ⟨κ,hκ,hκhi,e,he,T,?_⟩
  intro Y X q η t P hYT hY0 hlog hXlo hXhi hq hη hqY ht hP
  let p : ι → logWeightParameters c := fun i =>
    ⟨(Real.log (X i)/Real.log Y,1/Real.log Y),logWeightParameters_mem hc hY0 hlog (hXlo i) (hXhi i)⟩
  have hb := hraw p Y X q η t P hYT
    (fun i => (Real.rpow_pos_of_pos hY0 c).trans_le (hXlo i)) hq hη hqY ht hP
  apply le_trans _ hb
  apply Finset.sum_le_sum
  intro a ha
  exact pow_le_pow_left₀ (_root_.norm_nonneg _)
    (normalizedCoordinate_norm_le hc hY0 hlog a.1 a.2 q η t W X V hWlo hXlo hXhi) 2

end CubicFirstMoment

end

end OAI
