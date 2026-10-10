import OAI.Analysis.KadisonKastler.NormalizedPolarPath
import OAI.Analysis.KadisonKastler.SmoothedNormalizerPaths
import OAI.Analysis.KadisonKastler.SmoothingProductComparison

namespace OAI

/-! # Uniform exact normalizers from quantitative smoothing data

All radii and constants are chosen before the Hilbert space and factor.
The smoothing hypotheses give continuous approximate inverses with
controlled algebra distance and strong-star convergence.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

private theorem exists_smoothing_radius {e0 L : ℝ} (he0 : 0 < e0) (hL : 0 < L) :
    ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r < r0 →
      r < 1 / 8 ∧ 50 * r < e0 ∧ L * r < 1 / 1000 ∧ 2 * r + L * r < 1 := by
  let r0 := min (1 / 8) (min (e0 / 50) (1 / (1000 * (L + 2))))
  have hp : 0 < r0 := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  refine ⟨r0, hp, ?_⟩
  intro r hr hsmall
  have h₁ := hsmall.trans_le (min_le_left _ _)
  have h₂ := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have h₃ := hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  change r < 1 / (1000 * (L + 2)) at h₃
  have hmul := (lt_div_iff₀ (show 0 < 1000 * (L + 2) by positivity)).mp h₃
  refine ⟨h₁, ?_, ?_, ?_⟩ <;> change r < e0 / 50 at h₂ <;> nlinarith

local instance smoothingInputOrder {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance smoothingInputStarOrder {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

theorem uniform_typeIII_normalizer_from_smoothing
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (hSakai : PublishedSimpleDerivationInner.{u})
    (hDistance : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H], ∀ M : VonNeumannAlgebra H,
        PublishedBlockCommutantApproximation (Algebra M) H) :
    ∃ r0 C : ℝ, 0 < r0 ∧ 0 < C ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [Nontrivial H] [TopologicalSpace.SeparableSpace H],
      ∀ (M : VonNeumannAlgebra H), TypeIIIFactor M →
      ∀ (W : ℝ → unitary (H →L[ℂ] H)), W 0 = 1 →
      (∀ t, PublishedMultiplicationCorrection (unitaryConjugateAlgebra (W t) M)) →
      ∀ (a c D : ℕ → ℝ → H →L[ℂ] H) (r : ℝ), 0 < r → r < r0 →
      (∀ n, Continuous (a n)) →
      (∀ n t, ‖a n t‖ ≤ 1 + r) → (∀ n t, ‖c n t‖ ≤ 1 + r) →
      (∀ n t, ‖a n t * c n t - 1‖ ≤ r) → (∀ n t, ‖c n t * a n t - 1‖ ≤ r) →
      (∀ n t x, x ∈ unitBall M →
        Metric.infDist (a n t * x * c n t) (M : Set (H →L[ℂ] H)) ≤ r) →
      (∀ n t x, x ∈ unitBall M →
        Metric.infDist (c n t * x * a n t) (M : Set (H →L[ℂ] H)) ≤ r) →
      (∀ n t, ‖D n t‖ ≤ 2) → (∀ n t, ‖a n t - D n t‖ ≤ r) →
      (∀ t x, Tendsto (fun n => D n t x) atTop (𝓝 ((W t : H →L[ℂ] H) x))) →
      (∀ t x, Tendsto (fun n => star (D n t) x) atTop (𝓝 (star (W t : H →L[ℂ] H) x))) →
      (∀ t, kkDistance (unitaryConjugateAlgebra (W t) M) M < 2 * r) →
      ∀ t, ∃ v : unitary (H →L[ℂ] H), Conjugates v M M ∧
        ‖(v : H →L[ℂ] H) - W t‖ ≤ C * r := by
  obtain ⟨e0, K, he0, hK, hnormalizer⟩ := uniform_typeIII_smoothed_normalizers
    hSpectral hCompare hSakai hDistance
  let L := 5 * (50 * (K + 1) + 15)
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨r0, hr0, hsmall⟩ := exists_smoothing_radius he0 hL
  refine ⟨r0, 128 * L, hr0, by positivity, ?_⟩
  intro H _ _ _ _ _ M hM W hW0 hCorrection a c D r hr hrr ha han hcn hac hca
    halg hcalg hDn haD hD hDs hgap t
  obtain ⟨hrsmall, he, hLs, hgs⟩ := hsmall r hr hrr
  choose v E hv hE hE0 hEv hva hvc hdef using fun n =>
    exists_based_polar_normalizer_path M (a n) (c n) (ha n) hr.le hrsmall
      (han n) (hcn n) (hac n) (hca n) (halg n) (hcalg n)
  let Q (n : ℕ) := D n t * star (D n 0)
  have hQn (n : ℕ) : ‖Q n‖ ≤ 4 := by
    exact (norm_mul_le _ _).trans ((mul_le_mul (hDn n t)
      ((norm_star _).le.trans (hDn n 0)) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num))
  have hQstar (x : H) : Tendsto (fun n => star (Q n) x) atTop
      (𝓝 (star (W t : H →L[ℂ] H) x)) := by
    have hh := tendsto_operator_comp_of_uniform_bound
      (fun n => D n 0) (fun n => star (D n t))
      (W 0) (star (W t : H →L[ℂ] H)) 2 (Eventually.of_forall fun n => hDn n 0)
      (hD 0) (hDs t) x
    simpa only [Q, star_mul, star_star, hW0, OneMemClass.coe_one, one_mul] using hh
  have hvD (n : ℕ) (s : ℝ) : ‖(v n s : H →L[ℂ] H) - D n s‖ ≤ 5 * r :=
    (norm_sub_le_norm_sub_add_norm_sub _ (a n s) _).trans
      ((add_le_add (hva n s) (haD n s)).trans_eq (by ring))
  have hEQ (n : ℕ) : ‖(E n t : H →L[ℂ] H) - Q n‖ ≤ 15 * r := by
    rw [hEv]
    exact (norm_unitary_product_sub_le (v n t) (v n 0) (D n t) (D n 0)
      (by norm_num) (hvD n t) (hvD n 0) (hDn n t)).trans_eq (by ring)
  have hsmall' : (1 + 4) * ((K + 1) * (50 * r) + 15 * r) < 1 / 1000 := by
    convert hLs using 1
    dsimp [L]
    ring
  have hge' : 2 * r + (1 + 4) * ((K + 1) * (50 * r) + 15 * r) < 1 := by
    convert hgs using 1
    dsimp [L]
    ring
  obtain ⟨p, hp, hpn⟩ := hnormalizer H M hM (W t) (hCorrection t) E Q t (50 * r)
    (15 * r) 4 (2 * r) (by positivity) he (by positivity) (by norm_num)
    hE hE0 hdef hQstar hEQ hQn hsmall' hge' (hgap t)
  refine ⟨p, hp, ?_⟩
  convert hpn using 1
  dsimp [L]
  ring

end

end KadisonKastler

end OAI
