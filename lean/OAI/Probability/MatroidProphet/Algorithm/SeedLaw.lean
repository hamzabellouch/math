import OAI.Probability.MatroidProphet.SeedLaw
import OAI.Probability.MatroidProphet.Algorithm.Rule
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

namespace MatroidProphet

open MeasureTheory Finset

abbrev MainSeedBlocks (n : ℕ) := Seed n × (Seed n × (Seed n × (Seed n × Seed 2)))

noncomputable def encodeMainSeed {n : ℕ} (b : MainSeedBlocks n) : Seed (mainSeedBits n) :=
  fun i => if hi : i.val < 4*n then
    let e : Fin n := ⟨i.val / 4, by omega⟩
    if i.val % 4 = 0 then b.1 e else
    if i.val % 4 = 1 then b.2.1 e else
    if i.val % 4 = 2 then b.2.2.1 e else b.2.2.2.1 e
  else b.2.2.2.2 ⟨i.val-4*n, by have := i.isLt; dsimp [mainSeedBits] at this; omega⟩

lemma encodeMainSeed_mask {n : ℕ} (b : MainSeedBlocks n) :
    seedMask (encodeMainSeed b) 0 = seedSet b.1 ∧
    seedMask (encodeMainSeed b) 1 = seedSet b.2.1 ∧
    seedMask (encodeMainSeed b) 2 = seedSet b.2.2.1 ∧
    seedMask (encodeMainSeed b) 3 = seedSet b.2.2.2.1 := by
  have h0 : ∀ e : Fin n, 4*e.val+0 < 4*n := fun e => by omega
  have h1 : ∀ e : Fin n, 4*e.val+1 < 4*n := fun e => by omega
  have h2 : ∀ e : Fin n, 4*e.val+2 < 4*n := fun e => by omega
  have h3 : ∀ e : Fin n, 4*e.val+3 < 4*n := fun e => by omega
  repeat' constructor
  all_goals
    ext e
    simp_all [seedMask, seedSet, encodeMainSeed, Nat.add_mod, Nat.mul_add_div]

lemma encodeMainSeed_branch {n : ℕ} (b : MainSeedBlocks n) :
    mainBranch (encodeMainSeed b) = b.2.2.2.2 0 := by
  simp [mainBranch, encodeMainSeed]

lemma encodeMainSeed_odd {n : ℕ} (b : MainSeedBlocks n) :
    (mainMasks (encodeMainSeed b)).odd = b.2.2.2.2 1 := by
  have h : ¬ 4*n+1 < 4*n := by omega
  simp [mainMasks, encodeMainSeed, h]

noncomputable def maskCoinLaw (n : ℕ) (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : Measure (Seed n) :=
  bernoulliSeedLaw (fun _ => p) (fun _ => h0) (fun _ => h1)

instance maskCoinLaw_probability (n : ℕ) (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    IsProbabilityMeasure (maskCoinLaw n p h0 h1) := by
  unfold maskCoinLaw
  infer_instance

noncomputable def mainBlockLaw (n : ℕ) (q : Fin 5 → ℝ)
    (h0 : ∀ j, 0 ≤ q j) (h1 : ∀ j, q j ≤ 1) : Measure (MainSeedBlocks n) :=
  (maskCoinLaw n (q 0) (h0 0) (h1 0)).prod
    ((maskCoinLaw n (q 1) (h0 1) (h1 1)).prod
      ((maskCoinLaw n (q 2) (h0 2) (h1 2)).prod
        ((maskCoinLaw n (q 3) (h0 3) (h1 3)).prod
          (maskCoinLaw 2 (q 4) (h0 4) (h1 4)))))

instance mainBlockLaw_probability (n : ℕ) (q : Fin 5 → ℝ)
    (h0 : ∀ j, 0 ≤ q j) (h1 : ∀ j, q j ≤ 1) :
    IsProbabilityMeasure (mainBlockLaw n q h0 h1) := by
  unfold mainBlockLaw
  infer_instance

noncomputable def mainSeedLaw (n : ℕ) (q : Fin 5 → ℝ)
    (h0 : ∀ j, 0 ≤ q j) (h1 : ∀ j, q j ≤ 1) : Measure (Seed (mainSeedBits n)) :=
  (mainBlockLaw n q h0 h1).map encodeMainSeed

instance mainSeedLaw_probability (n : ℕ) (q : Fin 5 → ℝ)
    (h0 : ∀ j, 0 ≤ q j) (h1 : ∀ j, q j ≤ 1) :
    IsProbabilityMeasure (mainSeedLaw n q h0 h1) :=
  inferInstanceAs (IsProbabilityMeasure ((mainBlockLaw n q h0 h1).map encodeMainSeed))

lemma integral_mainSeedLaw (n : ℕ) (q : Fin 5 → ℝ)
    (h0 : ∀ j, 0 ≤ q j) (h1 : ∀ j, q j ≤ 1) (f : Seed (mainSeedBits n) → ℝ) :
    (∫ r, f r ∂mainSeedLaw n q h0 h1) =
      ∫ H, ∫ D, ∫ C, ∫ T, ∫ b, f (encodeMainSeed (H, D, C, T, b))
        ∂maskCoinLaw 2 (q 4) (h0 4) (h1 4)
        ∂maskCoinLaw n (q 3) (h0 3) (h1 3)
        ∂maskCoinLaw n (q 2) (h0 2) (h1 2)
        ∂maskCoinLaw n (q 1) (h0 1) (h1 1)
        ∂maskCoinLaw n (q 0) (h0 0) (h1 0) := by
  rw [mainSeedLaw, integral_map_of_stronglyMeasurable (measurable_of_countable _)
    (measurable_of_countable f).stronglyMeasurable]
  simp only [mainBlockLaw]
  rw [integral_prod _ Integrable.of_finite]
  apply integral_congr_ae
  exact ae_of_all _ fun H => by
    dsimp only
    rw [integral_prod _ Integrable.of_finite]
    apply integral_congr_ae
    exact ae_of_all _ fun D => by
      dsimp only
      rw [integral_prod _ Integrable.of_finite]
      apply integral_congr_ae
      exact ae_of_all _ fun C => by
        dsimp only
        rw [integral_prod _ Integrable.of_finite]

lemma mainSeedLaw_expectation (n : ℕ) (q : Fin 5 → ℝ)
    (h0 : ∀ j, 0 ≤ q j) (h1 : ∀ j, q j ≤ 1) (f : Seed (mainSeedBits n) → ℝ) :
    (∫ r, f r ∂mainSeedLaw n q h0 h1) =
      bitsExpectation (fun _ : Fin n => q 0) Finset.univ (fun H =>
        bitsExpectation (fun _ : Fin n => q 1) Finset.univ (fun D =>
          bitsExpectation (fun _ : Fin n => q 2) Finset.univ (fun C =>
            bitsExpectation (fun _ : Fin n => q 3) Finset.univ (fun T =>
              bitsExpectation (fun _ : Fin 2 => q 4) Finset.univ (fun b =>
                f (encodeMainSeed (setSeed H, setSeed D, setSeed C, setSeed T, setSeed b))))))) := by
  rw [integral_mainSeedLaw]
  simp only [maskCoinLaw, integral_bernoulliSeedLaw]

end MatroidProphet

end OAI
