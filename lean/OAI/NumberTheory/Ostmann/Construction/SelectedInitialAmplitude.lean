import OAI.NumberTheory.Ostmann.Construction.SelectedInitialPriorBounds
import OAI.NumberTheory.Ostmann.Construction.SelectedInitialWindowRate
import OAI.NumberTheory.Ostmann.Construction.InitialPrimeWindow
import OAI.NumberTheory.Ostmann.Arithmetic.MovingProductPoissonCutoff
import OAI.NumberTheory.Ostmann.Construction.UniformSupportedInitialAmplitude

namespace OAI

/-! # The original initial amplitude for the selected mixed priors -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem eventual_selected_initial_amplitude
    (k : ℕ) (hk : 2 ≤ k) (Bs BD Bz a C atail c δ H : ℝ)
    (hBs : 0 ≤ Bs) (hH : 0 ≤ H) (hatail : 0 < atail) (hc : 0 < c) (hδ : 0 < δ)
    (hgap : 2 * ((4 - 2 * Real.log (1 / 320000)) + 2 + 2 * Real.log 4 +
      (4 * (Real.log 2 + 2) + 2 * Real.log 2 + 4) + 3) ≤ Bs - 1)
    (hklarge : 14 * (64 * tailCellLinearRate a C + 3) ≤ (k : ℝ) ^ 3)
    (ψ : 𝓢(ℝ, ℂ)) (hψ : ∀ x, 0 ≤ (ψ x).re)
    (hsupp : ∀ t : ℝ, H < |t| → 𝓕 ψ t = 0) :
    ∀ᶠ L : ℝ in atTop, ∀ {A B : Set ℕ} {N hi top : ℕ}
      {Y G cb cd : ℝ} {D Qb Qd : Finset ℕ} {centers : List ℕ},
      0 < Y → Y ≤ Real.exp L →
      SelectedSmallTailCell A B N a C L Y hi D
        ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top →
      List.Forall₂ (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j)
        centers (movingCompensationTargets
          (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
          (movingCompensationGaps k BD Bz L)) → centers.length = k →
      ∀ (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)], (∀ p ∈ P, p.Prime) →
      initialRegularPrimeRange L ⊆ P → smoothGiantPrimeRange G ⊆ P →
      0 < smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G →
      smoothGiantLogNormalizer (smoothGiantPrimeRange G) logCellProfile G ≤ (91 / 100) * L →
      (∑ p : P, primeSubsetPrior P Qb p) = 1 →
      (∑ p : P, primeSubsetPrior P Qd p) = 1 →
      (∀ p : P, (p : ℝ) * primeSubsetPrior P Qb p ≤ (L / 320000)⁻¹ ∧
        (p : ℝ) * primeSubsetPrior P Qd p ≤ (L / 320000)⁻¹) →
      let m := spectatorBulkCount k L
      let cells := initialSmallCellList top centers
      let ν := selectedInitialHalfPrior P A B N hi Y G D Qb Qd (m / 2) (m / 2) top centers
      let w := initialHalfCutoffWeight (fun p : P => (p : ℕ)) (m / 2) (m / 2) cells.length cb cd
      let good := fun p : P => (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
        residueDensity (tailDensityMask A N p) ≤ 2 / 3
      Real.exp (-(2 * (Real.log 2 + 2)) * m) ≤
        ∑ x ∈ balancedTupleSet (m / 2 + (m / 2 + cells.length)) (fun _ p => good p),
          productPrior (Fin.tail ν) x * w x →
      (∀ i (p : P), ν i p ≠ 0 → Real.exp (Real.exp ((4 / 10000 : ℝ) * L)) ≤ (p : ℝ)) →
      (∑ p : P, (p : ℝ)⁻¹) ≤ 2 * m →
      ∀ (E : Finset ℤ) (favorable : P → Bool),
      atail * Real.sqrt (Real.exp Y) / Y ^ 3 ≤ (E.card : ℝ) →
      (∀ e ∈ E, c ≤ (ψ ((e : ℝ) / Real.exp Y)).re) →
      (∀ e ∈ E, ∀ p : P, (e : ZMod (p : ℕ)) ∈ tailDensityMask A N p) →
      (E.card : ℝ) * δ ≤ ∑ e ∈ E,
        (∑ p : P, (smoothGiantPrior P logCellProfile G p : ℂ) *
          primePhysicalTest (tailDensityMask A N p) true (favorable p)
            (e : ZMod (p : ℕ))).re →
      ∀ T : ℕ → ℝ,
      let Δ := selectedInitialLogCenter G Y cb cd top centers
      let width : ℝ := 2 * (cells.length + 3)
      let V := movingProductNaturalCutoff T (Y + Δ + width) Y ((m : ℝ) / 4) 0
      let F : Fin ((m / 2 + (m / 2 + cells.length)) + 1) →
        (p : P) → ZMod (p : ℕ) → ℂ := primeHalfTests P (fun p => tailDensityMask A N p) favorable
      Real.exp (-(6 * Real.log 2 + 13) * m) ≤
        ‖regularInitialAmplitude P (Fin.append ν ν) (Fin.append F F) ψ (Real.exp Y) V
          (doubledHalfWeight (fun y => (w (Fin.tail y) : ℂ)))‖ := by
  classical
  have hz : 1 ≤ (k : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ k by omega))
  have hrate : 0 ≤ Bs + 1 + 8 * Real.log ((k : ℝ) ^ 4) := by
    have := Real.log_nonneg hz
    linarith
  obtain ⟨M, hM⟩ := eventually_atTop.mp (uniform_supported_initial_amplitude
    (3 + 2 * k) ((k : ℝ) ^ 4) (4 - 2 * Real.log (1 / 320000)) 2 (Bs - 1)
    atail c δ hz hatail hc hδ hgap ψ H hψ hsupp)
  filter_upwards [(spectatorBulkCount_tendsto k (by omega)).eventually
      (eventually_ge_atTop (M : ℝ)),
    eventual_linear_product_prime_window H (Bs + 1 + 8 * Real.log ((k : ℝ) ^ 4))
      ((k : ℝ) ^ 4) (4 / 10000) hrate (by norm_num),
    eventual_spectator_product_poisson_cutoff k (by omega) H hH,
    eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (4 / (k : ℝ) ^ 4)]
    with L hm0 hprime hpoisson hL hscale
  intro A B N hi top Y G cb cd D Qb Qd centers hY hYhi htop hcenters hlen
    P _ hP hsmall hgiant hmass hnorm hb hd hpoint m cells ν w good hbalanced
    hlive htotal E favorable hE hcE hendpoint hmean T Δ width V F
  have hscale' : 4 ≤ (k : ℝ) ^ 4 * L := by
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < (k : ℝ) ^ 4)).mp hscale
  have hmupper : (m : ℝ) ≤ (k : ℝ) ^ 4 * L := spectatorBulkCount_upper k L (by linarith)
  have hmlower : L ≤ (m : ℝ) := by
    have h := spectatorBulkCount_half k L hscale'
    have hk4 : (2 : ℝ) ≤ (k : ℝ) ^ 4 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
        (show (2 : ℝ) ≤ k by exact_mod_cast hk) 4
      norm_num at hh
      linarith
    nlinarith only [h, mul_le_mul_of_nonneg_right hk4 (by linarith : 0 ≤ L)]
  have hdata := selected_initial_prior_bounds (a₀ := 1 / 320000) htop hcenters P hP hsmall hgiant hmass hnorm
    hb hd (by simpa only [div_eq_mul_inv, mul_comm, one_mul] using hpoint) (m / 2) (m / 2)
  have hwindow := selected_initial_window_rate k hk hL (tailCellLinearRate_nonneg a C)
    (tailDefectBudget_linear a C L Y hL hY hYhi) hklarge hscale' htop hcenters hlen
  have hnormcost := selected_initial_normalizer_rate k hk L (by linarith) hscale' top centers hlen
  have hlen' : cells.length = 3 + 2 * k := by
    dsimp only [cells]
    rw [initialSmallCellList_length, hlen]
  have heven : m / 2 + m / 2 = m := by
    obtain ⟨t, ht⟩ := spectatorBulkCount_even k L
    dsimp only [m]
    omega
  have heq : m + (3 + 2 * k) = m / 2 + (m / 2 + cells.length) := by omega
  have hh := hM m (by exact_mod_cast hm0)
  rw [heq] at hh
  have hwidth : 0 ≤ width := by dsimp only [width]; positivity
  have hlow : 0 ≤ Δ - width := by
    have hg : 0 ≤ Bs - 1 + 8 * Real.log ((k : ℝ) ^ 4) := by
      have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      have hla : Real.log (1 / 320000 : ℝ) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
      linarith [Real.log_nonneg hz]
    exact (mul_nonneg hg (Nat.cast_nonneg _)).trans hwindow.1
  have hpoisson' : H * Real.exp (Δ + width) ≤ V := by
    have hw : Y ≤ Y + Δ + width := by linarith
    have hh := hpoisson T (Y + Δ + width) Y hw
    have he : Y + Δ + width - Y = Δ + width := by ring
    simpa only [he] using hh
  apply hh L Y (Real.exp Y) (Δ - width) (Real.exp (Δ + width))
    (by linarith) hmlower hmupper hY hYhi (Real.exp_pos _) (Real.exp_pos _) hwindow.1
    P hP (fun p => tailDensityMask A N p) favorable ν
    (initialHalfNormalizer (m / 2) (m / 2) cells.length (1 / 320000) L (91 / 100))
    hdata.1 (initialHalfNormalizer_nonneg _ _ _ _ _ _ (by norm_num) (by linarith)) hdata.2.2
    hnormcost htotal w E
    (balancedTupleSet (m / 2 + (m / 2 + cells.length)) (fun _ p => good p))
    (initialHalfCutoffWeight_nonneg _ _ _ _ _ _) (initialHalfCutoffWeight_le_one _ _ _ _ _ _)
    hbalanced (by
      intro x hx i
      have hx' : ∀ j, good (x j) := by
        simpa only [balancedTupleSet, Finset.mem_filter, Finset.mem_univ, true_and] using hx
      exact hx' i) hE hcE hendpoint hmean
    (fun i p hp => hprime m hmupper (Δ + width) hwindow.2 p (hlive i p hp)) V
  all_goals
    intro x hx hw
    have hprod := selected_initial_product_window htop hcenters P hP (m / 2) (m / 2)
      (fun _ => primeSubsetPrior P Qb) (fun _ => primeSubsetPrior P Qd) x hx hw
  · exact sampled_product_poisson_cutoff (fun i => (x i : ℕ)) (Real.exp Y) H
      (Real.exp (Δ + width)) V (Real.exp_nonneg _) hH hprod.2 hpoisson'
  · exact hprod.1
  · exact hprod.2

end Ostmann

end OAI
