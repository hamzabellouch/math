import OAI.NumberTheory.JointDickman.Amplification.PublishedRampProfile
import OAI.NumberTheory.JointDickman.Amplification.ReindexedCells
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeChannelMarginal

namespace OAI

/-! # The logarithmic coarse channel bound from published inputs -/

namespace JointDickman

open Filter Finset
open scoped Topology NNReal

noncomputable def coarseChannelError (A C T M L θ : ℝ) (B : ℕ) (δ mesh mass : ℝ) : ℝ :=
  let E := C * (B : ℝ) ^ (-(80 : ℝ))
  let κ := 9 / (8 * (auxiliaryCutoff B : ℝ))
  let η := E / δ + L * δ
  8 * (T * (2 * θ + 1 / auxiliaryRatio B) ^ (1 / 4 : ℝ)) * (A + (E + κ) / δ) +
    4 * (2 * M * η + η ^ 2 + κ / (δ * δ) + 2 * M * L * mesh) * mass

open Classical in
theorem primeLogCoarse_from_published
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ A C T : ℝ, 0 ≤ A ∧ 0 < C ∧ 0 < T ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 8 → ∃ M L : ℝ≥0, ∀ᶠ B : ℕ in atTop,
      ∀ (D R : Type*) [Fintype D] [Fintype R] [Nonempty R] [DecidableEq D] [DecidableEq R],
      ∀ lower upper : D × R → ℝ,
      (∀ a b s, s ∈ Set.Ioc (lower a) (upper a) → s ∈ Set.Ioc (lower b) (upper b) → a = b) →
      (∀ a, 1 / 2 ≤ lower a) → (∀ a, upper a ≤ 16 / 5) →
      ∀ δ mesh : ℝ, 0 < δ → 0 ≤ mesh → (∀ a, upper a - lower a = δ) →
      (∀ d r s, |lower (d, r) - lower (d, s)| ≤ mesh) →
      ∀ f : (auxiliaryPrimes B → Bool) → ℝ,
      let U := finiteChannel (fullPrimeMass (auxiliaryPrimes B)) (fun _ => δ)
        (partialFairPrimeTransition (auxiliaryPrimes B) (logarithmicCell B lower upper)) f
      (∑ a : D × R, δ * (U a - finiteResidueAverage (fun r => U (a.1, r))) ^ 2) ≤
        coarseChannelError A C T M L θ B δ mesh (∑ _a : D × R, δ) *
          ∑ x, fullPrimeMass (auxiliaryPrimes B) x * f x ^ 2 := by
  obtain ⟨v, _, H, C₀, hC₀, hprofile⟩ := primeRampProfile_from_published hSD hSW hM hMP
  obtain ⟨A₁, C₁, hA₁, hC₁, hcommon⟩ := primeCommonLogCell_upper hSD hSW hM hMP
  obtain ⟨A₂, C₂, hA₂, hC₂, hmarginal⟩ := primeChannelMarginal_upper hSD hSW hM hMP
  obtain ⟨T, hT, htail⟩ := quarterPrimeMass_small_log_tail hM
  let A := A₁ + A₂
  let C := C₀ + C₁ + C₂
  have hA : 0 ≤ A := add_nonneg hA₁ hA₂
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨A, C, T, hA, hC, hT, ?_⟩
  intro θ hθ hθmax
  obtain ⟨M, L, hprof⟩ := hprofile θ (2 * θ) hθ (by linarith)
  refine ⟨M, L, ?_⟩
  filter_upwards [hprof, hcommon, hmarginal, htail, eventually_ge_atTop 2]
    with B hprofB hcommonB hmarginalB htailB hB
  intro D R _ _ _ _ _ lower upper hdisjoint hlower hupper δ mesh hδ hmesh hwidth hdiam f
  let E := C * (B : ℝ) ^ (-(80 : ℝ))
  let κ := 9 / (8 * (auxiliaryCutoff B : ℝ))
  let A₀ := A + (E + κ) / δ
  let η := E / δ + (L : ℝ) * δ
  let low := lowPrimeLog (auxiliaryPrimes B) B (2 * θ)
  let weight (e : auxiliaryPrimes B → Bool) :=
    averagingRamp θ (2 * θ) (Real.log (retainedPrimeProduct (auxiliaryPrimes B) e) / B)
  let profile (c : auxiliaryPrimes B → Bool) (x : ℝ) :=
    rampDensity (scaledRoughDensity v (1 / 4) H B) θ (2 * θ)
      (x - Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B)
  have horder (a : D × R) : lower a < upper a := by linarith [hwidth a]
  have hq : ((1 : ℕ) : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) := by
    simpa only [Nat.cast_one] using
      (Real.one_le_rpow (by exact_mod_cast (show 1 ≤ B by omega)) (by norm_num : (0 : ℝ) ≤ 100))
  have hE : 0 ≤ E := mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg B) _)
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  have hA₀ : 0 ≤ A₀ := add_nonneg hA (div_nonneg (add_nonneg hE hκ) hδ.le)
  have hη : 0 ≤ η := add_nonneg (div_nonneg hE hδ.le) (mul_nonneg L.coe_nonneg hδ.le)
  have hAmul : A₀ * δ = A * δ + E + κ := by dsimp [A₀]; field_simp; ring
  have hN : auxiliaryCutoff B ≠ 0 := pow_ne_zero _ (by omega)
  have hcut : ∀ p ∈ auxiliaryPrimes B, auxiliaryCutoff B < p := by
    intro p hp
    exact_mod_cast (mem_filter.mp hp).2
  have hweight (e) : 0 ≤ weight e ∧ weight e ≤ 1 := averagingRamp_bounds (by linarith) _
  have hhigh (e) (he : ¬low e) : weight e = 1 := by
    apply averagingRamp_one (by linarith)
    exact le_of_lt (lt_of_not_ge he)
  have hmar : ∀ a : D × R,
      independentCellMarginal (quarterPrimeMass (auxiliaryPrimes B)) (quarterPrimeMass (auxiliaryPrimes B))
        (primeProductCell (auxiliaryPrimes B) (logarithmicCell B lower upper)) a ≤ A₀ * δ := by
    intro a
    rw [logarithmicCell_marginal]
    have hb := hmarginalB (D × R) 1 hq lower upper hdisjoint
      (fun a => by linarith [hlower a]) (fun a => (horder a).le) hupper a 1
    simp only [Nat.totient_one, Nat.cast_one, div_one, hwidth] at hb
    have hAC : A₂ * δ ≤ A * δ := mul_le_mul_of_nonneg_right (by dsimp [A]; linarith) hδ.le
    have hEC : C₂ * (B : ℝ) ^ (-(80 : ℝ)) ≤ E :=
      mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (Real.rpow_nonneg (Nat.cast_nonneg B) _)
    rw [hAmul]
    linarith
  have hcom : ∀ e, low e → ∀ a : D × R,
      optionCellMass (quarterPrimeMass (auxiliaryPrimes B))
        (fun c => primeProductCell (auxiliaryPrimes B) (logarithmicCell B lower upper) c e) a ≤ A₀ * δ := by
    intro e he a
    have he' : lowPrimeLog (auxiliaryPrimes B) B (1 / 4) e := by
      exact le_trans he (by linarith)
    have hcomm : (fun c => primeProductCell (auxiliaryPrimes B) (logarithmicCell B lower upper) c e) =
        primeProductCell (auxiliaryPrimes B) (logarithmicCell B lower upper) e := by
      funext c
      simp only [primeProductCell, Nat.mul_comm]
    rw [hcomm, logarithmicCell_primeProduct_mass]
    have hb := hcommonB (D × R) 1 hq lower upper hdisjoint hlower
      (fun a => (horder a).le) hupper e he' a 1
    have hcomm' : (fun c => primeProductCell (auxiliaryPrimes B) (logResidueCell B 1 lower upper) c e) =
        primeProductCell (auxiliaryPrimes B) (logResidueCell B 1 lower upper) e := by
      funext c
      simp only [primeProductCell, Nat.mul_comm]
    rw [hcomm'] at hb
    simp only [Nat.totient_one, Nat.cast_one, div_one, hwidth] at hb
    have hAC : A₁ * δ ≤ A * δ := mul_le_mul_of_nonneg_right (by dsimp [A]; linarith) hδ.le
    have hEC : C₁ * (B : ℝ) ^ (-(80 : ℝ)) ≤ E :=
      mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (Real.rpow_nonneg (Nat.cast_nonneg B) _)
    rw [hAmul]
    linarith
  have hloc : ∀ c a,
      |optionCellMass (fun e => quarterPrimeMass (auxiliaryPrimes B) e * weight e)
          (primeProductCell (auxiliaryPrimes B) (logarithmicCell B lower upper) c) a / δ -
        profile c (lower a)| ≤ η := by
    intro c a
    rw [logarithmicCell_primeProduct_mass]
    have hb := hprofB.2.2 (D × R) 1 hq lower upper hdisjoint horder hupper c a 1
    have hEC : C₀ * (B : ℝ) ^ (-(80 : ℝ)) ≤ E :=
      mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (Real.rpow_nonneg (Nat.cast_nonneg B) _)
    have hh := primeRampCell_normalized_error (by norm_num : (0 : ℝ) < Nat.totient 1)
      hprofB.2.1 c a 1 (horder a) (hb.trans hEC)
    simpa only [primeRampCell, weight, profile, Nat.totient_one, Nat.cast_one, div_one, hwidth] using hh
  have hplip (c) : LipschitzWith L (profile c) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := hprofB.2.1.dist_le_mul
      (x - Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B)
      (y - Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B)
    simpa only [Real.dist_eq, sub_sub_sub_cancel_right, profile] using h
  have hout := partialFairPrimeWeightedCoarse_square_bound (auxiliaryPrimes B)
    (auxiliaryPrimes_prime B) hN hcut (logarithmicCell B lower upper) weight low hweight hhigh
    profile lower hδ hA₀ M.coe_nonneg hη hmesh (fun c x => hprofB.1 _) hplip hdiam hmar hcom hloc f
  have hσ : lowExclusiveProbability (quarterPrimeMass (auxiliaryPrimes B)) low ≤
      T * (2 * θ + 1 / auxiliaryRatio B) ^ (1 / 4 : ℝ) :=
    htailB (2 * θ) (by positivity) (by linarith)
  have hin : 0 ≤ ∑ x, fullPrimeMass (auxiliaryPrimes B) x * f x ^ 2 :=
    sum_nonneg (fun x _ => mul_nonneg (fullPrimeMass_nonneg _ (auxiliaryPrimes_prime B) x) (sq_nonneg _))
  refine hout.trans (mul_le_mul_of_nonneg_right ?_ hin)
  exact add_le_add (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hσ (by norm_num : (0 : ℝ) ≤ 8)) hA₀) le_rfl

end JointDickman

end OAI
