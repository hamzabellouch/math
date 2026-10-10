import OAI.Probability.InvariantIsing.Cavity.ConsecutiveMinimumIncrement
import OAI.Probability.InvariantIsing.Magnetic.RestrictedMinimumPressure
import OAI.Probability.InvariantIsing.Cavity.CavityEnvelopeTelescoping
import OAI.Probability.InvariantIsing.Cavity.CavityPenaltyRate

namespace OAI

/-! Telescoping the actual minimum envelope for a repeated constrained
block gives its unperturbed pressure lower bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology
namespace InvariantIsing

def consecutivePriorObjective {m n : ℕ}
    (μ : (N : ℕ) → Measure (SpecialOrthogonal N))
    (eig c : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N))
    (q : ℕ) (C : Finset (Spin n)) (hC : C.Nonempty) (r : ℕ)
    (u : Fin ((q+r)*n) → ℝ) (v : Fin m → ℝ) : ℝ :=
  priorPerturbationObjective (μ ((q+r)*n))
    (restrictedZeroTreePrior (consecutiveBlockConstraint n (q+r) C)
      (consecutiveBlockConstraint_nonempty C hC))
    (eig ((q+r)*n)) (c ((q+r)*n)) (I ((q+r)*n)) 1 (fun _ => 0) u v

def consecutivePriorIncrement {m n : ℕ}
    (μ : (N : ℕ) → Measure (SpecialOrthogonal N))
    (eig c : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N))
    (q : ℕ) (C : Finset (Spin n)) (hC : C.Nonempty)
    (u : (r : ℕ) → Fin ((q+r)*n) → ℝ) (v : ℕ → Fin m → ℝ) (r : ℕ) : ℝ :=
  let N := (q+r)*n
  ((N+n : ℕ) : ℝ)*priorPerturbationPressureMean (μ (N+n))
    (restrictedZeroTreePrior (cavityProductSlice (consecutiveBlockConstraint n (q+r) C) C)
      (cavityProductSlice_nonempty _ (consecutiveBlockConstraint_nonempty C hC) C hC))
    (eig (N+n)) (c (N+n)) (I (N+n)) 1 (fun _ => 0)
    (fun i => cavityBaseAmplitude (u r) i) (v r) -
  (N : ℝ)*priorPerturbationPressureMean (μ N)
    (restrictedZeroTreePrior (consecutiveBlockConstraint n (q+r) C)
      (consecutiveBlockConstraint_nonempty C hC))
    (eig N) (c N) (I N) 1 (fun _ => 0) (u r) (v r)

theorem consecutive_envelope_pressure_lower
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {m n q : ℕ} (hn : 0 < n) (hq : 3 ≤ q*n)
    (μ : (N : ℕ) → Measure (SpecialOrthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    (hμ : ∀ N, 3 ≤ N → (μ N).IsMulLeftInvariant)
    (eig c : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N))
    (C : Finset (Spin n)) (hC : C.Nonempty)
    (u : (r : ℕ) → Fin ((q+r)*n) → ℝ) (v : ℕ → Fin m → ℝ)
    (hu : ∀ r i, u r i ∈ Set.Icc (1 : ℝ) 2) (hv : ∀ r a, v r a ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ r u' v', (∀ i, u' i ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      consecutivePriorObjective μ eig c I q C hC r (u r) (v r) ≤
        consecutivePriorObjective μ eig c I q C hC r u' v')
    (L : ℝ)
    (hlower : ∀ ε > 0, ∀ᶠ r in atTop, L-ε ≤
      (consecutivePriorIncrement μ eig c I q C hC u v r +
        (Real.log C.card-n*Real.log 2))/(n : ℝ)) :
    ∀ ε > 0, ∀ᶠ r in atTop, L-ε ≤
      ∫ U, restrictedRotatedPressure (consecutiveBlockConstraint n (q+r) C)
        (eig ((q+r)*n)) (specialRotation U) (c ((q+r)*n)) ∂μ ((q+r)*n) := by
  let N := fun r => (q+r)*n
  have hN r : 3 ≤ N r := hq.trans (Nat.mul_le_mul_right n (Nat.le_add_right q r))
  have hNlim : Tendsto N atTop atTop := by
    apply tendsto_atTop_mono (fun r => ?_) tendsto_id
    dsimp only [N]
    exact (Nat.le_add_left r q).trans (Nat.le_mul_of_pos_right (q+r) hn)
  let O := fun r => consecutivePriorObjective μ eig c I q C hC r (u r) (v r)
  let mass := fun r => Real.log (consecutiveBlockConstraint n (q+r) C).card-(N r : ℝ)*Real.log 2
  let A := fun r => -(N r : ℝ)*O r+mass r
  let P := fun r => ∫ U, restrictedRotatedPressure (consecutiveBlockConstraint n (q+r) C)
    (eig (N r)) (specialRotation U) (c (N r)) ∂μ (N r)
  let Δ := fun r => consecutivePriorIncrement μ eig c I q C hC u v r +
    (Real.log C.card-n*Real.log 2)
  let p := fun r => tensorMinimumPenalty (u r) (v r)
  let E := fun r => (n : ℝ)*p r+((N r+n : ℕ) : ℝ)*(1/4:ℝ)*(1/2:ℝ)^(N r)
  have hcost := restricted_zero_field_minimum_tendsto hhaar hgauss N hN hNlim m
    (fun r => μ (N r)) (fun r => hμ (N r) (hN r))
    (fun r => consecutiveBlockConstraint n (q+r) C)
    (fun _ => consecutiveBlockConstraint_nonempty C hC)
    (fun r => eig (N r)) (fun r => c (N r)) (fun r => I (N r)) (fun _ => 1)
    u v hu hv hmin
  have hclose : Tendsto (fun r => A r/((q*n : ℕ)+(n : ℝ)*r)-P r) atTop (𝓝 0) := by
    have hz := hcost.1
    simp only [one_mul] at hz
    convert hz using 1
    funext r
    have hnz : (N r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hN r; omega)
    have hNr : ((q*n : ℕ) : ℝ)+(n : ℝ)*r=(N r : ℝ) := by
      simp only [N, Nat.cast_mul, Nat.cast_add]
      ring
    rw [hNr]
    dsimp only [A, O, P, mass, consecutivePriorObjective]
    apply congrArg (fun x : ℝ => x - ∫ U, restrictedRotatedPressure
      (consecutiveBlockConstraint n (q+r) C) (eig (N r)) (specialRotation U) (c (N r)) ∂μ (N r))
    apply (div_eq_iff hnz).mpr
    field_simp
    rfl
  have hE : Tendsto E atTop (𝓝 0) := by
    simpa only [E, Nat.cast_add] using cavity_total_minimum_penalty_tendsto N hNlim n p hcost.2
  have hinc r : Δ r-(n : ℝ)*(E r/(n : ℝ)) ≤ A (r+1)-A r := by
    have hi := consecutive_minimum_increment μ eig c I C hC (u r) (v r)
      (u (r+1)) (v (r+1)) (hu r) (hv r) (hmin (r+1))
    change -(N (r+1) : ℝ)*O (r+1)+(N r : ℝ)*O r ≥
      consecutivePriorIncrement μ eig c I q C hC u v r -
        (n : ℝ)*p r-((N r+n : ℕ) : ℝ)*(1/4:ℝ)*(1/2:ℝ)^(N r) at hi
    have hmass : mass (r+1)-mass r=Real.log C.card-n*Real.log 2 := by
      dsimp only [mass, N]
      rw [consecutiveBlockConstraint_log_mass C, consecutiveBlockConstraint_log_mass C]
      push_cast
      ring
    dsimp only [Δ, E, A]
    rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn.ne')]
    linarith

  exact cavity_envelope_progression_lower A P Δ (fun r => E r/(n : ℝ)) ((q*n : ℕ) : ℝ) n L
    (by exact_mod_cast (show 0 < q*n by omega)) (by exact_mod_cast hn) hclose
    (by simpa only [zero_div] using hE.div_const (n : ℝ)) hinc hlower

end InvariantIsing

end

end OAI
