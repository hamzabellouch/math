import OAI.Probability.InvariantIsing.Cavity.OffsetMinimumIncrement
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

def offsetPriorObjective {m n r₀ : ℕ}
    (μ : (N : ℕ) → Measure (SpecialOrthogonal N))
    (eig c : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N))
    (q : ℕ) (R : Finset (Spin r₀)) (hR : R.Nonempty)
    (C : Finset (Spin n)) (hC : C.Nonempty) (r : ℕ)
    (u : Fin (r₀+(q+r)*n) → ℝ) (v : Fin m → ℝ) : ℝ :=
  priorPerturbationObjective (μ (r₀+(q+r)*n))
    (restrictedZeroTreePrior (offsetBlockConstraint (q+r) R C)
      (offsetBlockConstraint_nonempty R hR C hC))
    (eig (r₀+(q+r)*n)) (c (r₀+(q+r)*n)) (I (r₀+(q+r)*n)) 1 (fun _ => 0) u v

def offsetPriorIncrement {m n r₀ : ℕ}
    (μ : (N : ℕ) → Measure (SpecialOrthogonal N))
    (eig c : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N))
    (q : ℕ) (R : Finset (Spin r₀)) (hR : R.Nonempty)
    (C : Finset (Spin n)) (hC : C.Nonempty)
    (u : (r : ℕ) → Fin (r₀+(q+r)*n) → ℝ) (v : ℕ → Fin m → ℝ) (r : ℕ) : ℝ :=
  let N := r₀+(q+r)*n
  ((N+n : ℕ) : ℝ)*priorPerturbationPressureMean (μ (N+n))
    (restrictedZeroTreePrior (cavityProductSlice (offsetBlockConstraint (q+r) R C) C)
      (cavityProductSlice_nonempty _ (offsetBlockConstraint_nonempty R hR C hC) C hC))
    (eig (N+n)) (c (N+n)) (I (N+n)) 1 (fun _ => 0)
    (fun i => cavityBaseAmplitude (u r) i) (v r) -
  (N : ℝ)*priorPerturbationPressureMean (μ N)
    (restrictedZeroTreePrior (offsetBlockConstraint (q+r) R C)
      (offsetBlockConstraint_nonempty R hR C hC))
    (eig N) (c N) (I N) 1 (fun _ => 0) (u r) (v r)

theorem offset_envelope_pressure_lower
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {m n q r₀ : ℕ} (hn : 0 < n) (hq : 3 ≤ r₀+q*n)
    (μ : (N : ℕ) → Measure (SpecialOrthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    (hμ : ∀ N, 3 ≤ N → (μ N).IsMulLeftInvariant)
    (eig c : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N))
    (R : Finset (Spin r₀)) (hR : R.Nonempty)
    (C : Finset (Spin n)) (hC : C.Nonempty)
    (u : (r : ℕ) → Fin (r₀+(q+r)*n) → ℝ) (v : ℕ → Fin m → ℝ)
    (hu : ∀ r i, u r i ∈ Set.Icc (1 : ℝ) 2) (hv : ∀ r a, v r a ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ r u' v', (∀ i, u' i ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      offsetPriorObjective μ eig c I q R hR C hC r (u r) (v r) ≤
        offsetPriorObjective μ eig c I q R hR C hC r u' v')
    (L : ℝ)
    (hlower : ∀ ε > 0, ∀ᶠ r in atTop, L-ε ≤
      (offsetPriorIncrement μ eig c I q R hR C hC u v r +
        (Real.log C.card-n*Real.log 2))/(n : ℝ)) :
    ∀ ε > 0, ∀ᶠ r in atTop, L-ε ≤
      ∫ U, restrictedRotatedPressure (offsetBlockConstraint (q+r) R C)
        (eig (r₀+(q+r)*n)) (specialRotation U) (c (r₀+(q+r)*n)) ∂μ (r₀+(q+r)*n) := by
  let N := fun r => r₀+(q+r)*n
  have hN r : 3 ≤ N r := hq.trans (Nat.add_le_add_left (Nat.mul_le_mul_right n (Nat.le_add_right q r)) r₀)
  have hNlim : Tendsto N atTop atTop := by
    apply tendsto_atTop_mono (fun r => ?_) tendsto_id
    dsimp only [N]
    exact ((Nat.le_add_left r q).trans (Nat.le_mul_of_pos_right (q+r) hn)).trans (Nat.le_add_left _ r₀)
  let O := fun r => offsetPriorObjective μ eig c I q R hR C hC r (u r) (v r)
  let mass := fun r => Real.log (offsetBlockConstraint (q+r) R C).card-(N r : ℝ)*Real.log 2
  let A := fun r => -(N r : ℝ)*O r+mass r
  let P := fun r => ∫ U, restrictedRotatedPressure (offsetBlockConstraint (q+r) R C)
    (eig (N r)) (specialRotation U) (c (N r)) ∂μ (N r)
  let Δ := fun r => offsetPriorIncrement μ eig c I q R hR C hC u v r +
    (Real.log C.card-n*Real.log 2)
  let p := fun r => tensorMinimumPenalty (u r) (v r)
  let E := fun r => (n : ℝ)*p r+((N r+n : ℕ) : ℝ)*(1/4:ℝ)*(1/2:ℝ)^(N r)
  have hcost := restricted_zero_field_minimum_tendsto hhaar hgauss N hN hNlim m
    (fun r => μ (N r)) (fun r => hμ (N r) (hN r))
    (fun r => offsetBlockConstraint (q+r) R C)
    (fun _ => offsetBlockConstraint_nonempty R hR C hC)
    (fun r => eig (N r)) (fun r => c (N r)) (fun r => I (N r)) (fun _ => 1)
    u v hu hv hmin
  have hclose : Tendsto (fun r => A r/((r₀+q*n : ℕ)+(n : ℝ)*r)-P r) atTop (𝓝 0) := by
    have hz := hcost.1
    simp only [one_mul] at hz
    convert hz using 1
    funext r
    have hnz : (N r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hN r; omega)
    have hNr : ((r₀+q*n : ℕ) : ℝ)+(n : ℝ)*r=(N r : ℝ) := by
      simp only [N, Nat.cast_mul, Nat.cast_add]
      ring
    rw [hNr]
    dsimp only [A, O, P, mass, offsetPriorObjective]
    apply congrArg (fun x : ℝ => x - ∫ U, restrictedRotatedPressure
      (offsetBlockConstraint (q+r) R C) (eig (N r)) (specialRotation U) (c (N r)) ∂μ (N r))
    apply (div_eq_iff hnz).mpr
    field_simp
    rfl
  have hE : Tendsto E atTop (𝓝 0) := by
    simpa only [E, Nat.cast_add] using cavity_total_minimum_penalty_tendsto N hNlim n p hcost.2
  have hinc r : Δ r-(n : ℝ)*(E r/(n : ℝ)) ≤ A (r+1)-A r := by
    have hi := offset_minimum_increment μ eig c I R hR C hC (u r) (v r)
      (u (r+1)) (v (r+1)) (hu r) (hv r) (hmin (r+1))
    change -(N (r+1) : ℝ)*O (r+1)+(N r : ℝ)*O r ≥
      offsetPriorIncrement μ eig c I q R hR C hC u v r -
        (n : ℝ)*p r-((N r+n : ℕ) : ℝ)*(1/4:ℝ)*(1/2:ℝ)^(N r) at hi
    have hmass : mass (r+1)-mass r=Real.log C.card-n*Real.log 2 := by
      dsimp only [mass, N]
      rw [offsetBlockConstraint_log_mass R hR C hC, offsetBlockConstraint_log_mass R hR C hC]
      push_cast
      ring
    dsimp only [Δ, E, A]
    rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn.ne')]
    linarith

  exact cavity_envelope_progression_lower A P Δ (fun r => E r/(n : ℝ)) ((r₀+q*n : ℕ) : ℝ) n L
    (by exact_mod_cast (show 0 < r₀+q*n by omega)) (by exact_mod_cast hn) hclose
    (by simpa only [zero_div] using hE.div_const (n : ℝ)) hinc hlower

end InvariantIsing

end

end OAI
