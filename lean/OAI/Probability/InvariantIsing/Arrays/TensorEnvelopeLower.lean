import OAI.Probability.InvariantIsing.Arrays.TensorMinimumSequence
import OAI.Probability.InvariantIsing.Arrays.TensorMinimumIncrement
import OAI.Probability.InvariantIsing.Cavity.CavityEnvelopeTelescoping
import OAI.Probability.InvariantIsing.Cavity.CavityPenaltyRate

namespace OAI

/-! The cavity increment lower bound passes through actual minimizing
pressure envelopes to the ordinary Haar pressure on an arithmetic progression. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem tensor_envelope_pressure_lower
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (m depth N₀ n : ℕ) (hN₀ : 3≤N₀) (hn : 0<n)
    (b : ℕ → ℝ) (hb : CascadeExponents depth b)
    (μ : (N : ℕ) → Measure (SpecialOrthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    (hμ : ∀ N, (μ N).IsMulLeftInvariant)
    (eig c : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N))
    (u : (N : ℕ) → Fin N → ℝ) (v : ℕ → Fin m → ℝ)
    (hu : ∀ N j, u N j ∈ Set.Icc (1 : ℝ) 2) (hv : ∀ N a, v N a ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ N, 3≤N → ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      tensorPerturbationObjective (μ N) (eig N) (c N) (I N) 1 depth b
        (fun _ => 0) (u N) (v N) ≤
      tensorPerturbationObjective (μ N) (eig N) (c N) (I N) 1 depth b (fun _ => 0) u' v')
    (L : ℝ)
    (hlower : ∀ ε>0, ∀ᶠ r in atTop,
      let N := N₀+n*r
      L-ε ≤ ((N+n : ℝ)*tensorPerturbationPressureMean (μ (N+n)) (eig (N+n)) (c (N+n))
        (I (N+n)) (fun j => cavityBaseAmplitude (u N) j) (v N) 1 depth b (fun _ => 0) -
        (N : ℝ)*tensorPerturbationPressureMean (μ N) (eig N) (c N) (I N)
          (u N) (v N) 1 depth b (fun _ => 0))/(n : ℝ)) :
    ∀ ε>0, ∀ᶠ r in atTop, L-ε ≤
      ∫ U, rotatedPressure (eig (N₀+n*r)) (specialRotation U) (c (N₀+n*r)) ∂μ (N₀+n*r) := by
  let N := fun r => N₀+n*r
  have hN r : 3≤N r := by dsimp only [N]; omega
  have hNlim : Tendsto N atTop atTop := by
    apply tendsto_atTop_mono (fun r => ?_) tendsto_id
    dsimp only [N]
    change r≤N₀+n*r
    have : r≤n*r := Nat.le_mul_of_pos_left r hn
    omega
  let O := fun k => tensorPerturbationObjective (μ k) (eig k) (c k) (I k) 1 depth b
    (fun _ => 0) (u k) (v k)
  let A := fun r => -(N r : ℝ)*O (N r)
  let P := fun r => ∫ U, rotatedPressure (eig (N r)) (specialRotation U) (c (N r)) ∂μ (N r)
  let Δ := fun r => ((N r+n : ℝ)*tensorPerturbationPressureMean (μ (N r+n)) (eig (N r+n))
      (c (N r+n)) (I (N r+n)) (fun j => cavityBaseAmplitude (u (N r)) j) (v (N r))
      1 depth b (fun _ => 0) - (N r : ℝ)*tensorPerturbationPressureMean (μ (N r))
      (eig (N r)) (c (N r)) (I (N r)) (u (N r)) (v (N r)) 1 depth b (fun _ => 0))
  let p := fun r => tensorMinimumPenalty (u (N r)) (v (N r))
  let E := fun r => (n : ℝ)*p r+(N r+n : ℝ)*(1/4:ℝ)*(1/2:ℝ)^(N r)
  have hcost := tensor_zero_field_minimum_tendsto hhaar hgauss N hN hNlim m
    (fun r => μ (N r)) (fun r => hμ (N r)) (fun r => eig (N r)) (fun r => c (N r))
    (fun r => I (N r)) (fun _ => 1) (fun _ => depth) (fun _ => b) (fun _ => hb)
    (fun r => u (N r)) (fun r => v (N r)) (fun r => hu (N r)) (fun r => hv (N r))
    (fun r => hmin (N r) (hN r))
  have hclose : Tendsto (fun r => A r/((N₀ : ℝ)+(n : ℝ)*r)-P r) atTop (𝓝 0) := by
    have hz := hcost.1
    simp only [one_mul] at hz
    convert hz using 1
    funext r
    have hpos : (N r : ℝ)≠0 := Nat.cast_ne_zero.mpr (by have := hN r; omega)
    have hNr : (N₀ : ℝ)+(n : ℝ)*r=(N r : ℝ) := by simp only [N, Nat.cast_add, Nat.cast_mul]
    rw [hNr]
    dsimp only [A, O, P]
    apply congrArg (fun x : ℝ => x - ∫ U, rotatedPressure (eig (N r))
      (specialRotation U) (c (N r)) ∂μ (N r))
    apply (div_eq_iff hpos).mpr
    ring
  have hE : Tendsto E atTop (𝓝 0) := cavity_total_minimum_penalty_tendsto N hNlim n p hcost.2
  have hinc r : Δ r-(n : ℝ)*(E r/(n : ℝ))≤A (r+1)-A r := by
    have hh := tensor_minimum_increment (depth := depth) (μ (N r+n)) (μ (N r))
      (eig (N r+n)) (c (N r+n)) (eig (N r)) (c (N r)) (I (N r+n)) (I (N r))
      1 b (fun _ => 0) (u (N r+n)) (v (N r+n)) (u (N r)) (v (N r))
      (hu (N r)) (hv (N r)) (hmin (N r+n) (by have := hN r; omega))
    have hsucc : N (r+1)=N r+n := by simp only [N, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
    dsimp only [A]
    rw [hsucc, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn.ne')]
    dsimp only [Δ, E, p, O] at *
    simp only [Nat.cast_add] at ⊢
    linarith
  exact cavity_envelope_progression_lower A P Δ (fun r => E r/(n : ℝ)) N₀ n L
    (by exact_mod_cast (show 0<N₀ by omega)) (by exact_mod_cast hn) hclose
    (by simpa only [zero_div] using hE.div_const (n : ℝ)) hinc hlower

end InvariantIsing

end

end OAI
