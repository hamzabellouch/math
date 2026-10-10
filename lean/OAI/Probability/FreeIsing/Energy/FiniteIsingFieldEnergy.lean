import OAI.Probability.FreeIsing.Gaussian.FiniteIsingGaussianEnergy
import OAI.Probability.FreeIsing.Stochastic.FiniteFieldEntropyIntegral
import OAI.Probability.FreeIsing.Trees.GibbsField

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace Problem367

local instance finiteIsingFieldEnergyNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

theorem finiteIsingEntropy_le_own_observation {d : ℕ} {beta : ℝ}
    (hbeta : 0 ≤ beta) (D : Finset (TreeVertex d)) (v : D) (y : D → ℝ) :
    FinitePosterior.fieldEntropy (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) w => spinSign (eta w))
      (fun eta => spinSign (eta v)) y ≤ 2 * (|y v| + (d : ℝ) * beta) := by
  classical
  have hspin : ∀ eta : D → IsingSpin, spinSign (eta v) = -1 ∨ spinSign (eta v) = 1 := by
    intro eta
    cases eta v <;> simp [spinSign]
  have hneg : ∃ eta : D → IsingSpin, spinSign (eta v) = -1 := ⟨fun _ => .neg, rfl⟩
  have hpos : ∃ eta : D → IsingSpin, spinSign (eta v) = 1 := ⟨fun _ => .pos, rfl⟩
  have hF := FinitePosterior.fieldEntropy_le_abs_field (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) w => spinSign (eta w))
    (fun eta => spinSign (eta v)) y hspin hneg hpos
  have hb := finite_tree_gibbs_field_uniform_bound D hbeta y v
  change |FinitePosterior.fieldField (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) w => spinSign (eta w))
    (fun eta => spinSign (eta v)) y - y v| ≤ (d : ℝ) * beta at hb
  have ht := norm_le_norm_sub_add (FinitePosterior.fieldField (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) w => spinSign (eta w))
    (fun eta => spinSign (eta v)) y) (y v)
  simp only [Real.norm_eq_abs] at ht
  linarith

theorem HasFreeIsingLaw.integral_finiteIsingEntropy_le_own_observation
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : Finset (TreeVertex d)) (v : D) (t : ℝ) :
    let spin : (D → IsingSpin) → D → ℝ := fun eta w => spinSign (eta w)
    let ρ := (μ.map D.restrict).prod (Measure.pi (fun _ : D => gaussianReal 0 1))
    (∫ x, FinitePosterior.fieldEntropy (finiteIsingEnergy beta D) spin
      (fun eta => spinSign (eta v)) (FinitePosterior.finiteStandardObservation spin t x) ∂ρ) ≤
      2 * ((∫ x, |FinitePosterior.finiteStandardObservation spin t x v| ∂ρ) + (d : ℝ) * beta) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let spin : (D → IsingSpin) → D → ℝ := fun eta w => spinSign (eta w)
  let ρ := (μ.map D.restrict).prod (Measure.pi (fun _ : D => gaussianReal 0 1))
  have hcoords : ∀ eta w, spin eta w = -1 ∨ spin eta w = 1 := by
    intro eta w
    change spinSign (eta w) = -1 ∨ spinSign (eta w) = 1
    cases eta w <;> simp [spinSign]
  have hobsInt : Integrable (FinitePosterior.finiteStandardObservation spin t) ρ :=
    FinitePosterior.integrable_finiteStandardObservation (μ.map D.restrict) spin hcoords t
  have hcoordInt : Integrable (fun x => |FinitePosterior.finiteStandardObservation spin t x v|) ρ :=
    (hobsInt.eval v).abs
  have hFInt : Integrable (fun x => FinitePosterior.fieldEntropy (finiteIsingEnergy beta D) spin
      (fun eta => spinSign (eta v)) (FinitePosterior.finiteStandardObservation spin t x)) ρ :=
    FinitePosterior.integrable_finiteStandardEntropy (μ.map D.restrict) (finiteIsingEnergy beta D)
      spin (fun eta => spinSign (eta v)) (fun eta => hcoords eta v)
      ⟨fun _ => .neg, rfl⟩ ⟨fun _ => .pos, rfl⟩ hcoords t
  have hb := integral_mono hFInt
    ((hcoordInt.add (integrable_const ((d : ℝ) * beta))).const_mul 2)
    (fun x => finiteIsingEntropy_le_own_observation hbeta D v
      (FinitePosterior.finiteStandardObservation spin t x))
  change (∫ x, FinitePosterior.fieldEntropy (finiteIsingEnergy beta D) spin
      (fun eta => spinSign (eta v)) (FinitePosterior.finiteStandardObservation spin t x) ∂ρ) ≤ _
  calc
    _ ≤ ∫ x, 2 * (|FinitePosterior.finiteStandardObservation spin t x v| + (d : ℝ) * beta) ∂ρ := hb
    _ = _ := by rw [integral_const_mul, integral_add hcoordInt (integrable_const _)]; simp [ρ, spin]

theorem finiteIsingEntropy_zero {d : ℕ} (beta : ℝ) (D : Finset (TreeVertex d)) (v : D) :
    FinitePosterior.fieldEntropy (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) w => spinSign (eta w))
      (fun eta => spinSign (eta v)) 0 = 0 := by
  have hz := finiteIsingPosterior_spin_zero beta D v
  change FinitePosterior.fieldMean (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) w => spinSign (eta w))
    (fun eta => spinSign (eta v)) 0 = 0 at hz
  simp [FinitePosterior.fieldEntropy, hz]

theorem HasFreeIsingLaw.integral_finiteIsingEntropyEnergy
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D)
    {T : ℝ} (hT : 0 ≤ T) :
    let spin : (D → IsingSpin) → D → ℝ := fun eta w => spinSign (eta w)
    let ρ := (μ.map D.restrict).prod (Measure.pi (fun _ : D => gaussianReal 0 1))
    let C : ℝ → ℝ := fun t => ∫ x,
      (1 + FinitePosterior.fieldMean (finiteIsingEnergy beta D) spin
        (fun eta => spinSign (eta v)) (FinitePosterior.finiteStandardObservation spin t x) ^ 2) *
        ∑ w, FinitePosterior.normalizedFieldCovariance (finiteIsingEnergy beta D) spin
          (fun eta => spinSign (eta v)) (FinitePosterior.finiteStandardObservation spin t x) w ^ 2 ∂ρ
    IntervalIntegrable C volume 0 T ∧
      (∫ t in 0..T, C t) =
        (∫ x, FinitePosterior.fieldEntropy (finiteIsingEnergy beta D) spin
          (fun eta => spinSign (eta v)) (FinitePosterior.finiteStandardObservation spin T x) ∂ρ) ∧
      0 ≤ (∫ t in 0..T, C t) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hcoords : ∀ (eta : D → IsingSpin) w, spinSign (eta w) = -1 ∨ spinSign (eta w) = 1 := by
    intro eta w
    cases eta w <;> simp [spinSign]
  have h := FinitePosterior.integral_finiteStandardEntropyEnergy
    (μ.map D.restrict) (finiteIsingEnergy beta D)
    (hμ.restrict_real_eq_normalized_exp D hD)
    (fun (eta : D → IsingSpin) w => spinSign (eta w)) (fun eta => spinSign (eta v))
    (fun eta => hcoords eta v) ⟨fun _ => .neg, rfl⟩ ⟨fun _ => .pos, rfl⟩ hcoords hT
  simpa only [finiteIsingEntropy_zero, sub_zero] using h

theorem HasFreeIsingLaw.integral_finiteIsingNormalizedEnergy_le
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D)
    {T : ℝ} (hT : 0 ≤ T) :
    let spin : (D → IsingSpin) → D → ℝ := fun eta w => spinSign (eta w)
    let ρ := (μ.map D.restrict).prod (Measure.pi (fun _ : D => gaussianReal 0 1))
    let Q : ℝ → ℝ := fun t => ∫ x, ∑ w,
      FinitePosterior.normalizedFieldCovariance (finiteIsingEnergy beta D) spin
        (fun eta => spinSign (eta v)) (FinitePosterior.finiteStandardObservation spin t x) w ^ 2 ∂ρ
    IntervalIntegrable Q volume 0 T ∧
      (∫ t in 0..T, Q t) ≤
        2 * ((∫ x, |FinitePosterior.finiteStandardObservation spin T x v| ∂ρ) + (d : ℝ) * beta) ∧
      0 ≤ (∫ t in 0..T, Q t) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hcoords : ∀ (eta : D → IsingSpin) w, spinSign (eta w) = -1 ∨ spinSign (eta w) = 1 := by
    intro eta w
    cases eta w <;> simp [spinSign]
  have h := FinitePosterior.integral_finiteStandardNormalizedEnergy_le
    (μ.map D.restrict) (finiteIsingEnergy beta D)
    (hμ.restrict_real_eq_normalized_exp D hD)
    (fun (eta : D → IsingSpin) w => spinSign (eta w)) (fun eta => spinSign (eta v))
    (fun eta => hcoords eta v) ⟨fun _ => .neg, rfl⟩ ⟨fun _ => .pos, rfl⟩ hcoords hT
  have hbound := hμ.integral_finiteIsingEntropy_le_own_observation hbeta D v T
  simp only [finiteIsingEntropy_zero, sub_zero] at h
  exact ⟨h.1, h.2.1.trans hbound, h.2.2⟩

end Problem367

end

end OAI
