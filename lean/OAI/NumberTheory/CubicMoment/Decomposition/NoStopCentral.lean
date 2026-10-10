import OAI.NumberTheory.CubicMoment.Estimates.ShortOuterLow
import OAI.NumberTheory.CubicMoment.Decomposition.NoStopSupport
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedBinMoment

namespace OAI

/-! The original no-stop branch, with its exact surrogate and product
cutoff, is controlled by the derived central Type-I estimate. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def noStopCenteredValue (R : Finset Eisenstein) (v : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w ρ Z B : ℝ) (ℓ : ℤ) (W : ℝ → ℂ)
    (H T X X₀ : ℝ) : ℂ :=
  ∑ r ∈ R, v r*∑ u ∈ primaryElementBall (B*X),
    ∑ m ∈ primaryProductSlice (squarefreeProductEnvelope (B*X)) (B*X) (r*u) with
      norm r*primeSurrogate (primaryPrimeFactors m)
        (geometricPrimeBin ρ (B*X)) (geometricBinLower ρ (B*X)) < Z,
      cutoffMoebius ψ w m*centeredHeightKernel ℓ W H T X X₀ (r*(m*u))

theorem noStop_central_bound
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    (ℓ : ℤ) (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    {κ M : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M) (Ct : ℕ) :
    ∃ ρ K : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ 0 ≤ K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (i : γ) (R : Finset Eisenstein) (v : Eisenstein → ℂ)
        (ψ : ℝ → ℝ) (w Z Y H X₀ : ℝ),
        2 ≤ X → 1 ≤ Real.log X → Real.exp hW.radius ≤ X →
        1 ≤ Y → (Real.exp hW.radius*X)^(κ/4)*Z ≤ Y →
        2*Y ≤ X^(51/100:ℝ) → 0 < H →
        (∀ r ∈ R, primary r) → (∀ r ∈ R, ‖v r‖ ≤ M) →
        (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
        ‖noStopCenteredValue R v ψ w ρ Z (Real.exp hW.radius) ℓ (W i)
          H ((1+Real.log X)^Ct) X X₀‖ ≤
          K*(1+Real.log Y)*(1+Real.log X)^Ct*X^(5/6-1/100:ℝ) := by
  obtain ⟨ρ,hρ,hρ₂,hgeom⟩ := noStop_short_support hκ
  obtain ⟨K,hK,hbound⟩ := short_outer_low_bound hV hW ℓ hGamma hM 1 Ct
  refine ⟨ρ,K,hρ,hρ₂,hK,?_⟩
  have hcomp : Tendsto (fun X : ℝ => Real.exp hW.radius*X) atTop atTop :=
    tendsto_id.const_mul_atTop (Real.exp_pos _)
  filter_upwards [hcomp.eventually hgeom] with X hgeomX
  intro i R v ψ w Z Y H X₀ hX hlog hBX hY hdist hYX hH hR hv hψ
  let F := Real.exp hW.radius*X
  let D := primaryElementBall F
  let P := primaryPairSupport R D
  let α := noStopCoefficient R D v ψ w ρ F Z
  have hP (b : Eisenstein) (hb : b ∈ P) : primary b :=
    primaryPairSupport_primary R D hR (fun m hm => (mem_primaryElementBall.mp hm).1) hb
  have hs (b : Eisenstein) (_hb : b ∈ P) (hne : α b ≠ 0) : norm b ≤ Y :=
    (hgeomX R v ψ w Z b hne).le.trans hdist
  have ha (b : Eisenstein) (hb : b ∈ P) :
      ‖α b‖ ≤ M*((metaplecticPrimaryDivisors b).card:ℝ)^1 := by
    simpa only [pow_one] using noStop_coefficient_divisor_bound R D hR hψ w ρ F Z v hM hv (hP b hb)
  have hb := hbound (fun _ => i) P α X Y H X₀ hX hlog hBX hY hYX hH hP hs ha
  have he := noStop_coefficient_collection (squarefreeProductEnvelope F) R v ψ w ρ F Z
    (centeredHeightKernel ℓ (W i) H ((1+Real.log X)^Ct) X X₀)
  change ‖noStopCenteredValue R v ψ w ρ Z (Real.exp hW.radius) ℓ (W i)
    H ((1+Real.log X)^Ct) X X₀‖ ≤ _
  change ‖∑ r ∈ R, v r*∑ u ∈ D,
    ∑ m ∈ primaryProductSlice (squarefreeProductEnvelope F) F (r*u) with
      norm r*primeSurrogate (primaryPrimeFactors m) (geometricPrimeBin ρ F)
        (geometricBinLower ρ F) < Z,
      cutoffMoebius ψ w m*centeredHeightKernel ℓ (W i) H ((1+Real.log X)^Ct) X X₀ (r*(m*u))‖ ≤ _
  rw [he]
  exact hb

end CubicFirstMoment

end

end OAI
