import OAI.NumberTheory.CubicMoment.Estimates.ShortOuterLow
import OAI.NumberTheory.CubicMoment.Estimates.RestrictedNoStopSupport
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedBinMoment

namespace OAI

/-! The original no-stop branch, retaining an arbitrary extra predicate
on the two outer factors, obeys the derived central Type-I estimate. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def restrictedNoStopCenteredValue (R : Finset Eisenstein) (v : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w ρ Z B : ℝ) (ℓ : ℤ) (W : ℝ → ℂ)
    (H T X X₀ : ℝ) (P : Eisenstein → Eisenstein → Prop) : ℂ :=
  ∑ r ∈ R, v r*∑ u ∈ primaryElementBall (B*X),
    ∑ m ∈ primaryProductSlice (squarefreeProductEnvelope (B*X)) (B*X) (r*u) with
      norm r*primeSurrogate (primaryPrimeFactors m)
        (geometricPrimeBin ρ (B*X)) (geometricBinLower ρ (B*X)) < Z ∧ P r m,
      cutoffMoebius ψ w m*centeredHeightKernel ℓ W H T X X₀ (r*(m*u))

theorem restricted_noStop_central_bound
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    (ℓ : ℤ) (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    {κ M : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M) (Ct : ℕ) {cap : ℝ} (hcap : 1 < cap) :
    ∃ ρ K : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ρ ≤ cap ∧ 0 ≤ K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (i : γ) (R : Finset Eisenstein) (v : Eisenstein → ℂ)
        (ψ : ℝ → ℝ) (w Z Y H X₀ : ℝ) (P : Eisenstein → Eisenstein → Prop),
        2 ≤ X → 1 ≤ Real.log X → Real.exp hW.radius ≤ X →
        1 ≤ Y → (Real.exp hW.radius*X)^(κ/4)*Z ≤ Y →
        2*Y ≤ X^(51/100:ℝ) → 0 < H →
        (∀ r ∈ R, primary r) → (∀ r ∈ R, ‖v r‖ ≤ M) →
        (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
        ‖restrictedNoStopCenteredValue R v ψ w ρ Z (Real.exp hW.radius) ℓ (W i)
          H ((1+Real.log X)^Ct) X X₀ P‖ ≤
          K*(1+Real.log Y)*(1+Real.log X)^Ct*X^(5/6-1/100:ℝ) := by
  obtain ⟨ρ,hρ,hρ₂,hsmall,hgeom⟩ := restricted_noStop_short_support hκ hcap
  obtain ⟨K,hK,hbound⟩ := short_outer_low_bound hV hW ℓ hGamma hM 1 Ct
  refine ⟨ρ,K,hρ,hρ₂,hsmall,hK,?_⟩
  have hcomp : Tendsto (fun X : ℝ => Real.exp hW.radius*X) atTop atTop :=
    tendsto_id.const_mul_atTop (Real.exp_pos _)
  filter_upwards [hcomp.eventually hgeom] with X hgeomX
  intro i R v ψ w Z Y H X₀ P hX hlog hBX hY hdist hYX hH hR hv hψ
  let F := Real.exp hW.radius*X
  let D := primaryElementBall F
  let Bsupport := primaryPairSupport R D
  let α := restrictedNoStopCoefficient R D v ψ w ρ F Z P
  have hP (b : Eisenstein) (hb : b ∈ Bsupport) : primary b :=
    primaryPairSupport_primary R D hR (fun m hm => (mem_primaryElementBall.mp hm).1) hb
  have hs (b : Eisenstein) (_hb : b ∈ Bsupport) (hne : α b ≠ 0) : norm b ≤ Y :=
    (hgeomX R v ψ w Z P b hne).le.trans hdist
  have ha (b : Eisenstein) (hb : b ∈ Bsupport) :
      ‖α b‖ ≤ M*((metaplecticPrimaryDivisors b).card:ℝ)^1 := by
    simpa only [pow_one] using restrictedNoStop_coefficient_divisor_bound R D hR hψ w ρ F Z P v hM hv (hP b hb)
  have hb := hbound (fun _ => i) Bsupport α X Y H X₀ hX hlog hBX hY hYX hH hP hs ha
  have he := restrictedNoStop_coefficient_collection (squarefreeProductEnvelope F) R v ψ w ρ F Z P
    (centeredHeightKernel ℓ (W i) H ((1+Real.log X)^Ct) X X₀)
  change ‖restrictedNoStopCenteredValue R v ψ w ρ Z (Real.exp hW.radius) ℓ (W i)
    H ((1+Real.log X)^Ct) X X₀ P‖ ≤ _
  change ‖∑ r ∈ R, v r*∑ u ∈ D,
    ∑ m ∈ primaryProductSlice (squarefreeProductEnvelope F) F (r*u) with
      norm r*primeSurrogate (primaryPrimeFactors m) (geometricPrimeBin ρ F)
        (geometricBinLower ρ F) < Z ∧ P r m,
      cutoffMoebius ψ w m*centeredHeightKernel ℓ (W i) H ((1+Real.log X)^Ct) X X₀ (r*(m*u))‖ ≤ _
  rw [he]
  exact hb

end CubicFirstMoment

end

end OAI
