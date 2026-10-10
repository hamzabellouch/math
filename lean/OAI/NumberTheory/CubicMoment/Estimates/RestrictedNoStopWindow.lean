import OAI.NumberTheory.CubicMoment.Estimates.ShortOuterWindow
import OAI.NumberTheory.CubicMoment.Estimates.RestrictedNoStopSupport

namespace OAI

/-! The surviving no-stop part at a dyadic height. Its failed-prefix
predicate remains in the actual coefficient when Type I is applied. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def restrictedNoStopGaussWindowValue (R : Finset Eisenstein) (v : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w ρ Z B : ℝ) (ℓ : ℤ) (W : ℝ → ℂ)
    (H T X X₀ : ℝ) (P : Eisenstein → Eisenstein → Prop) : ℂ :=
  ∑ r ∈ R, v r*∑ u ∈ primaryElementBall (B*X),
    ∑ m ∈ primaryProductSlice (squarefreeProductEnvelope (B*X)) (B*X) (r*u) with
      norm r*primeSurrogate (primaryPrimeFactors m)
        (geometricPrimeBin ρ (B*X)) (geometricBinLower ρ (B*X)) < Z ∧ P r m,
      cutoffMoebius ψ w m*productGaussHeightWindowKernel ℓ W H T X X₀ (r*(m*u))

theorem restricted_noStop_window_bound (hpnt : PrimaryPrimePNT)
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput a)
    {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMean0 : 0 ≤ MV)
    {κ η ν A cap : ℝ} (hκ : 0 < κ) (hη : η ≤ κ/4)
    (hν : 0 < ν) (hA : 0 ≤ A) (hcap : 1 < cap) (M : ℕ) :
    ∃ ρ C E : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ρ ≤ cap ∧ 0 ≤ C ∧ 0 ≤ E ∧
      ∀ᶠ X : ℝ in atTop, ∀ (i : γ) (R : Finset Eisenstein)
        (v : Eisenstein → ℂ) (ψ : ℝ → ℝ) (w Z Y H T X₀ : ℝ)
        (P : Eisenstein → Eisenstein → Prop),
      2 ≤ X → 1 ≤ Real.log X → 1 ≤ Y → Real.log X ≤ T → 0 < H → 0 < X₀ →
      (Real.exp hW.radius*X)^(ν/4)*Z ≤ Y →
      ((2*Y ≤ X^(2/5:ℝ) ∧ T ≤ X^(1/100:ℝ)) ∨
        (2*Y ≤ X^(1/3-κ/2) ∧ T ≤ X^(1/6+η))) →
      (∀ r ∈ R, primary r) → (∀ r ∈ R, ‖v r‖ ≤ A) →
      (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
      ‖restrictedNoStopGaussWindowValue R v ψ w ρ Z (Real.exp hW.radius)
        0 (W i) H T X X₀ P‖ ≤
        (1+Real.log Y)*(C*X^(5/6-min (1/100) (3*κ/16))+
          E*X^(5/6:ℝ)/(Real.log X)^M) := by
  obtain ⟨ρ,hρ,hρ₂,hsmall,hgeom⟩ := restricted_noStop_short_support hν hcap
  obtain ⟨C,E,hC,hE,hbound⟩ := radial_short_outer_window_bound hpnt hW
    hVor hMV hMean0 hκ hη hA 1 M
  refine ⟨ρ,C,E,hρ,hρ₂,hsmall,hC,hE,?_⟩
  have hcomp : Tendsto (fun X : ℝ => Real.exp hW.radius*X) atTop atTop :=
    tendsto_id.const_mul_atTop (Real.exp_pos _)
  filter_upwards [hcomp.eventually hgeom] with X hgeomX
  intro i R v ψ w Z Y H T X₀ P hX hlog hY hLT hH hX₀ hdist hrange hR hv hψ
  let F' := Real.exp hW.radius*X
  let D := primaryElementBall F'
  let Bsupport := primaryPairSupport R D
  let α := restrictedNoStopCoefficient R D v ψ w ρ F' Z P
  have hP (b : Eisenstein) (hb : b ∈ Bsupport) : primary b :=
    primaryPairSupport_primary R D hR (fun m hm => (mem_primaryElementBall.mp hm).1) hb
  have hs (b : Eisenstein) (_hb : b ∈ Bsupport) (hne : α b ≠ 0) : norm b ≤ Y :=
    (hgeomX R v ψ w Z P b hne).le.trans hdist
  have ha (b : Eisenstein) (hb : b ∈ Bsupport) :
      ‖α b‖ ≤ A*((metaplecticPrimaryDivisors b).card:ℝ)^1 := by
    simpa only [pow_one] using restrictedNoStop_coefficient_divisor_bound R D hR
      hψ w ρ F' Z P v hA hv (hP b hb)
  have hb := hbound (fun _ => i) Bsupport α X Y H T X₀ hX hlog hY hLT hH hX₀
    hrange hP hs ha
  change ‖∑ r ∈ R, v r*∑ u ∈ D,
    ∑ m ∈ primaryProductSlice (squarefreeProductEnvelope F') F' (r*u) with
      norm r*primeSurrogate (primaryPrimeFactors m)
        (geometricPrimeBin ρ F') (geometricBinLower ρ F') < Z ∧ P r m,
      cutoffMoebius ψ w m*productGaussHeightWindowKernel 0 (W i) H T X X₀ (r*(m*u))‖ ≤ _
  rw [restrictedNoStop_coefficient_collection]
  exact hb

end CubicFirstMoment

end

end OAI
