import OAI.Probability.InvariantIsing.Magnetic.MagneticRationalTemplateLower
import OAI.Probability.InvariantIsing.Magnetic.MagneticVariationalContinuity
import OAI.Probability.InvariantIsing.Magnetic.MagneticVariationalBounds

namespace OAI

/-! The full rational magnetization supremum is a lower bound for physical
pressure whenever the spectral and field populations have a finite template. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem finite_template_magnetic_pressure_lower
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n)
    (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (amax : Fin m) (hmax : ∀ a, lam a ≤ lam amax)
    (μ : (M : ℕ) → Measure (Orthogonal M)) [∀ M, IsProbabilityMeasure (μ M)]
    [∀ M, (μ M).IsMulRightInvariant]
    (spec : Fin m → ℕ) (hsp : ∀ a, 0 < spec a) (hspec : ∑ a, spec a=n)
    (hρspec : ∀ a, (spec a : ℝ)=(n : ℝ)*ρ a)
    (e : (M : ℕ) → Fin M → Fin m)
    (he : Tendsto (fun M a => (spinGroupSize (e M) a : ℝ)/M) atTop (𝓝 ρ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin n → A) (γ : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hcount : ∀ a, (spinGroupSize group a : ℝ)=n*γ a)
    (g : (M : ℕ) → Fin M → A) (b : A → ℝ)
    (hg : Tendsto (fun M a => (spinGroupSize (g M) a : ℝ)/M) atTop (𝓝 γ))
    {D : ℝ} (hD : 0 ≤ D) (hb : ∀ a, |b a| ≤ D)
    : ∀ ε > 0, ∀ᶠ M in atTop,
      (finiteMagneticFunctional (finiteR ρ lam hρ hsum) γ b).toReal-ε ≤
      ∫ V, rotatedPressure (fun i => lam (e M i)) (matrixRotation V⁻¹)
        (fun i => b (g M i)) ∂μ M := by
  intro ε hε
  let R := finiteR ρ lam hρ hsum
  let F := (finiteMagneticFunctional R γ b).toReal
  have hr := finiteVariational_ne_top_bot ρ lam hρ hsum
  have hf := finiteMagneticFunctional_ne_top_bot R γ b hγ hγsum hr.1 hr.2
  have hlt : ((F-ε/3 : ℝ) : EReal)<finiteMagneticFunctional R γ b := by
    rw [← EReal.coe_toReal hf.1 hf.2]
    apply EReal.coe_lt_coe
    change F-ε/3<F
    linarith
  obtain ⟨mag,hmag⟩ := lt_iSup_iff.mp hlt
  have hmfin := finiteMagneticVariational_ne_top_bot ρ lam hρ hsum γ
    (fun a => (mag.val a : ℝ)) hγ hγsum (fun a => (mag.property a).le)
  change ((F-ε/3 : ℝ) : EReal)<
    ((∑ a, γ a*b a*(mag.val a : ℝ) : ℝ) : EReal)+
      magneticVariationalFunctional R γ (fun a => (mag.val a : ℝ)) at hmag
  rw [← EReal.coe_toReal hmfin.1 hmfin.2,← EReal.coe_add] at hmag
  have hmag' := EReal.coe_lt_coe_iff.mp hmag
  let V := (magneticVariationalFunctional R γ (fun a => (mag.val a : ℝ))).toReal
  have hevent := magnetic_rational_template_pressure_lower hhaar hgauss hpub hm hn
    ρ lam hρ hsum hK hlam amax hmax μ spec hsp hspec hρspec e he group γ hγ hγsum
    hcount mag g b hg hD hb (V-ε/3) (by dsimp only [V,R]; linarith) (ε/3) (by positivity)
  filter_upwards [hevent] with M hM
  change F-ε ≤ _
  change V-ε/3+(∑ a, γ a*b a*(mag.val a : ℝ))-ε/3 ≤ _ at hM
  change F-ε/3<(∑ a, γ a*b a*(mag.val a : ℝ))+V at hmag'
  linarith

end InvariantIsing

end

end OAI
