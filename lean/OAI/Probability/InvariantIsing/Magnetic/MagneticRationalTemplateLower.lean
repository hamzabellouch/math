import OAI.Probability.InvariantIsing.Magnetic.MagneticTemplateFullLower
import OAI.Probability.InvariantIsing.Magnetic.RationalMagnetizationCounts

namespace OAI

/-! Every rational interior profile is admissible after a finite common
denominator repetition of a spectral and field template. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem magnetic_rational_template_pressure_lower
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
    (mag : RationalMagnetization A)
    (g : (M : ℕ) → Fin M → A) (b : A → ℝ)
    (hg : Tendsto (fun M a => (spinGroupSize (g M) a : ℝ)/M) atTop (𝓝 γ))
    {D : ℝ} (hD : 0 ≤ D) (hb : ∀ a, |b a| ≤ D)
    (L : ℝ) (hL : L < (magneticVariationalFunctional (finiteR ρ lam hρ hsum) γ
      (fun a => (mag.val a : ℝ))).toReal) :
    ∀ ε > 0, ∀ᶠ M in atTop, L+(∑ a, γ a*b a*(mag.val a : ℝ))-ε ≤
      ∫ V, rotatedPressure (fun i => lam (e M i)) (matrixRotation V⁻¹)
        (fun i => b (g M i)) ∂μ M := by
  obtain ⟨d,hd,k,hk,hkc⟩ := rational_magnetization_counts (spinGroupSize group) mag
  obtain ⟨s,hs,hmags,_⟩ := exists_uniform_magnetization_radius
    (fun _ : ℕ => fun a => (mag.val a : ℝ)) (fun a => (mag.val a : ℝ))
    tendsto_const_nhds mag.property
  have hcount' := consecutiveSiteGroup_proportion (K := d) group γ hcount
  have hspec' : ∑ a, d*spec a=d*n := by rw [← Finset.mul_sum,hspec]
  have hρspec' a : (d*spec a : ℕ)=(d*n : ℕ)*ρ a := by
    rw [Nat.cast_mul,Nat.cast_mul,hρspec]
    ring
  exact magnetic_template_full_pressure_lower hhaar hgauss hpub hm (Nat.mul_pos hd hn)
    ρ lam hρ hsum hK hlam amax hmax μ (fun a => d*spec a)
    (fun a => Nat.mul_pos hd (hsp a)) hspec' hρspec' e he
    (consecutiveSiteGroup d group) k
    (by simpa only [consecutiveSiteGroup_size] using hk) γ (fun a => (mag.val a : ℝ))
    hγ hγsum hcount' hs hmags
    (by simpa only [consecutiveSiteGroup_size,Nat.cast_mul] using hkc)
    g b hg hD hb L hL

end InvariantIsing

end

end OAI
