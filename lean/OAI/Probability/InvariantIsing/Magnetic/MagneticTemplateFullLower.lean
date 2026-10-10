import OAI.Probability.InvariantIsing.Magnetic.MagneticAffineTemplateLower
import OAI.Probability.InvariantIsing.Core.AffineTemplateComparison
import OAI.Probability.InvariantIsing.Magnetic.MagneticResidueSelection
import OAI.Probability.InvariantIsing.Cavity.CavityResidueFamily

namespace OAI

/-! A rational spectral and magnetic template gives a lower bound along
all physical dimensions, by selecting an arbitrary bad residue for each
candidate block size. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem magnetic_template_full_pressure_lower
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
    (group : Fin n → A) (k : A → ℕ) (hk : ∀ a, k a ≤ spinGroupSize group a)
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hcount : ∀ a, (spinGroupSize group a : ℝ)=n*γ a)
    {s : ℝ} (hs : s < 1) (hmag : ∀ a, |mag a| ≤ s)
    (hc : ∀ a, (k a : ℝ)=spinGroupSize group a*((1+mag a)/2))
    (g : (M : ℕ) → Fin M → A) (b : A → ℝ)
    (hg : Tendsto (fun M a => (spinGroupSize (g M) a : ℝ)/M) atTop (𝓝 γ))
    {D : ℝ} (hD : 0 ≤ D) (hb : ∀ a, |b a| ≤ D)
    (L : ℝ) (hL : L < (magneticVariationalFunctional (finiteR ρ lam hρ hsum) γ mag).toReal) :
    ∀ ε > 0, ∀ᶠ M in atTop, L+(∑ a, γ a*b a*mag a)-ε ≤
      ∫ V, rotatedPressure (fun i => lam (e M i)) (matrixRotation V⁻¹)
        (fun i => b (g M i)) ∂μ M := by
  let B := fun r => (r+1)*n
  let q := fun r => m*B r-B r+B r+3
  let P := fun M => ∫ V, rotatedPressure (fun i => lam (e M i)) (matrixRotation V⁻¹)
    (fun i => b (g M i)) ∂μ M
  apply magnetic_full_lower_of_residue_selection B q
    (fun r => Nat.mul_pos (Nat.succ_pos r) hn) P (L+∑ a, γ a*b a*mag a)
  intro t
  let c := fun r => cavityResidueOffset (by omega : 0 < m) (t r)
  let R := fun r => (Finset.univ : Finset (Spin (∑ a, c r a)))
  have hR r : (R r).Nonempty := Finset.univ_nonempty
  obtain ⟨r,hr⟩ := magnetic_affine_template_pressure_lower hhaar hgauss hpub hm hn
    ρ lam hρ hsum hK hlam amax hmax μ spec hsp hspec hρspec c R hR
    group k hk γ mag hγ hγsum hcount hs hmag hc b L hL
  refine ⟨r,fun ε hε => ?_⟩
  have hspec' : ∑ a, (r+1)*spec a=B r := by rw [← Finset.mul_sum,hspec]
  have hρspec' a : ((r+1)*spec a : ℕ)=(B r : ℝ)*ρ a := by
    dsimp only [B]
    rw [Nat.cast_mul,Nat.cast_mul,hρspec]
    ring
  have hcomp := affine_template_pressure_comparison (by omega : 0 < m)
    (Nat.mul_pos (Nat.succ_pos r) hn) (q r) (by dsimp only [q]; omega)
    (fun a => (r+1)*spec a) (c r) hspec' ρ lam hρ hρspec' μ e he
    g γ b hg (consecutiveSiteGroup (r+1) group)
    (consecutiveSiteGroup_proportion group γ hcount) hK hlam hD hb
  have hevent := (tendsto_order.mp hcomp).1 (-ε/2) (by linarith)
  filter_upwards [hr (ε/2) (by linarith),hevent] with j hj hd
  dsimp only at hj hd
  have hsumc : ∑ a, c r a=(t r : ℕ) := cavityResidueOffset_sum _ _
  rw [hsumc] at hj hd
  change L+(∑ a, γ a*b a*mag a)-ε ≤ P ((t r : ℕ)+(q r+j)*B r)
  dsimp only [P]
  dsimp only [B,q] at *
  linarith

end InvariantIsing

end

end OAI
