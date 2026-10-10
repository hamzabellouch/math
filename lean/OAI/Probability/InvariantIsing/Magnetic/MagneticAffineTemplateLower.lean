import OAI.Probability.InvariantIsing.Magnetic.MagneticAffineFieldLower
import OAI.Probability.InvariantIsing.Cavity.ConsecutiveGroupProfile

namespace OAI

/-! A single rational spectral/field template supplies the growing
attainable blocks in the physical magnetic pressure lower bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem magnetic_affine_template_pressure_lower
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
    (c : ℕ → Fin m → ℕ)
    (R : (r : ℕ) → Finset (Spin (∑ a, c r a))) (hR : ∀ r, (R r).Nonempty)
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin n → A) (k : A → ℕ) (hk : ∀ a, k a ≤ spinGroupSize group a)
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hcount : ∀ a, (spinGroupSize group a : ℝ)=n*γ a)
    {s : ℝ} (hs : s < 1) (hmag : ∀ a, |mag a| ≤ s)
    (hc : ∀ a, (k a : ℝ)=spinGroupSize group a*((1+mag a)/2))
    (b : A → ℝ) (L : ℝ) (hL : L < (magneticVariationalFunctional (finiteR ρ lam hρ hsum) γ mag).toReal) :
    ∃ r, ∀ ε > 0, ∀ᶠ j in atTop,
      let B := (r+1)*n
      let q := m*B-B+B+3
      let M := (∑ a, c r a)+(q+j)*B
      let g := cavityAffineLabel (by omega : 0 < m) (fun a => (r+1)*spec a) (c r)
        (by rw [← Finset.mul_sum, hspec]) M
      L+(∑ a, γ a*b a*mag a)-ε ≤ ∫ V, rotatedPressure (fun i => lam (g i)) (matrixRotation V⁻¹)
        (offsetBlockField (∑ a, c r a) (q+j) (fun i => b (consecutiveSiteGroup (r+1) group i))) ∂μ M := by
  let N := fun r => (r+1)*n
  have hN r : 0 < N r := Nat.mul_pos (Nat.succ_pos r) hn
  have hNlim : Tendsto N atTop atTop := by
    apply tendsto_atTop_mono (fun r => ?_) tendsto_id
    exact (Nat.le_succ r).trans (Nat.le_mul_of_pos_right (r+1) hn)
  let sp := fun r a => (r+1)*spec a
  have hsp' r a : 0 < sp r a := Nat.mul_pos (Nat.succ_pos r) (hsp a)
  have hspec' r : ∑ a, sp r a=N r := by
    dsimp only [sp, N]
    rw [← Finset.mul_sum, hspec]
  have hρsp r a : (sp r a : ℝ)=(N r : ℝ)*ρ a := by
    dsimp only [sp, N]
    rw [Nat.cast_mul, hρspec, Nat.cast_mul]
    ring
  have hh := magnetic_affine_field_subsequence_lower hhaar hgauss hpub hm ρ lam hρ hsum hK hlam
    amax hmax μ N hN hNlim sp hsp' hspec' hρsp c R hR
    (fun r => consecutiveSiteGroup (r+1) group) (fun r a => (r+1)*k a)
    (fun _ => consecutiveSiteGroup_attainable group k hk) γ mag hγ hγsum
    (fun _ => consecutiveSiteGroup_proportion group γ hcount) hs hmag
    (fun _ => consecutiveSiteGroup_magnetization group k mag hc) b L hL
  exact hh

end InvariantIsing

end

end OAI
