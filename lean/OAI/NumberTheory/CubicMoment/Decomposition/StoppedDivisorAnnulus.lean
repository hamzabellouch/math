import OAI.NumberTheory.CubicMoment.Decomposition.StoppedRadialForm
import OAI.NumberTheory.CubicMoment.Estimates.DivisorPoissonRadial

namespace OAI

/-! The literal stopped square-divisor Poisson annulus, with principal
frequencies tested at d*h and the exact inverse-square divisor cost. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_divisor_noncube_poisson_annulus
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
    (hΦ' : ContDiff ℝ ∞ Φ) (k q H : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b u V B Y A : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      2 ≤ b → X^κ ≤ b → b ≤ X →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      1 ≤ B → B ≤ b^(3/5:ℝ) →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      0 < Y → 0 ≤ A → ∀ (d : Eisenstein), d ≠ 0 → ∀ (S : Finset Eisenstein),
      (∀ v ∈ S, d*v ≠ 0 ∧ norm (d*v) ≤ B ∧ ¬∃ n : Eisenstein, n^3 = d*v) →
      (∀ v ∈ S, Y ≤ norm (d*v) ∧ norm (d*v) ≤ 2*Y) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2 < min (X^ξ) (geometricBinLower (1+δ) X h) →
      2*(Real.log X)^(2*(4*(k+2)+k)) ≤
        min (X^ξ) (geometricBinLower (1+δ) X h) →
      (1+A*Y/(27*(norm d)^3*(b/2)^2))^q*
        ‖finiteDivisorPoissonContribution d (stoppedIntervalSupport ι X (b/2) b e) S
          (stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
            (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
              j₀ k₀ h Z Q early)) u Φ A‖ ≤
        K*A*b*B^(1/3:ℝ)/((norm d)^2*(Real.log X)^k) := by
  obtain ⟨K,hK,hr⟩ := stopped_noncube_radial_form (ι := ι) (E := E)
    hpnt hSW hMV hC hHuxley hξ hξz hκ hF hJ Φ hΦ hΦ' k q H
  refine ⟨2*K/9,by positivity,?_⟩
  filter_upwards [hr] with X hr
  intro δ b u V B Y A hδ hδone hwidth hb2 hb hbX hV hu hVF hB hBb
    W hW hWi hWd hY hA d hd S hS hSY e he hNe j₀ k₀ h Z Q early hj hR hRL
  let P := stoppedIntervalSupport ι X (b/2) b e
  let selected := stoppedSideTest (geometricPrimeBin (1+δ) X)
    (geometricBinLower (1+δ) X) j₀ k₀ h Z Q early
  let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W selected
  let S' := S.image (fun v => d*v)
  let phase := divisorFourierPhase d
  let ρ := A*Y/(27*(norm d)^3*(b/2)^2)
  have hdN : 0 < norm d := norm_pos_of_ne_zero hd
  have hbpos : 0 < b := by linarith
  have hN : 0 < b/2 := by positivity
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hS' : ∀ v ∈ S', v ≠ 0 ∧ norm v ≤ B ∧ ¬∃ n : Eisenstein, n^3 = v := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    exact hS w hw
  have hSY' : ∀ v ∈ S', Y ≤ norm v ∧ norm v ≤ 2*Y := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    exact hSY w hw
  have hphase : ∀ v ∈ S', ‖phase v‖ ≤ 1 := by
    intro v _
    exact (norm_divisorFourierPhase d v).le
  have hrad := hr δ b u V B Y hδ hδone hwidth hb2 hb hbX hV hu hVF hB hBb
    W hW hWi hWd hY S' phase hS' hSY' hphase e he hNe j₀ k₀ h Z Q early hj hR hRL ρ hρ
  have heq := finiteDivisorPoissonContribution_radial hd P S
    (fun n hn => (stoppedIntervalSupport_spec X (b/2) b e hn).1)
    β u Φ hA hN hY
  dsimp only [β] at heq
  simp only [←stoppedRowCoefficient_phase] at heq
  rw [heq,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hA (by positivity))]
  have hscalar : A/(9*(norm d)^2*(b/2))*b^2 = (2/9:ℝ)*A*b/(norm d)^2 := by
    field_simp [hbpos.ne',hdN.ne']
  calc
    _ = A/(9*(norm d)^2*(b/2))*((1+ρ)^q*‖normCoprimeRadialForm P S'
        (fun n => star (stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W selected n))
        (fun n => star (stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W selected n))
        phase (fun v => norm v/Y) (fun n => norm n/(b/2)) Φ ρ‖) := by ring
    _ ≤ A/(9*(norm d)^2*(b/2))*(K*b^2*B^(1/3:ℝ)/(Real.log X)^k) :=
      mul_le_mul_of_nonneg_left hrad (by positivity)
    _ = (A/(9*(norm d)^2*(b/2))*b^2)*K*B^(1/3:ℝ)/(Real.log X)^k := by ring
    _ = _ := by rw [hscalar]; ring

end CubicFirstMoment

end

end OAI
